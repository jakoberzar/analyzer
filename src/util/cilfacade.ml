(** Helpful functions for dealing with [Cil]. *)

open GobConfig
open Cil
module E = Errormsg
module GU = Goblintutil


let get_labelLoc = function
  | Label (_, loc, _) -> loc
  | Case (_, loc) -> loc
  | CaseRange (_, _, loc) -> loc
  | Default loc -> loc

let rec get_labelsLoc = function
  | [] -> Cil.locUnknown
  | label :: labels ->
    let loc = get_labelLoc label in
    if CilType.Location.equal loc Cil.locUnknown then
      get_labelsLoc labels (* maybe another label has known location *)
    else
      loc

let get_stmtkindLoc = Cil.get_stmtLoc (* CIL has a confusing name for this function *)

let get_stmtLoc stmt =
  match stmt.skind with
  (* Cil.get_stmtLoc returns Cil.locUnknown in these cases, so try labels instead *)
  | Instr []
  | Block {bstmts = []; _} ->
    get_labelsLoc stmt.labels
  | _ -> get_stmtkindLoc stmt.skind


let init () =
  initCIL ();
  lowerConstants := GobConfig.get_bool "exp.lower-constants";
  Mergecil.ignore_merge_conflicts := true;
  (* lineDirectiveStyle := None; *)
  Rmtmps.keepUnused := true;
  print_CIL_Input := true

let current_statement = ref dummyStmt
let current_file = ref dummyFile
let showtemps = ref false

let parse fileName =
  Frontc.parse fileName ()

let print_to_file (fileName: string) (fileAST: file) =
  let oc = Stdlib.open_out fileName in
  dumpFile defaultCilPrinter oc fileName fileAST

let print (fileAST: file) =
  dumpFile defaultCilPrinter stdout "stdout" fileAST

let printDebug fileAST =
  dumpFile Printer.debugCilPrinter stdout "stdout" fileAST

let rmTemps fileAST =
  Rmtmps.removeUnusedTemps fileAST

class allBBVisitor = object (* puts every instruction into its own basic block *)
  inherit nopCilVisitor
  method! vstmt s =
    match s.skind with
    | Instr(il) ->
      let list_of_stmts =
        List.map (fun one_inst -> mkStmtOneInstr one_inst) il in
      let block = mkBlock list_of_stmts in
      ChangeDoChildrenPost(s, (fun _ -> s.skind <- Block(block); s))
    | _ -> DoChildren

  method! vvdec _ = SkipChildren
  method! vexpr _ = SkipChildren
  method! vlval _ = SkipChildren
  method! vtype _ = SkipChildren
end

let end_basic_blocks f =
  let thisVisitor = new allBBVisitor in
  visitCilFileSameGlobals thisVisitor f

let visitors = ref []
let register_preprocess name visitor_fun =
  visitors := !visitors @ [name, visitor_fun]

let do_preprocess ast =
  let f fd (name, visitor_fun) =
    (* this has to be done here, since the settings aren't available when register_preprocess is called *)
    if List.mem name (get_string_list "ana.activated") then
      ignore @@ visitCilFunction (visitor_fun fd) fd
  in
  iterGlobals ast (function GFun (fd,_) -> List.iter (f fd) !visitors | _ -> ())

let createCFG (fileAST: file) =
  (* The analyzer keeps values only for blocks. So if you want a value for every program point, each instruction      *)
  (* needs to be in its own block. end_basic_blocks does that.                                                        *)
  (* After adding support for VLAs, there are new VarDecl instructions at the point where a variable was declared and *)
  (* its declaration is no longer printed at the beginning of the function. Putting these VarDecl into their own      *)
  (* BB causes the output CIL file to no longer compile.                                                              *)
  (* Since we want the output of justcil to compile, we do not run allBB visitor if justcil is enable, regardless of  *)
  (* exp.basic-blocks. This does not matter, as we will not run any analysis anyway, when justcil is enabled.         *)
  if not (get_bool "exp.basic-blocks") && not (get_bool "justcil") then end_basic_blocks fileAST;

  (* We used to renumber vids but CIL already generates them fresh, so no need.
   * Renumbering is problematic for using [Cabs2cil.environment], e.g. in witness invariant generation to use original variable names.
   * See https://github.com/goblint/cil/issues/31#issuecomment-824939793. *)

  iterGlobals fileAST (fun glob ->
      match glob with
      | GFun(fd,_) ->
        prepareCFG fd;
        computeCFGInfo fd true
      | _ -> ()
    );
  do_preprocess fileAST

let getAST fileName =
  let fileAST = parse fileName in
  (*  rmTemps fileAST; *)
  fileAST

(* a visitor that puts calls to constructors at the starting points to main *)
class addConstructors cons = object
  inherit nopCilVisitor
  val mutable cons1 = cons
  method! vfunc fd =
    if List.mem fd.svar.vname (get_string_list "mainfun") then begin
      if get_bool "dbg.verbose" then ignore (Pretty.printf "Adding constructors to: %s\n" fd.svar.vname);
      let loc = match fd.sbody.bstmts with
        | s :: _ -> get_stmtLoc s
        | [] -> locUnknown
      in
      let f fd = mkStmt (Instr [Call (None,Lval (Var fd.svar, NoOffset),[],loc)]) in
      let call_cons = List.map f cons1 in
      let body = mkBlock (call_cons @ fd.sbody.bstmts) in
      fd.sbody <- body;
      ChangeTo fd
    end else SkipChildren

  method! vstmt _ = SkipChildren
  method! vvdec _ = SkipChildren
  method! vexpr _ = SkipChildren
  method! vlval _ = SkipChildren
  method! vtype _ = SkipChildren
end

let getMergedAST fileASTs =
  let merged = Mergecil.merge fileASTs "stdout" in
  if !E.hadErrors then
    E.s (E.error "There were errors during merging\n");
  merged

(* call constructors at start of main functions *)
let callConstructors ast =
  let constructors =
    let cons = ref [] in
    iterGlobals ast (fun glob ->
        match glob with
        | GFun({svar={vattr=attr; _}; _} as def, _) when hasAttribute "constructor" attr ->
          cons := def::!cons
        | _ -> ()
      );
    !cons
  in
  let d_fundec () fd = Pretty.text fd.svar.vname in
  if get_bool "dbg.verbose" then ignore (Pretty.printf "Constructors: %a\n" (Pretty.d_list ", " d_fundec) constructors);
  visitCilFileSameGlobals (new addConstructors constructors) ast;
  ast

let in_section check attr_list =
  let f attr = match attr with
    | Attr ("section", [AStr str]) -> check str
    | _ -> false
  in List.exists f attr_list

let is_init = in_section (fun s -> s = ".init.text")
let is_initptr = in_section (fun s -> s = ".initcall6.init")
let is_exit = in_section (fun s -> s = ".exit.text")

let rec get_varinfo exp: varinfo =
  (* ignore (Pretty.printf "expression: %a\n" (printExp plainCilPrinter) exp); *)
  match exp with
  | AddrOf (Var v, _) -> v
  | CastE (_,e) -> get_varinfo e
  | _ -> failwith "Unimplemented: searching for variable in more complicated expression"

exception MyException of varinfo
let find_module_init funs fileAST =
  try iterGlobals fileAST (
      function
      | GVar ({vattr=attr; _}, {init=Some (SingleInit exp) }, _) when is_initptr attr ->
        raise (MyException (get_varinfo exp))
      | _ -> ()
    );
    (funs, [])
  with MyException var ->
    let f (s:fundec) = s.svar.vname = var.vname in
    List.partition f funs

type startfuns = fundec list * fundec list * fundec list

let getFuns fileAST : startfuns =
  let add_main f (m,e,o) = (f::m,e,o) in
  let add_exit f (m,e,o) = (m,f::e,o) in
  let add_other f (m,e,o) = (m,e,f::o) in
  let f acc glob =
    match glob with
    | GFun({svar={vname=mn; _}; _} as def,_) when List.mem mn (get_string_list "mainfun") -> add_main def acc
    | GFun({svar={vname=mn; _}; _} as def,_) when mn="StartupHook" && !OilUtil.startuphook -> add_main def acc
    | GFun({svar={vname=mn; _}; _} as def,_) when List.mem mn (get_string_list "exitfun") -> add_exit def acc
    | GFun({svar={vname=mn; _}; _} as def,_) when List.mem mn (get_string_list "otherfun") -> add_other def acc
    | GFun({svar={vname=mn; vattr=attr; _}; _} as def, _) when get_bool "kernel" && is_init attr ->
      Printf.printf "Start function: %s\n" mn; set_string "mainfun[+]" mn; add_main def acc
    | GFun({svar={vname=mn; vattr=attr; _}; _} as def, _) when get_bool "kernel" && is_exit attr ->
      Printf.printf "Cleanup function: %s\n" mn; set_string "exitfun[+]" mn; add_exit def acc
    | GFun ({svar={vstorage=NoStorage; _}; _} as def, _) when (get_bool "nonstatic") -> add_other def acc
    | GFun (def, _) when ((get_bool "allfuns")) ->  add_other def  acc
    | GFun (def, _) when get_string "ana.osek.oil" <> "" && OilUtil.is_starting def.svar.vname -> add_other def acc
    | _ -> acc
  in
  foldGlobals fileAST f ([],[],[])


let getFirstStmt fd = List.hd fd.sbody.bstmts

let pstmt stmt = dumpStmt defaultCilPrinter stdout 0 stmt; print_newline ()

let p_expr exp = Pretty.printf "%a\n" (printExp defaultCilPrinter) exp
let d_expr exp = Pretty.printf "%a\n" (printExp plainCilPrinter) exp

(* Returns the ikind of a TInt(_) and TEnum(_). Unrolls typedefs. Warns if a a different type is put in and return IInt *)
let rec get_ikind t =
  (* important to unroll the type here, otherwise problems with typedefs *)
  match Cil.unrollType t with
  | TInt (ik,_)
  | TEnum ({ekind = ik; _},_) -> ik
  | TPtr _ -> get_ikind !Cil.upointType
  | _ ->
    Messages.warn "Something that we expected to be an integer type has a different type, assuming it is an IInt";
    Cil.IInt

let ptrdiff_ikind () = get_ikind !ptrdiffType


(** Cil.typeOf, etc reimplemented to raise sensible exceptions
    instead of printing all errors directly... *)

type typeOfError =
  | RealImag_NonNumerical (** unexpected non-numerical type for argument to __real__/__imag__ *)
  | StartOf_NonArray (** typeOf: StartOf on a non-array *)
  | Mem_NonPointer of exp (** typeOfLval: Mem on a non-pointer (exp) *)
  | Index_NonArray (** typeOffset: Index on a non-array *)
  | Field_NonCompound (** typeOffset: Field on a non-compound *)

exception TypeOfError of typeOfError

let () = Printexc.register_printer (function
    | TypeOfError error ->
      let msg = match error with
        | RealImag_NonNumerical -> "unexpected non-numerical type for argument to __real__/__imag__"
        | StartOf_NonArray -> "typeOf: StartOf on a non-array"
        | Mem_NonPointer exp -> Printf.sprintf "typeOfLval: Mem on a non-pointer (%s)" (CilType.Exp.show exp)
        | Index_NonArray -> "typeOffset: Index on a non-array"
        | Field_NonCompound -> "typeOffset: Field on a non-compound"
      in
      Some (Printf.sprintf "Cilfacade.TypeOfError(%s)" msg)
    | _ -> None (* for other exceptions *)
  )

(* Cil doesn't expose this *)
let stringLiteralType = ref charPtrType

let typeOfRealAndImagComponents t =
  match unrollType t with
  | TInt _ -> t
  | TFloat (fkind, attrs) ->
    let newfkind = function
      | FFloat -> FFloat      (* [float] *)
      | FDouble -> FDouble     (* [double] *)
      | FLongDouble -> FLongDouble (* [long double] *)
      | FComplexFloat -> FFloat
      | FComplexDouble -> FDouble
      | FComplexLongDouble -> FLongDouble
    in
    TFloat (newfkind fkind, attrs)
  | _ -> raise (TypeOfError RealImag_NonNumerical)

let rec typeOf (e: exp) : typ =
  match e with
  | Const(CInt64 (_, ik, _)) -> TInt(ik, [])

  (* Character constants have type int.  ISO/IEC 9899:1999 (E),
   * section 6.4.4.4 [Character constants], paragraph 10, if you
   * don't believe me. *)
  | Const(CChr _) -> intType

  (* The type of a string is a pointer to characters ! The only case when
   * you would want it to be an array is as an argument to sizeof, but we
   * have SizeOfStr for that *)
  | Const(CStr s) -> !stringLiteralType

  | Const(CWStr s) -> TPtr(!wcharType,[])

  | Const(CReal (_, fk, _)) -> TFloat(fk, [])

  | Const(CEnum(tag, _, ei)) -> typeOf tag
  | Real e -> typeOfRealAndImagComponents @@ typeOf e
  | Imag e -> typeOfRealAndImagComponents @@ typeOf e
  | Lval(lv) -> typeOfLval lv
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> !typeOfSizeOf
  | AlignOf _ | AlignOfE _ -> !typeOfSizeOf
  | UnOp (_, _, t)
  | BinOp (_, _, _, t)
  | Question (_, _, _, t)
  | CastE (t, _) -> t
  | AddrOf (lv) -> TPtr(typeOfLval lv, [])
  | AddrOfLabel (lv) -> voidPtrType
  | StartOf (lv) -> begin
      match unrollType (typeOfLval lv) with
        TArray (t,_, a) -> TPtr(t, a)
      | _ -> raise (TypeOfError StartOf_NonArray)
    end

and typeOfInit (i: init) : typ =
  match i with
    SingleInit e -> typeOf e
  | CompoundInit (t, _) -> t

and typeOfLval = function
    Var vi, off -> typeOffset vi.vtype off
  | Mem addr, off -> begin
      match unrollType (typeOf addr) with
        TPtr (t, _) -> typeOffset t off
      | _ -> raise (TypeOfError (Mem_NonPointer addr))
    end

and typeOffset basetyp =
  let blendAttributes baseAttrs =
    let (_, _, contageous) =
      partitionAttributes ~default:(AttrName false) baseAttrs in
    typeAddAttributes contageous
  in
  function
    NoOffset -> basetyp
  | Index (_, o) -> begin
      match unrollType basetyp with
        TArray (t, _, baseAttrs) ->
        let elementType = typeOffset t o in
        blendAttributes baseAttrs elementType
      | t -> raise (TypeOfError Index_NonArray)
    end
  | Field (fi, o) ->
    match unrollType basetyp with
      TComp (_, baseAttrs) ->
      let fieldType = typeOffset fi.ftype o in
      blendAttributes baseAttrs fieldType
    | _ -> raise (TypeOfError Field_NonCompound)


let get_ikind_exp e = get_ikind (typeOf e)


(** HashSet of line numbers *)
let locs = Hashtbl.create 200

(** Visitor to count locs appearing inside a fundec. *)
class countFnVisitor = object
    inherit nopCilVisitor
    method! vstmt s =
      match s.skind with
      | Return (_, loc)
      | Goto (_, loc)
      | ComputedGoto (_, loc)
      | Break loc
      | Continue loc
      | If (_,_,_,loc)
      | Switch (_,_,_,loc)
      | Loop (_,loc,_,_)
      | TryFinally (_,_,loc)
      | TryExcept (_,_,_,loc)
        -> Hashtbl.replace locs loc.line (); DoChildren
      | _ ->
        DoChildren

    method! vinst = function
      | Set (_,_,loc)
      | Call (_,_,_,loc)
      | Asm (_,_,_,_,_,loc)
        -> Hashtbl.replace locs loc.line (); SkipChildren
      | _ -> SkipChildren

    method! vvdec _ = SkipChildren
    method! vexpr _ = SkipChildren
    method! vlval _ = SkipChildren
    method! vtype _ = SkipChildren
end

let fnvis = new countFnVisitor

(** Count the number of unique locations appearing in fundec [fn].
    Uses {!Cilfacade.locs} hashtable for intermediate computations
*)
let countLoc fn =
  let _ = visitCilFunction fnvis fn in
  let res = Hashtbl.length locs in
  Hashtbl.clear locs;
  res


let fundec_return_type f =
  match f.svar.vtype with
  | TFun (return_type, _, _, _) -> return_type
  | _ -> failwith "fundec_return_type: not TFun"


module StmtH = Hashtbl.Make (CilType.Stmt)

let stmt_fundecs: fundec StmtH.t Lazy.t =
  lazy (
    let h = StmtH.create 113 in
    iterGlobals !current_file (function
        | GFun (fd, _) ->
          List.iter (fun stmt ->
              StmtH.replace h stmt fd
            ) fd.sallstmts
        | _ -> ()
      );
    h
  )

(** Find [fundec] which the [stmt] is in. *)
let find_stmt_fundec stmt = StmtH.find (Lazy.force stmt_fundecs) stmt (* stmt argument must be explicit, otherwise force happens immediately *)


module VarinfoH = Hashtbl.Make (CilType.Varinfo)

let varinfo_fundecs: fundec VarinfoH.t Lazy.t =
  lazy (
    let h = VarinfoH.create 111 in
    iterGlobals !current_file (function
        | GFun (fd, _) ->
          VarinfoH.replace h fd.svar fd
        | _ -> ()
      );
    h
  )

(** Find [fundec] by the function's [varinfo] (has the function name and type). *)
let find_varinfo_fundec vi = VarinfoH.find (Lazy.force varinfo_fundecs) vi (* vi argument must be explicit, otherwise force happens immediately *)


module StringH = Hashtbl.Make (Printable.Strings)

let name_fundecs: fundec StringH.t Lazy.t =
  lazy (
    let h = StringH.create 111 in
    iterGlobals !current_file (function
        | GFun (fd, _) ->
          StringH.replace h fd.svar.vname fd
        | _ -> ()
      );
    h
  )

(** Find [fundec] by the function's name. *)
let find_name_fundec name = StringH.find (Lazy.force name_fundecs) name (* name argument must be explicit, otherwise force happens immediately *)


type varinfo_role =
  | Formal of fundec
  | Local of fundec
  | Function
  | Global

let varinfo_roles: varinfo_role VarinfoH.t Lazy.t =
  lazy (
    let h = VarinfoH.create 113 in
    iterGlobals !current_file (function
        | GFun (fd, _) ->
          VarinfoH.replace h fd.svar Function; (* function itself can be used as a variable (function pointer) *)
          List.iter (fun vi -> VarinfoH.replace h vi (Formal fd)) fd.sformals;
          List.iter (fun vi -> VarinfoH.replace h vi (Local fd)) fd.slocals
        | GVar (vi, _, _)
        | GVarDecl (vi, _) ->
          VarinfoH.replace h vi Global
        | _ -> ()
      );
    h
  )

(** Find the role of the [varinfo]. *)
let find_varinfo_role vi = VarinfoH.find (Lazy.force varinfo_roles) vi (* vi argument must be explicit, otherwise force happens immediately *)

let is_varinfo_formal vi =
  match find_varinfo_role vi with
  | Formal _ -> true
  | exception Not_found
  | _ -> false


(** Find the scope of the [varinfo].
    If [varinfo] is a local or a formal argument of [fundec], then returns [Some fundec].
    If [varinfo] is a global or a function itself, then returns [None]. *)
let find_scope_fundec vi =
  match find_varinfo_role vi with
  | Formal fd
  | Local fd ->
    Some fd
  | Function
  | Global
  | exception Not_found ->
    None


let original_names: string VarinfoH.t Lazy.t =
  (* only invert environment map when necessary (e.g. witnesses) *)
  lazy (
    let h = VarinfoH.create 113 in
    Hashtbl.iter (fun original_name (envdata, _) ->
        match envdata with
        | Cabs2cil.EnvVar vi when vi.vname <> "" -> (* TODO: fix temporary variables with empty names being in here *)
          VarinfoH.replace h vi original_name
        | _ -> ()
      ) Cabs2cil.environment;
    h
  )

(** Find the original name (in input source code) of the [varinfo].
    If it was renamed by CIL, then returns the original name before renaming.
    If it wasn't renamed by CIL, then returns the same name.
    If it was inserted by CIL (or Goblint), then returns [None]. *)
let find_original_name vi = VarinfoH.find_opt (Lazy.force original_names) vi (* vi argument must be explicit, otherwise force happens immediately *)


let stmt_pretty_short () x =
  match x.skind with
  | Instr (y::ys) -> dn_instr () y
  | If (exp,_,_,_) -> dn_exp () exp
  | _ -> dn_stmt () x
