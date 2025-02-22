(** Master Control Program *)

open Prelude.Ana
open GobConfig
open Analyses

module QuerySet = Set.Make (Queries.Any)

type spec_modules = { spec : (module MCPSpec)
                    ; dom  : (module Lattice.S)
                    ; glob : (module Lattice.S)
                    ; cont : (module Printable.S) }

let analyses_list  : (int * spec_modules) list ref = ref []
let analyses_list' : (int * spec_modules) list ref = ref []
let dep_list       : (int * (int list)) list ref   = ref []
let dep_list'      : (int * (string list)) list ref= ref []

let analyses_table = ref []

let register_analysis =
  let count = ref 0 in
  fun ?(dep=[]) (module S:MCPSpec) ->
    let s = { spec = (module S : MCPSpec)
            ; dom  = (module S.D : Lattice.S)
            ; glob = (module S.G : Lattice.S)
            ; cont = (module S.C : Printable.S)
            }
    in
    let n = S.name () in
    analyses_table := (!count,n) :: !analyses_table;
    analyses_list' := (!count,s) :: !analyses_list';
    dep_list'      := (!count,dep) :: !dep_list';
    count := !count + 1


type unknown = Obj.t

module type DomainListPrintableSpec =
sig
  val assoc_dom : int -> (module Printable.S)
  val domain_list : unit -> (int * (module Printable.S)) list
end

module type DomainListLatticeSpec =
sig
  val assoc_dom : int -> (module Lattice.S)
  val domain_list : unit -> (int * (module Lattice.S)) list
end

module PrintableOfLatticeSpec (D:DomainListLatticeSpec) : DomainListPrintableSpec =
struct
  let assoc_dom n =
    let f (module L:Lattice.S) = (module L : Printable.S)
    in
    f (D.assoc_dom n)

  let domain_list () =
    let f (module L:Lattice.S) = (module L : Printable.S) in
    List.map (fun (x,y) -> (x,f y)) (D.domain_list ())
end

exception DomListBroken of string

module DomListPrintable (DLSpec : DomainListPrintableSpec)
  (*  : Printable.S with type t = (string * unknown) list *)
=
struct
  include Printable.Std (* for default invariant, tag, ... *)

  open DLSpec
  open List
  open Obj

  type t = (int * unknown) list

  let unop_fold f a (x:t) =
    let f a n d =
      f a n (assoc_dom n) d
    in
    fold_left (fun a (n,d) -> f a n d) a x

  let pretty () x =
    let f a n (module S : Printable.S) x = Pretty.dprintf "%s:%a" (S.name ()) S.pretty (obj x) :: a in
    let xs = unop_fold f [] x in
    match xs with
    | [] -> text "[]"
    | x :: [] -> x
    | x :: y ->
      let rest  = List.fold_left (fun p n->p ++ text "," ++ break ++ n) nil y in
      text "[" ++ align ++ x ++ rest ++ unalign ++ text "]"

  let show x =
    let xs = unop_fold (fun a n (module S : Printable.S) x ->
        let analysis_name = assoc n !analyses_table in
        (analysis_name ^ ":(" ^ S.show (obj x) ^ ")") :: a) [] x
    in
    IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " String.print) (rev xs)

  let to_yojson xs =
    let f a n (module S : Printable.S) x =
      let name = BatList.assoc n !analyses_table in
      (name, S.to_yojson (obj x)) :: a
    in `Assoc (unop_fold f [] xs)

  let binop_fold f a (x:t) (y:t) =
    let f a n d1 d2 =
      f a n (assoc_dom n) d1 d2
    in
    try if length x <> length y
      then raise (DomListBroken "binop_fold : differing lengths")
      else fold_left (fun a (n,d) -> f a n d @@ assoc n y) a x
    with Not_found -> raise (DomListBroken "binop_fold : assoc failure")

  let binop_map_rev (f: (module Printable.S) -> Obj.t -> Obj.t -> Obj.t) =
    binop_fold (fun a n s d1 d2 -> (n, f s d1 d2) :: a) []

  let equal   x y = binop_fold (fun a n (module S : Printable.S) x y -> a && S.equal (obj x) (obj y)) true x y
  let compare x y = binop_fold (fun a n (module S : Printable.S) x y -> if a <> 0 then a else S.compare (obj x) (obj y)) 0 x y

  let hashmul x y = if x=0 then y else if y=0 then x else x*y

  let hash     = unop_fold (fun a n (module S : Printable.S) x -> hashmul a @@ S.hash (obj x)) 0

  let name () =
    let domain_name (n, (module D: Printable.S)) =
      let analysis_name = assoc n !analyses_table in
      analysis_name ^ ":(" ^ D.name () ^ ")"
    in
    IO.to_string (List.print ~first:"[" ~last:"]" ~sep:", " String.print) (map domain_name @@ domain_list ())

  let printXml f xs =
    let print_one a n (module S : Printable.S) x : unit =
      BatPrintf.fprintf f "<analysis name=\"%s\">\n" (List.assoc n !analyses_table);
      S.printXml f (obj x);
      BatPrintf.fprintf f "</analysis>\n"
    in
    unop_fold print_one () xs

  let invariant c = unop_fold (fun a n (module S : Printable.S) x ->
      Invariant.(a && S.invariant c (obj x))
    ) Invariant.none

  let arbitrary () =
    let arbs = map (fun (n, (module D: Printable.S)) -> QCheck.map ~rev:(fun (_, o) -> obj o) (fun x -> (n, repr x)) @@ D.arbitrary ()) @@ domain_list () in
    MyCheck.Arbitrary.sequence arbs
end

let _ =
  let module Test : functor (DLSpec : DomainListPrintableSpec) -> Printable.S with type t = (int * unknown) list = DomListPrintable  in
  ()

module DomListLattice (DLSpec : DomainListLatticeSpec)
  : Lattice.S with type t = (int * unknown) list
=
struct
  open DLSpec
  open List
  open Obj

  include DomListPrintable (PrintableOfLatticeSpec (DLSpec))

  let binop_fold f a (x:t) (y:t) =
    let f a n d1 d2 =
      f a n (assoc_dom n) d1 d2
    in
    try if length x <> length y
      then raise (DomListBroken "binop_fold : differing lengths")
      else fold_left (fun a (n,d) -> f a n d @@ assoc n y) a x
    with Not_found -> raise (DomListBroken "binop_fold : assoc failure")

  let binop_map (f: (module Lattice.S) -> Obj.t -> Obj.t -> Obj.t) x y =
    List.rev @@ binop_fold (fun a n s d1 d2 -> (n, f s d1 d2) :: a) [] x y

  let unop_fold f a (x:t) =
    let f a n d =
      f a n (assoc_dom n) d
    in
    fold_left (fun a (n,d) -> f a n d) a x

  let narrow = binop_map (fun (module S : Lattice.S) x y -> repr @@ S.narrow (obj x) (obj y))
  let widen  = binop_map (fun (module S : Lattice.S) x y -> repr @@ S.widen  (obj x) (obj y))
  let meet   = binop_map (fun (module S : Lattice.S) x y -> repr @@ S.meet   (obj x) (obj y))
  let join   = binop_map (fun (module S : Lattice.S) x y -> repr @@ S.join   (obj x) (obj y))

  let leq    = binop_fold (fun a n (module S : Lattice.S) x y -> a && S.leq (obj x) (obj y)) true

  let is_top = unop_fold (fun a n (module S : Lattice.S) x -> a && S.is_top (obj x)) true
  let is_bot = unop_fold (fun a n (module S : Lattice.S) x -> a && S.is_bot (obj x)) true

  let top () = map (fun (n,(module S : Lattice.S)) -> (n,repr @@ S.top ())) @@ domain_list ()
  let bot () = map (fun (n,(module S : Lattice.S)) -> (n,repr @@ S.bot ())) @@ domain_list ()

  let pretty_diff () (x,y) =
    let f a n (module S : Lattice.S) x y =
      if S.leq (obj x) (obj y) then a
      else a ++ S.pretty_diff () (obj x, obj y) ++ text ". "
    in
    binop_fold f nil x y
end

module LocalDomainListSpec : DomainListLatticeSpec =
struct
  let assoc_dom n = (List.assoc n !analyses_list).dom
  let domain_list () = List.map (fun (n,p) -> n, p.dom) !analyses_list
end

module GlobalDomainListSpec : DomainListLatticeSpec =
struct
  let assoc_dom n = (List.assoc n !analyses_list).glob
  let domain_list () = List.map (fun (n,p) -> n, p.glob) !analyses_list
end

module ContextListSpec : DomainListPrintableSpec =
struct
  let assoc_dom n = (List.assoc n !analyses_list).cont
  let domain_list () = List.map (fun (n,p) -> n, p.cont) !analyses_list
end

module MCP2 : Analyses.Spec
  with module D = DomListLattice (LocalDomainListSpec)
   and module G = DomListLattice (GlobalDomainListSpec)
   and module C = DomListPrintable (ContextListSpec) =
struct
  module D = DomListLattice (LocalDomainListSpec)
  module G = DomListLattice (GlobalDomainListSpec)
  module C = DomListPrintable (ContextListSpec)

  open List open Obj

  let name () = "MCP2"

  let path_sens = ref []
  let cont_inse = ref []
  let base_id   = ref (-1)


  let topo_sort deps circ_msg =
    let rec f res stack = function
      | []                     -> res
      | x::xs when mem x stack -> circ_msg x
      | x::xs when mem x res   -> f res stack xs
      | x::xs                  -> f (x :: f res (x::stack) (deps x)) stack xs
    in rev % f [] []

  let topo_sort_an xs =
    let msg (x,_) = failwith ("Analyses have circular dependencies, conflict for "^assoc x !analyses_table^".") in
    let deps (y,_) = map (fun x -> x, assoc x xs) @@ assoc y !dep_list in
    topo_sort deps msg xs

  let check_deps xs =
    let check_dep x y =
      if not (exists (fun (y',_) -> y=y') xs) then begin
        let xn = assoc x !analyses_table in
        let yn = assoc y !analyses_table in
        Legacy.Printf.eprintf "Activated analysis '%s' depends on '%s' and '%s' is not activated.\n" xn yn yn;
        raise Exit
      end
    in
    let deps (x,_) = iter (check_dep x) @@ assoc x !dep_list in
    iter deps xs


  type marshal = Obj.t list
  let init marshal =
    let map' f =
      let f x =
        try f x
        with Not_found -> raise @@ ConfigError ("Analysis '"^x^"' not found. Abort!")
      in
      List.map f
    in
    let xs = get_string_list "ana.activated" in
    let xs = map' (flip assoc_inv !analyses_table) xs in
    base_id := assoc_inv "base" !analyses_table;
    analyses_list := map (fun s -> s, assoc s !analyses_list') xs;
    path_sens := map' (flip assoc_inv !analyses_table) @@ get_string_list "ana.path_sens";
    cont_inse := map' (flip assoc_inv !analyses_table) @@ get_string_list "ana.ctx_insens";
    dep_list  := map (fun (n,d) -> (n,map' (flip assoc_inv !analyses_table) d)) !dep_list';
    check_deps !analyses_list;
    analyses_list := topo_sort_an !analyses_list;
    (*iter (fun (x,y) -> Printf.printf "%s -> %a\n"  (flip assoc !analyses_table x) (List.print (fun f -> String.print f % flip assoc !analyses_table)) y) !dep_list_trans;
      Printf.printf "\n";
      iter (Printf.printf "%s\n" % flip assoc !analyses_table % fst) !analyses_list;
      Printf.printf "\n";*)
    match marshal with
    | Some marshal ->
      combine !analyses_list marshal
      |> iter (fun ((_,{spec=(module S:MCPSpec); _}), marshal) -> S.init (Some (Obj.obj marshal)))
    | None ->
      iter (fun (_,{spec=(module S:MCPSpec); _}) -> S.init None) !analyses_list

  let finalize () = map (fun (_,{spec=(module S:MCPSpec); _}) -> Obj.repr (S.finalize ())) !analyses_list

  let spec x = (assoc x !analyses_list).spec
  let spec_list xs =
    map (fun (n,x) -> (n,spec n,x)) xs
  let spec_name (n:int) : string = assoc n !analyses_table

  let map_deadcode f xs =
    let dead = ref false in
    let one_el xs (n,(module S:MCPSpec),d) = try f xs (n,(module S:MCPSpec),d) :: xs with Deadcode -> dead:=true; (n,repr @@ S.D.bot ()) :: xs in
    let ys = fold_left one_el [] xs in
    List.rev ys, !dead

  let context fd x =
    let x = spec_list x in
    map (fun (n,(module S:MCPSpec),d) ->
        let d' = if mem n !cont_inse then S.D.top () else obj d in
        n, repr @@ S.context fd d'
      ) x

  let should_join x y =
    let rec zip3 lst1 lst2 lst3 = match lst1,lst2,lst3 with
      | [],_, _ -> []
      | _,[], _ -> []
      | _,_ , []-> []
      | (x::xs),(y::ys), (z::zs) -> (x,y,z)::(zip3 xs ys zs)
    in
    let should_join ((_,(module S:Analyses.MCPSpec),_),(_,x),(_,y)) = S.should_join (obj x) (obj y) in
    (* obtain all analyses specs that are path sensitive and their values both in x and y *)
    let specs = filter (fun (x,_,_) -> mem x !path_sens) (spec_list x) in
    let xs = filter (fun (x,_) -> mem x !path_sens) x in
    let ys = filter (fun (x,_) -> mem x !path_sens) y in
    let zipped = zip3 specs xs ys in
    List.for_all should_join zipped

  let exitstate  v = map (fun (n,{spec=(module S:MCPSpec); _}) -> n, repr @@ S.exitstate  v) !analyses_list
  let startstate v = map (fun (n,{spec=(module S:MCPSpec); _}) -> n, repr @@ S.startstate v) !analyses_list
  let morphstate v x = map (fun (n,(module S:MCPSpec),d) -> n, repr @@ S.morphstate v (obj d)) (spec_list x)

  let call_descr f xs =
    let xs = filter (fun (x,_) -> x = !base_id) xs in
    fold_left (fun a (n,(module S:MCPSpec),d) -> S.call_descr f (obj d)) f.svar.vname @@ spec_list xs


  let rec assoc_replace (n,c) = function
    | [] -> failwith "assoc_replace"
    | (n',c')::xs -> if n=n' then (n,c)::xs else (n',c') :: assoc_replace (n,c) xs

  (** [assoc_split_eq (=) 1 [(1,a);(1,b);(2,x)] = ([a,b],[(2,x)])] *)
  let assoc_split_eq eq (k:'a) (xs:('a * 'b) list) : ('b list) * (('a * 'b) list) =
    let rec f a b = function
      | [] -> a, b
      | (k',v)::xs when eq k k' -> f (v::a) b xs
      | x::xs -> f a (x::b) xs
    in
    f [] [] xs

  let assoc_split k xs = assoc_split_eq (=) k xs


  (** [group_assoc_eq (=) [(1,a);(1,b);(2,x);(2,y)] = [(1,[a,b]),(2,[x,y])]] *)
  let group_assoc_eq eq (xs: ('a * 'b) list) : ('a * ('b list)) list  =
    let rec f a = function
      | [] -> a
      | (k,v)::xs ->
        let a', b = assoc_split_eq eq k xs in
        f ((k,v::a')::a) b
    in f [] xs

  (** [group_assoc [(1,a);(1,b);(2,x);(2,y)] = [(1,[a,b]),(2,[x,y])]] *)
  let group_assoc xs = group_assoc_eq (=) xs

  let filter_presubs n xs =
    let f n =
      let x = try assoc n !analyses_table with Not_found -> Printf.eprintf "filter_presubs: Analysis '%d' not registered.\n" n; failwith "filter_presubs" in
      let y = try assoc n xs with Not_found ->
        (*iter (Printf.printf "%s\n" % flip assoc !analyses_table % fst) xs;*)
        Printf.eprintf "filter_presubs: Analysis '%s' (%d) not found.\n" x n; failwith "filter_presubs" in
      x, y
    in
    map f (assoc n !dep_list)

  let do_spawns ctx (xs:(varinfo * (int * lval option * exp list)) list) =
    let spawn_one v d =
      List.iter (fun (n, lval, args) -> ctx.spawn lval v args) d
    in
    if not (get_bool "exp.single-threaded") then
      iter (uncurry spawn_one) @@ group_assoc_eq Basetype.Variables.equal xs

  let do_sideg ctx (xs:(varinfo * (int * Obj.t)) list) =
    let side_one v d =
      let join_vals (n,(module S:MCPSpec),d) =
        n, repr @@ fold_left (fun x y -> S.G.join x (obj y)) (S.G.bot ()) d
      in
      ctx.sideg v @@ topo_sort_an @@ map join_vals @@ spec_list @@ group_assoc (d @ G.bot ())
    in
    iter (uncurry side_one) @@ group_assoc_eq Basetype.Variables.equal xs

  let do_assigns ctx assigns (xs:(int * Obj.t) list) =
    if List.is_empty assigns then xs (* nothing to do *)
    else
      let spec_assign n d : Obj.t =
        (* spec of current analysis *)
        let (module S:MCPSpec) = spec n in
        let assign_one d (lval, exp, name, ctx) =
          match name with
          | Some x when x <> spec_name n -> obj d (* do nothing if current spec name is filtered out *)
          | _ ->
            let ctx' = {(obj ctx) with local = obj d} in
            S.assign ctx' lval exp
        in
        let get_lval (lval, exp, name, ctx) = lval in
        (* group by assigns on the same lval -> only those must be joined *)
        List.group (compareBy get_lval) assigns
        |> List.fold_left (fun d xs -> List.map (assign_one d) xs |> List.reduce S.D.join |> repr) d
      in
      List.map (fun (n,d) -> n, spec_assign n d) xs

  let finalize () =
    let r = finalize () in
    Access.print_result ();
    r

  let rec do_splits ctx pv (xs:(int * (Obj.t * Events.t list)) list) =
    let split_one n (d,emits) =
      let nv = assoc_replace (n,d) pv in
      ctx.split (do_emits ctx emits nv) []
    in
    iter (uncurry split_one) xs

  and do_emits ctx emits xs =
    let octx = ctx in
    let ctx_with_local ctx local' =
      (* let rec ctx' =
        { ctx with
          local = local';
          ask = ask
        }
      and ask q = query ctx' q
      in
      ctx' *)
      {ctx with local = local'}
    in
    let do_emit ctx = function
      | Events.SplitBranch (exp, tv) ->
        ctx_with_local ctx (branch ctx exp tv)
      | e ->
        let spawns = ref [] in
        let splits = ref [] in
        let sides  = ref [] in (* why do we need to collect these instead of calling ctx.sideg directly? *)
        let assigns = ref [] in
        let emits = ref [] in
        let f post_all (n,(module S:MCPSpec),d) =
          let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
            { local  = obj d
            ; node   = ctx.node
            ; prev_node = ctx.prev_node
            ; control_context = ctx.control_context
            ; context = (fun () -> ctx.context () |> assoc n |> obj)
            ; edge   = ctx.edge
            ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
            ; emit   = (fun e -> emits := e :: !emits)
            ; presub = filter_presubs n ctx.local
            ; postsub= filter_presubs n post_all
            ; global = (fun v      -> ctx.global v |> assoc n |> obj)
            ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
            ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
            ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
            ; assign = (fun ?name v e    -> assigns := (v,e,name, repr ctx')::!assigns)
            }
          in
          let rec octx' : (S.D.t, S.G.t, S.C.t) ctx =
            { local  = obj (assoc n octx.local)
            ; node   = octx.node
            ; prev_node = octx.prev_node
            ; control_context = octx.control_context
            ; context = (fun () -> octx.context () |> assoc n |> obj)
            ; edge   = octx.edge
            ; ask    = (fun (type a) (q: a Queries.t) -> query octx q)
            ; emit   = (fun e -> emits := e :: !emits)
            ; presub = filter_presubs n octx.local
            ; postsub= filter_presubs n post_all
            ; global = (fun v      -> octx.global v |> assoc n |> obj)
            ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
            ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
            ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
            ; assign = (fun ?name v e    -> assigns := (v,e,name, repr octx')::!assigns)
            }
          in
          n, repr @@ S.event ctx' e octx'
        in
        let d, q = map_deadcode f @@ spec_list ctx.local in
        if M.tracing then M.tracel "event" "%a\n  before: %a\n  after:%a\n" Events.pretty e D.pretty ctx.local D.pretty d;
        do_sideg ctx !sides;
        do_spawns ctx !spawns;
        do_splits ctx d !splits;
        let d = do_assigns ctx !assigns d in
        let d = do_emits ctx !emits d in
        if q then raise Deadcode else ctx_with_local ctx d
    in
    let ctx' = List.fold_left do_emit (ctx_with_local ctx xs) emits in
    ctx'.local

  and branch (ctx:(D.t, G.t, C.t) ctx) (e:exp) (tv:bool) =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in (* why do we need to collect these instead of calling ctx.sideg directly? *)
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e    -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.branch ctx' e tv
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  (* Explicitly polymorphic type required here for recursive GADT call in ask. *)
  and query': type a. QuerySet.t -> (D.t, G.t, C.t) ctx -> a Queries.t -> a Queries.result = fun asked ctx q ->
    let module Result = (val Queries.Result.lattice q) in
    if QuerySet.mem (Any q) asked then
      Result.top () (* query cycle *)
    else
      let asked' = QuerySet.add (Any q) asked in
      let sides = ref [] in
      let f a (n,(module S:MCPSpec),d) =
        let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
          { local  = obj d
          ; node   = ctx.node
          ; prev_node = ctx.prev_node
          ; control_context = ctx.control_context
          ; context = (fun () -> ctx.context () |> assoc n |> obj)
          ; edge   = ctx.edge
          ; ask    = (fun (type b) (q: b Queries.t) -> query' asked' ctx q)
          ; emit   = (fun _ -> failwith "Cannot \"emit\" in query context.")
          ; presub = filter_presubs n ctx.local
          ; postsub= []
          ; global = (fun v      -> ctx.global v |> assoc n |> obj)
          ; spawn  = (fun v d    -> failwith "Cannot \"spawn\" in query context.")
          ; split  = (fun d es   -> failwith "Cannot \"split\" in query context.")
          ; sideg  = (fun v g    -> sides := (v, (n, repr g)) :: !sides)
          (* sideg is discouraged in query, because they would bypass sides grouping in other transfer functions.
             See https://github.com/goblint/analyzer/pull/214. *)
          ; assign = (fun ?name _ -> failwith "Cannot \"assign\" in query context.")
          }
        in
        (* meet results so that precision from all analyses is combined *)
        Result.meet a @@ S.query ctx' q
      in
      match q with
      | Queries.PrintFullState ->
        ignore (Pretty.printf "Current State:\n%a\n\n" D.pretty ctx.local);
        ()
      (* | EvalInt e ->
        (* TODO: only query others that actually respond to EvalInt *)
        (* 2x speed difference on SV-COMP nla-digbench-scaling/ps6-ll_valuebound5.c *)
        f (Result.top ()) (!base_id, spec !base_id, assoc !base_id ctx.local) *)
      | _ ->
        let r = fold_left f (Result.top ()) @@ spec_list ctx.local in
        do_sideg ctx !sides;
        r

  and query: type a. (D.t, G.t, C.t) ctx -> a Queries.t -> a Queries.result = fun ctx q ->
    query' QuerySet.empty ctx q

  let assign (ctx:(D.t, G.t, C.t) ctx) l e =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name _ -> failwith "Cannot \"assign\" in assign context (cycles?).")
        }
      in
      n, repr @@ S.assign ctx' l e
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d


  let vdecl (ctx:(D.t, G.t, C.t) ctx) v =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name _ -> failwith "Cannot \"assign\" in assign context (cycles?).")
        }
      in
      n, repr @@ S.vdecl ctx' v
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let body (ctx:(D.t, G.t, C.t) ctx) f =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.body ctx' f
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let return (ctx:(D.t, G.t, C.t) ctx) e f =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.return ctx' e f
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let intrpt (ctx:(D.t, G.t, C.t) ctx) =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.intrpt ctx'
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let asm (ctx:(D.t, G.t, C.t) ctx) =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.asm ctx'
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let skip (ctx:(D.t, G.t, C.t) ctx) =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.skip ctx'
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let special (ctx:(D.t, G.t, C.t) ctx) r f a =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.special ctx' r f a
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let sync (ctx:(D.t, G.t, C.t) ctx) reason =
    let spawns = ref [] in
    let splits = ref [] in
    let sides  = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> splits := (n,(repr d,es)) :: !splits)
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name _ -> failwith "Cannot \"assign\" in sync context.")
        }
      in
      n, repr @@ S.sync ctx' reason
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    do_splits ctx d !splits;
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let enter (ctx:(D.t, G.t, C.t) ctx) r f a =
    let spawns = ref [] in
    let sides  = ref [] in
    let f (n,(module S:MCPSpec),d) =
      let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun _ -> failwith "Cannot \"emit\" in enter context.")
        ; presub = filter_presubs n ctx.local
        ; postsub= []
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun _ _    -> failwith "Cannot \"split\" in enter context." )
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name _ -> failwith "Cannot \"assign\" in enter context.")
        }
      in
      map (fun (c,d) -> ((n, repr c), (n, repr d))) @@ S.enter ctx' r f a
    in
    let css = map f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    map (fun xs -> (topo_sort_an @@ map fst xs, topo_sort_an @@ map snd xs)) @@ n_cartesian_product css

  let combine (ctx:(D.t, G.t, C.t) ctx) r fe f a fc fd =
    let spawns = ref [] in
    let sides  = ref [] in
    let assigns = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let rec ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun l v a  -> spawns := (v,(n,l,a)) :: !spawns)
        ; split  = (fun d es   -> failwith "Cannot \"split\" in combine context.")
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> assigns := (v,e,name, repr ctx')::!assigns)
        }
      in
      n, repr @@ S.combine ctx' r fe f a (obj (assoc n fc)) (obj (assoc n fd))
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    do_spawns ctx !spawns;
    let d = do_assigns ctx !assigns d in
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d

  let threadenter (ctx:(D.t, G.t, C.t) ctx) lval f a =
    let sides  = ref [] in
    let emits = ref [] in
    let f (n,(module S:MCPSpec),d) =
      let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= []
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun v d    -> failwith "Cannot \"spawn\" in threadenter context.")
        ; split  = (fun d es   -> failwith "Cannot \"split\" in threadenter context.")
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> failwith "Cannot \"assign\" in threadenter context.")
        }
      in
      map (fun d -> (n, repr d)) @@ S.threadenter ctx' lval f a
    in
    let css = map f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    (* TODO: this do_emits is now different from everything else *)
    map (do_emits ctx !emits) @@ map topo_sort_an @@ n_cartesian_product css

  let threadspawn (ctx:(D.t, G.t, C.t) ctx) lval f a fctx =
    let sides  = ref [] in
    let emits = ref [] in
    let f post_all (n,(module S:MCPSpec),d) =
      let ctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj d
        ; node   = ctx.node
        ; prev_node = ctx.prev_node
        ; control_context = ctx.control_context
        ; context = (fun () -> ctx.context () |> assoc n |> obj)
        ; edge   = ctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query ctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n ctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> ctx.global v |> assoc n |> obj)
        ; spawn  = (fun v d    -> failwith "Cannot \"spawn\" in threadspawn context.")
        ; split  = (fun d es   -> failwith "Cannot \"split\" in threadspawn context.")
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> failwith "Cannot \"assign\" in threadspawn context.")
        }
      in
      let fctx' : (S.D.t, S.G.t, S.C.t) ctx =
        { local  = obj (assoc n fctx.local)
        ; node   = fctx.node
        ; prev_node = fctx.prev_node
        ; control_context = fctx.control_context
        ; context = (fun () -> fctx.context () |> assoc n |> obj)
        ; edge   = fctx.edge
        ; ask    = (fun (type a) (q: a Queries.t) -> query fctx q)
        ; emit   = (fun e -> emits := e :: !emits)
        ; presub = filter_presubs n fctx.local
        ; postsub= filter_presubs n post_all
        ; global = (fun v      -> fctx.global v |> assoc n |> obj)
        ; spawn  = (fun v d    -> failwith "Cannot \"spawn\" in threadspawn context.")
        ; split  = (fun d es   -> failwith "Cannot \"split\" in threadspawn context.")
        ; sideg  = (fun v g    -> sides  := (v, (n, repr g)) :: !sides)
        ; assign = (fun ?name v e -> failwith "Cannot \"assign\" in threadspawn context.")
        }
      in
      n, repr @@ S.threadspawn ctx' lval f a fctx'
    in
    let d, q = map_deadcode f @@ spec_list ctx.local in
    do_sideg ctx !sides;
    let d = do_emits ctx !emits d in
    if q then raise Deadcode else d
end
