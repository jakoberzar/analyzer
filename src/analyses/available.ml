(** An analysis specification for didactic purposes. *)

open Prelude.Ana
open Analyses



module Spec : Analyses.Spec =
struct
  include Analyses.DefaultSpec

  let name () = "available"

  (* Domain type *)

  module ExpSet = SetDomain.BottedSet (Basetype.CilExp) (struct let botname = "Various" end)
  (* module ExpSet = SetDomain.BottedSet (ExpDomain) (struct let botname = "Various" end) *)


  module D = ExpSet
  module G = Lattice.Unit
  module C = ExpSet
  (* module C = Lattice.Unit *)

  (* let val_of () = D.bot ()
     let context _ = () *)

  (* Check if the expression is interesting enough to store it *)
  let interesting_expr (exp:exp) : bool =
    match exp with
    | Const constant -> false
    | Lval lval -> false
    | _ -> true

  (* Check if given expressions contains the given lvalue*)
  let rec contains_lval (exp:exp) (lval:lval) : bool =
    match exp with
    | Lval lval_p
    | AddrOf lval_p
    | StartOf lval_p -> lval_p = lval
    | Real exp
    | Imag exp
    | SizeOfE exp
    | AlignOfE exp
    | UnOp (_, exp, _)
    | CastE (_, exp) -> contains_lval exp lval
    | BinOp (_, exp1, exp2, _) -> contains_lval exp1 lval || contains_lval exp2 lval
    | Question (exp1, exp2, exp3, _) -> (
        contains_lval exp1 lval || contains_lval exp2 lval || contains_lval exp3 lval
      )
    | _ -> false

  (* Remove any expressions that contain the given lvalue *)
  let remove_containing_exprs (exprs:D.t) (lval:lval) : D.t =
    (* ! can't figure out which exprs are available -
       or meant by all? However, is All really even
       reachable? *)
    D.filter (fun exp -> not (contains_lval exp lval)) exprs

  (* Get the lvalues that had their address taken in a given expression *)
  let rec lvals_taken_address (exp:exp) : lval list =
    match exp with
    | AddrOf lval_p -> [lval_p]
    | Real exp
    | Imag exp
    | SizeOfE exp
    | AlignOfE exp
    | UnOp (_, exp, _)
    | CastE (_, exp) -> lvals_taken_address exp
    | BinOp (_, exp1, exp2, _) -> List.append (lvals_taken_address exp1) (lvals_taken_address exp2)
    | Question (exp1, exp2, exp3, _) ->
      List.append (
        List.append (lvals_taken_address exp1) (lvals_taken_address exp2)
      ) (lvals_taken_address exp3)
    | _ -> []

  (* Remove all expressions that had their address taken in the given expression *)
  let addr_lvals_removed (exprs: D.t) (exp:exp) : D.t =
    let addr_lvals = lvals_taken_address exp
    in List.fold remove_containing_exprs exprs addr_lvals

  (* Add a new expression to the current set of expressions *)
  let add_new_expr (locals: D.t) (exp:exp) : D.t =
    (* Remove any lvals whose address was taken *)
    (* Add the expression only if it is interesting *)
    let exprs = addr_lvals_removed locals exp
    in
    if interesting_expr exp
    then D.union exprs (D.singleton exp)
    else exprs


  (* Remove some expressions from the set depending on the func. arguments and optional assignment *)
  let process_func_call (locals: D.t) (lval: lval option) (args: exp list): D.t =
    (* Remove expressions whose addresses were taken address of *)
    let new_set = List.fold addr_lvals_removed locals args
    in
    (* Remove lval (assignment) *)
    match lval with
    | Some lval -> remove_containing_exprs new_set lval
    | None -> new_set

  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    let new_set = add_new_expr ctx.local rval
    in remove_containing_exprs new_set lval

  let branch ctx (exp:exp) (tv:bool) : D.t =
    add_new_expr ctx.local exp

  let body ctx (f:fundec) : D.t =
    (* Nothing is available in a new function *)
    (* ctx.local or, D.top () *)
    D.top ()

  let return ctx (exp:exp option) (f:fundec) : D.t =
    match exp with
    | Some exp -> add_new_expr ctx.local exp
    | None -> ctx.local

  let enter ctx (lval: lval option) (f:varinfo) (args:exp list) : (D.t * D.t) list =
    (* What exactly should be put here and what in the body function? *)
    [ctx.local, D.top ()]

  let combine ctx (lval:lval option) fexp (f:varinfo) (args:exp list) fc (au:D.t) : D.t =
    process_func_call ctx.local lval args

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    process_func_call ctx.local lval arglist

  let startstate v = D.top ()
  let threadenter ctx lval f args = D.top ()
  let threadspawn ctx lval f args fctx = D.bot ()
  let exitstate  v = D.top ()
end

let _ =
  MCP.register_analysis (module Spec : Spec)
