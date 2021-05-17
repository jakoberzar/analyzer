open Cil

module type S =
sig
  include Lattice.S
  type value
  type field
  val get: t -> field -> value
  val replace: t -> field -> value -> t
  val refine: t -> field -> value -> t
  val fold: (field -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all_common_bindings: (value -> value -> bool) -> t -> t -> bool
  val map: (value -> value) -> t -> t
  val cardinal: t -> int
  val keys: t -> field list
  val widen_with_fct: (value -> value -> value) -> t -> t -> t
  val join_with_fct: (value -> value -> value) -> t -> t -> t
  val leq_with_fct: (value -> value -> bool) -> t -> t -> bool
end

module Simple (Val: Lattice.S) =
struct
  include Printable.Std
  module M = MapDomain.MapTop (Basetype.CilField) (Val)
  let name () = "simple structs"
  type t = M.t [@@deriving to_yojson]
  type field = fieldinfo
  type value = M.value

  (** Short summary for structs *)
  let short w mapping =
    let usable_length = w - 5 in
    let assoclist = M.fold (fun x y rest -> (x,y)::rest) mapping [] in
    let f (key, st) = Val.short usable_length st in
    let whole_str_list = List.rev_map f assoclist in
    Printable.get_short_list "<" ">" usable_length whole_str_list

  let for_all_common_bindings (pred: (value -> value -> bool)) (x:t) (y:t) =
    let pred_ok key value =
      try
        let other = M.find key y in
        pred value other
      with Not_found -> true
    in
    M.for_all pred_ok x

  let pretty_f sf = M.pretty_f sf
  let pretty () x = M.pretty_f short () x
  let replace s field value = M.add field value s
  let refine = replace
  let get s field = M.find field s
  let fold = M.fold
  let map = M.map
  let cardinal x = M.fold (fun _ _ -> succ) x 0
  let keys x = M.fold (fun k _ a -> k::a) x []

  (* Add these or the byte code will segfault ... *)
  let equal x y = M.equal x y
  let compare x y = M.compare x y
  let is_top x = M.is_top x
  let top () = M.top ()
  let is_bot x = M.is_bot x
  let bot () = M.bot ()
  let meet x y = M.meet x y
  let join x y = M.join x y
  let leq x y = M.leq x y
  let isSimple x = M.isSimple x
  let hash x = M.hash x
  let widen = M.widen
  let narrow = M.narrow
  let pretty_diff () (x,y) =
    Pretty.dprintf "{@[%a@] ...}" M.pretty_diff (x,y)
  let printXml f xs = M.printXml f xs
  let widen_with_fct = M.widen_with_fct
  let leq_with_fct = M.leq_with_fct
  let join_with_fct = M.join_with_fct

  let invariant c x =
    match c.Invariant.offset with
    (* invariants for all fields *)
    | NoOffset ->
      let c_lval = BatOption.get c.Invariant.lval in
      fold (fun f v acc ->
          let f_lval = Cil.addOffsetLval (Field (f, NoOffset)) c_lval in
          let f_c = {c with lval=Some f_lval} in
          let i = Val.invariant f_c v in
          Invariant.(acc && i)
        ) x Invariant.none
    (* invariant for one field *)
    | Field (f, offset) ->
      let f_c = {c with offset} in
      let v = get x f in
      Val.invariant f_c v
    (* invariant for one index *)
    | Index (i, offset) ->
      Invariant.none
end

module SimpleSets (Val: Lattice.S) =
struct
  include Printable.Std
  module M = MapDomain.MapTop (Basetype.CilField) (Val)
  module SS = Simple (Val)
  module SD = SetDomain.ToppedSet (SS) (struct let topname = "All Possible Component Values" end)
  let name () = "simple set structs"
  type t = SD.t [@@deriving to_yojson]
  type field = fieldinfo
  type value = SS.value

  (** Short summary for structs *)
  (* from int->tmap->string to int->t->string *)
  let short w mapping = SD.short w mapping

  let for_all_common_bindings (pred: (value -> value -> bool)) (x:t) (y:t) =
    SD.for_all (fun sy -> SD.for_all (fun s -> SS.for_all_common_bindings pred s sy) x) y


  let pretty_f sf = SD.pretty_f sf
  let pretty () x = SD.pretty_f short () x
  (* let replace s field value =
    SD.map (fun s -> SS.replace s field value) s *)
  let replace s field value =
    let result = SD.map (fun s -> SS.replace s field value) s in
    if Messages.tracing then Messages.tracel "bot-fail" "Replace - s is: %a\nfield is: %a\nvalue is: %a\nresult is: %a\n-------\n" SD.pretty s Basetype.CilField.pretty field Val.pretty value SD.pretty result;
    result

  let replaceIfLower s field value =
    let result = SD.map (fun s -> if Val.leq value (SS.get s field) then SS.replace s field value else s) s in
    result

  let refine s field value =
    let instanceComparable ss =
      let current = SS.get ss field in
      Val.leq value current || Val.leq current value in
    let filtered = SD.filter instanceComparable s in
    let result = replaceIfLower filtered field value in
    if Messages.tracing then Messages.tracel "bot-fail" "Refine - s is: %a\nfield is: %a\nvalue is: %a\nfiltered is: %a\nresult is: %a\n-------\n" SD.pretty s Basetype.CilField.pretty field Val.pretty value SD.pretty filtered SD.pretty result;
    result

  let get s field =
    if SD.is_empty s
    then Val.top ()
    else SD.fold (fun ss acc -> Val.join acc (SS.get ss field)) s (Val.bot ())


  let joinSS s =
    let elements = SD.elements s in
    match elements with
      | [] -> SS.top ()
      | [x] -> x
      | h::t -> List.fold_left (fun el acc -> SS.join el acc) h t

  let on_joint_ss f s = f (joinSS s)

  let fold f = on_joint_ss (SS.fold f)

  let map f s = SD.singleton (on_joint_ss (SS.map f) s)

  let cardinal = on_joint_ss (SS.cardinal)
  let keys = on_joint_ss (SS.keys)

  (* Add these or the byte code will segfault ... *)
  let equal x y = SD.equal x y
  let compare x y = SD.compare x y
  let is_top x = SD.for_all (SS.is_top) x
  let top () = SD.singleton (SS.top ())
  let is_bot x = SD.for_all (SS.is_bot) x
  let bot () = SD.singleton (SS.bot ())
  let join x y =
    let setJoined = SD.join x y in
    let limit = 10 in
    let result =
      if SD.cardinal setJoined < limit
      then setJoined
      else SD.singleton (joinSS setJoined)
    in
    result
  let leq x y =
    let left = joinSS x in
    let right = joinSS y in
    SS.leq left right
  let isSimple x = SD.isSimple x
  let hash x = SD.hash x
  let widen = SD.widen
  let narrow = SD.narrow
  (* let narrow x y = let result = SD.narrow x y in ignore (Pretty.printf "Narrowing - x is: %a\ny is: %a\nResult is: %a\n-------\n" SD.pretty x SD.pretty y SD.pretty result); result *)
  let pretty_diff () (x,y) =
    Pretty.dprintf "{@[%a@] ...}" SD.pretty_diff (x,y)
  let printXml f xs = SD.printXml f xs
  let widen_with_fct _ = widen
  let leq_with_fct _ = leq
  let join_with_fct _ = join

  let invariant c x = SD.invariant c x
  (* match c.Invariant.offset with
      (* invariants for all fields *)
      | NoOffset -> Invariant.none
      (* let c_lval = BatOption.get c.Invariant.lval in
      fold (fun f v acc ->
          let f_lval = Cil.addOffsetLval (Field (f, NoOffset)) c_lval in
          let f_c = {c with lval=Some f_lval} in
          let i = Val.invariant f_c v in
          Invariant.(acc && i)
        ) x Invariant.none *)
      (* invariant for one field *)
      | Field (f, offset) ->
        let f_c = {c with offset} in
        let v = get x f in
        Val.invariant f_c v
      (* invariant for one index *)
      | Index (i, offset) ->
        Invariant.none *)
end
