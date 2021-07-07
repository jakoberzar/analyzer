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

module type LatticeWithBotValue =
sig
  include Lattice.S
  val is_bot_value: t -> bool
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

module SimpleSets (Val: LatticeWithBotValue) =
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

  let replace s field value =
    SD.map (fun s -> SS.replace s field value) s

  let get_value_meet ss field value =
    let current = SS.get ss field in
    Val.meet value current

  let replace_with_meet s field value =
    SD.map (fun ss -> SS.replace ss field (get_value_meet ss field value)) s

  (* Get a set of all variants that include this field value  *)
  let including_variants s field value =
    let variant_comparable ss =
      let value_meet = get_value_meet ss field value in
      not (Val.is_bot_value value_meet)
    in
    SD.filter variant_comparable s

  let refine s field value =
    let including_set = including_variants s field value in
    replace_with_meet including_set field value

  let get s field =
    if SD.is_empty s
    then Val.top ()
    else SD.fold (fun ss acc -> Val.join acc (SS.get ss field)) s (Val.bot ())

  let join_ss s =
    let elements = SD.elements s in
    match elements with
      | [] -> SS.top ()
      | [x] -> x
      | h::t -> List.fold_left (fun el acc -> SS.join el acc) h t

  let on_joint_ss f s = f (join_ss s)

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
  let meet x y = SD.meet x y
  let join = SD.join
  let leq = SD.leq

  let isSimple x = SD.isSimple x
  let hash x = SD.hash x
  let widen = SD.widen
  let narrow = SD.narrow

  let pretty_diff () (x,y) =
    Pretty.dprintf "{@[%a@] ...}" SD.pretty_diff (x,y)
  let printXml f xs = SD.printXml f xs

  (* Ignore the function which should widen/leq/join by the struct components, as that
     would break the set domain ordering or destroy the precision.
     The consequence of this is that partitioned arrays aren't working with simple set structs. *)
  let widen_with_fct _ = widen
  let leq_with_fct _ = leq
  let join_with_fct _ = join

  let invariant c x = SD.invariant c x
end

module BetterSets (Val: LatticeWithBotValue) =
struct
  include Printable.Std
  module M = MapDomain.MapTop (Basetype.CilField) (Val)
  module SS = Simple (Val)
  module SD = SetDomain.ToppedSet (SS) (struct let topname = "All Possible Component Values" end)
  let name () = "better set structs"
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

  let join_ss s =
    let elements = SD.elements s in
    match elements with
      | [] -> SS.top ()
      | [x] -> x
      | h::t -> List.fold_left (fun el acc -> SS.join el acc) h t

  let on_joint_ss f s = f (join_ss s)

  let joint_variants s = SD.singleton (join_ss s)

  let cardinal = on_joint_ss (SS.cardinal)
  let keys = on_joint_ss (SS.keys)

  let find_key_field s =
    let existing_keys = keys s in
    if List.length existing_keys == 0
    then None
    else
      let first_existing_key = List.hd existing_keys in
      let struct_fields = first_existing_key.fcomp.cfields in
      let first_key = List.hd struct_fields in
      Some first_key

  let replace s field value =
    let result_replace = SD.map (fun s -> SS.replace s field value) s in
    let result_key =
      match find_key_field s with
        | None -> result_replace
        | Some key ->
          if Basetype.CilField.equal key field
          then joint_variants result_replace (* Key is now the same in all variants *)
          else result_replace
    in
    if Messages.tracing then Messages.tracel "bot-bug" "Replace with s:\n%a\nfield:\n%a\nvalue:\n%a\nresult:\n%a\n---------\n" SD.pretty s Basetype.CilField.pretty field Val.pretty value SD.pretty result_key;
    result_key

  let get_value_meet ss field value =
    let current = SS.get ss field in
    Val.meet value current

  (* Check if a given ss variant is comparable with given value in given field *)
  let variant_comparable field value ss =
    let value_meet = get_value_meet ss field value in
    not (Val.is_bot_value value_meet)

  (* Get a set of all variants that include this field value  *)
  let including_variants s field value =
    SD.filter (variant_comparable field value) s

  let replace_with_meet s field value =
    let result_replace = SD.map (fun ss -> SS.replace ss field (get_value_meet ss field value)) s in
    (* Normalization not needed;
    - variants in s are only those that have key values > or < than the new value
    - if they are >, there is only one variant that overlaps it -> we only narrow it down
    - if they are <, the new value is not lower -> it won't be replaced anyways
    - if they are boundaries; values are [1,2], [3,4] while the new value is [2,3]
      - should be replaced with meet -> [2,2], [3,3] -> still stay disjunctive *)
    result_replace

  let refine s field value =
    let including_set = including_variants s field value in
    let result = replace_with_meet including_set field value in
    if Messages.tracing then Messages.tracel "bot-bug" "Refine with s:\n%a\nfield:\n%a\nvalue:\n%a\nresult:\n%a\n---------\n" SD.pretty s Basetype.CilField.pretty field Val.pretty value SD.pretty result;
    result

  (* Check if a variant is above / below from this one in a given field *)
  let variant_above_below ss field value =
    let current = SS.get ss field in
    Val.leq current value || Val.leq value current

  (* Get a set of all variants that are above / below this one  *)
  let variants_above_below s field value =
    SD.filter (fun ss -> variant_above_below ss field value) s

  let get s field =
    if SD.is_empty s
    then Val.top ()
    else SD.fold (fun ss acc -> Val.join acc (SS.get ss field)) s (Val.bot ())

  let fold f = on_joint_ss (SS.fold f)

  let map f s = SD.singleton (on_joint_ss (SS.map f) s)

  (* Add these or the byte code will segfault ... *)
  let equal x y = SD.equal x y
  let compare x y = SD.compare x y
  let is_top x = SD.for_all (SS.is_top) x
  let top () = SD.singleton (SS.top ())
  let is_bot x = SD.for_all (SS.is_bot) x
  let bot () = SD.singleton (SS.bot ())

  let leq_common ss_wise_f x y =
    match find_key_field x with
    | None -> true
    | Some key ->
    let leq_variant ss y =
      let value = SS.get ss key in
      (* Find all comparable variants in y *)
      let yss = including_variants y key value in
      let joint_yss = join_ss yss in
      if SD.is_empty yss
      then false (* No comparable variants in y, this is only in x -> greater than y *)
      else ss_wise_f ss joint_yss
    in
    SD.for_all (fun ss -> leq_variant ss y) x

  let meet_narrow_common ss_wise_f x y =
    match find_key_field x with
    | None -> y
    | Some key ->
    let comparable_variants ss y =
      let value = SS.get ss key in
      including_variants y key value
    in
    let meet_variant ss y =
      let variants = comparable_variants ss y in
      if SD.is_empty variants
      then None (* No comparable variants in y, this is only in x -> not in meet *)
      else Some (SD.fold (fun ss acc -> ss_wise_f acc ss) variants ss)
    in
    let met_variants = SD.filter (fun ss -> not (SD.is_empty (comparable_variants ss y))) x in
    if SD.cardinal met_variants = 0 (* No common variants between the elements! *)
    then
      (
        if Messages.tracing then Messages.tracel "bot-bug" "Bot with x:\n%a\ny:\n%a\n---------\n" SD.pretty x SD.pretty y;
        bot ()
        (* let result = bot () in
        ignore (Pretty.printf "Bot with x:\n%a\ny:\n%a\nresult:\n%a\n---------\n" SD.pretty x SD.pretty y SD.pretty result);
        result *)
      )

    else SD.fold (fun ss acc ->
      match meet_variant ss y with
        | None -> acc (* This variant (with this key) is only in x, not in meet *)
        | Some result -> SD.add result acc
    ) met_variants (SD.empty ())

  let join_widen_common ss_wise_f x y =
    match find_key_field x with
    | None -> y
    | Some key ->
    let overlapping_key_variants ss y =
      let value = SS.get ss key in
      including_variants y key value
    in
    let overlapping_variants_join ss overlapping_y =
      if SD.is_empty overlapping_y
      then ss (* No comparable variants in y, this is only in x -> itself in join *)
      else SD.fold (fun ss acc -> ss_wise_f acc ss) overlapping_y ss
    in
    let join_variant ss y =
      let overlapping_y = overlapping_key_variants ss y in
      overlapping_variants_join ss overlapping_y
    in
    let variant_not_covered x ss =
      SD.is_empty (overlapping_key_variants ss x) (* No variant in x covers this key from y *)
    in
    let join_x_y x y =
      (* Join variants that overlap between x and y *)
      let x_with_overlapped_y = SD.fold (fun ss acc -> SD.add (join_variant ss y) acc) x (SD.empty ()) in
      (* Add variants not covered! *)
      let x_with_y = SD.fold (fun ss acc -> if variant_not_covered x ss then SD.add ss acc else acc) y x_with_overlapped_y in
      let join_comparable_key_variants x =
        let rec f unique remaining =
          if SD.is_empty remaining
          then unique
          else
            let head = List.hd (SD.elements remaining) in
            let tail = SD.remove head remaining in
            let overlapping_tail = overlapping_key_variants head tail in
            let new_head = overlapping_variants_join head overlapping_tail in
            let new_unique = SD.add new_head unique in
            let new_remaining = SD.diff tail overlapping_tail in
            f new_unique new_remaining
        in f (SD.empty ()) x
      in
      let new_x = join_comparable_key_variants x_with_y in
      new_x
    in
    join_x_y x y

  let meet x y =
    let result = meet_narrow_common SS.meet x y in
    if Messages.tracing then Messages.tracel "bot-bug" "Meet with x:\n%a\ny:\n%a\nresult:\n%a\n---------\n" SD.pretty x SD.pretty y SD.pretty result;
    result

  let join x y = (*join_widen_common SS.join x y *)
    let result = join_widen_common SS.join x y in
    (* if Messages.tracing then Messages.tracel "bot-bug" "Join with x:\n%a\ny:\n%a\nresult:\n%a\n---------\n" SD.pretty x SD.pretty y SD.pretty result; *)
    result

  let leq x y = (*leq_common SS.leq x y *)
    let result = leq_common SS.leq x y in
    if Messages.tracing then Messages.tracel "bot-bug" "Leq with x:\n%a\ny:\n%a\nresult:\n%b\n---------\n" SD.pretty x SD.pretty y result;
    result

  (* let equal x y = SD.equal x y || (leq x y && leq y x) *)
  let isSimple x = SD.isSimple x
  let hash x = SD.hash x

  let widen x y = join_widen_common SS.widen x y

  let narrow x y = (*meet_narrow_common SS.narrow x y*)
    let result = meet_narrow_common SS.narrow x y in
    if Messages.tracing then Messages.tracel "bot-bug" "Narrow with x:\n%a\ny:\n%a\nresult:\n%a\n---------\n" SD.pretty x SD.pretty y SD.pretty result;
    result


  let pretty_diff () (x,y) =
    Pretty.dprintf "{@[%a@] ...}" SD.pretty_diff (x,y)
  let printXml f xs = SD.printXml f xs
  let widen_with_fct f x y = join_widen_common (SS.widen_with_fct f) x y

  let leq_with_fct f x y = leq_common (SS.leq_with_fct f) x y

  let join_with_fct f x y = join_widen_common (SS.join_with_fct f) x y


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
