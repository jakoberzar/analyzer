(** Abstract domains representing structs. *)

open Cil

module type S =
sig
  include Lattice.S
  type field
  (** The abstract representation of field names. *)

  type value
  (** The abstract domain of values stored in the struct. *)

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
  val top_value: typ -> t
  val is_top_value: t -> typ -> bool
end

module Simple (Val: Lattice.S): S with type value = Val.t and type field = fieldinfo
(** Creates a simple structure domain by mapping fieldnames to their values
  * using the {!MapDomain.InfMap} functor *)

module SimpleSets (Val: LatticeWithBotValue): S with type value = Val.t and type field = fieldinfo

module BetterSets (Val: LatticeWithBotValue): S with type value = Val.t and type field = fieldinfo
