open EConstr
open Tactypes
open Names

type inhyps =
  | InList of variable list
  | AllMatchingBut of Id.Set.t

val induction_tac : with_evars:bool -> inhyps:inhyps -> constr list -> (constr with_bindings) option -> unit Proofview.tactic
