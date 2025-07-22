open EConstr
open Tactypes
open Names

type inhyps =
  | InList of variable list
  | AllMatchingBut of Id.Set.t

val induction_tac : with_evars:bool -> inhyps:inhyps -> constr -> constr with_bindings -> unit Proofview.tactic
