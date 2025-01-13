(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open CErrors
open Util
open Names
open Nameops
open Constr
open Context
open Termops
open Environ
open EConstr
open Vars
open Namegen
open Declarations
open Reductionops
open Tacred
open Genredexpr
open Tacmach
open Logic
open Clenv
open Tacticals
open Rocqlib
open Evarutil
open Indrec
open Unification
open Locus
open Locusops
open Tactypes
open Proofview.Notations
open Tactics

module NamedDecl = Context.Named.Declaration














(* TODO: Factor out (copy of tactics.ml) *)

module MakeProjections = struct

open Inductiveops
module RelDecl = Context.Rel.Declaration

type conjunction_status =
  | DefinedRecord of Constant.t option list
  | NotADefinedRecordUseScheme

let make_projection env sigma params cstr sign elim i n c (ind, u) =
  let open Context.Rel.Declaration in
  let elim = match elim with
  | NotADefinedRecordUseScheme ->
      (* bugs: goes from right to left when i increases! *)
      let cs_args = cstr.cs_args in
      let decl = List.nth cs_args i in
      let t = RelDecl.get_type decl in
      let b = match decl with LocalAssum _ -> mkRel (i+1) | LocalDef (_,b,_) -> b in
      if
        (* excludes dependent projection types *)
        noccur_between sigma 1 (n-i-1) t
        (* to avoid surprising unifications, excludes flexible
        projection types or lambda which will be instantiated by Meta/Evar *)
        && not (isEvar sigma (fst (whd_betaiota_stack env sigma t)))
        && (not (isRel sigma t))
      then
        let (_, mip) as specif = Inductive.lookup_mind_specif env ind in
        let t = lift (i + 1 - n) t in
        let ksort = Retyping.get_sort_quality_of (push_rel_context sign env) sigma t in
        if UnivGen.QualityOrSet.eliminates_to
             (UnivGen.QualityOrSet.of_quality @@ Inductiveops.elim_sort specif) ksort then
          let arity = List.firstn mip.mind_nrealdecls mip.mind_arity_ctxt in
          let mknas ctx = Array.of_list (List.rev_map get_annot ctx) in
          let ci = Inductiveops.make_case_info env ind RegularStyle in
          let br = [| mknas cs_args, b |] in
          let args = Context.Rel.instance mkRel 0 sign in
          let indr = ERelevance.make @@
            Inductive.relevance_of_ind_body mip (EConstr.Unsafe.to_instance u)
          in
          let pnas = Array.append (mknas (EConstr.of_rel_context arity)) [|make_annot Anonymous indr|] in
          let p = (pnas, lift (Array.length pnas) t) in
          let c = mkCase (ci, u, Array.of_list params, (p, get_relevance decl), NoInvert, mkApp (c, args), br) in
          Some (sigma, it_mkLambda_or_LetIn c sign, it_mkProd_or_LetIn t sign)
        else None
      else
        None
  | DefinedRecord l ->
      (* goes from left to right when i increases! *)
      match List.nth l i with
      | Some proj ->
          let args = Context.Rel.instance mkRel 0 sign in
          let sigma, proj =
            match Structures.PrimitiveProjections.find_opt_with_relevance (proj,u) with
            | Some (proj,r) ->
              sigma, mkProj (Projection.make proj false, r, mkApp (c, args))
            | None ->
              let env = EConstr.push_rel_context sign env in
              let args = Array.append (Array.of_list params) [|mkApp (c, args)|] in
              Typing.checked_appvect env sigma (mkConstU (proj, u)) args
          in
          let app = it_mkLambda_or_LetIn proj sign in
          let t = Retyping.get_type_of env sigma app in
            Some (sigma, app, t)
      | None -> None
  in elim

let make_projections env sigma c =
  let t = Retyping.get_type_of env sigma c in
  let ((ind,u),t) = reduce_to_quantified_ind env sigma t in
  let sign,ccl = EConstr.decompose_prod_decls sigma t in
  let n = (constructors_nrealargs env ind).(0) in
  let IndType (indf,_) = find_rectype env sigma ccl in
  let (_,inst), params = dest_ind_family indf in
  let cstr = (get_constructors env indf).(0) in
  let elim =
    try DefinedRecord (Structures.Structure.find_projections ind)
    with Not_found -> NotADefinedRecordUseScheme
  in
  let sigma, projtys = List.fold_left_map (fun sigma i ->
    match make_projection env sigma params cstr sign elim i n c (ind, u) with
    | Some (sigma, pr, ty) -> sigma, Some (pr, ty) | None -> sigma, None)
    sigma (List.init n (fun i -> i))
  in
  sigma, List.filter_map (fun x -> x) projtys
end
open MakeProjections











exception AlreadyUsed of Id.t
exception SchemeDontApply
exception NeedFullyAppliedArgument
exception NotAnInductionScheme of string
exception NotAnInductionSchemeLetIn
exception CannotFindInductiveArgument
exception MentionConclusionDependentOn of Id.t
exception DontKnowWhatToDoWith of intro_pattern_naming_expr
exception UnsupportedWithClause
exception UnsupportedEqnClause
exception UnsupportedInClause of bool
exception DontKnowWhereToFindArgument
exception MultipleAsAndUsingClauseOnlyList


let error ?loc e =
  Loc.raise ?loc e

let occur_rel sigma n c =
  let res = not (noccurn sigma n c) in
  res


let error_ind_scheme s = error (NotAnInductionScheme s)

let typ_of env sigma c =
  let open Retyping in
  try get_type_of ~lax:true env sigma c
  with RetypeError e ->
    user_err (print_retype_error e)











(*
   The general form of an induction principle is the following:

   forall prm1 prm2 ... prmp,                          (induction parameters)
   forall Q1...,(Qi:Ti_1 -> Ti_2 ->...-> Ti_ni),...Qq, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main induction arg)
   -> (Qi x1...xni HI        (f prm1...prmp x1...xni)).(conclusion)
                   ^^        ^^^^^^^^^^^^^^^^^^^^^^^^
               optional        optional argument added if
               even if HI    principle generated by functional
             present above   induction, only if HI does not exist
             [indarg]                  [farg]

  HI is not present when the induction principle does not come directly from an
  inductive type (like when it is generated by functional induction for
  example). HI is present otherwise BUT may not appear in the conclusion
  (dependent principle). HI and (f...) cannot be both present.

  Principles taken from functional induction have the final (f...).*)

(* [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)

type elim_scheme = {
  elimt: types;
  indref: GlobRef.t option;
  params: rel_context;      (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;               (* number of parameters *)
  predicates: rel_context;  (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;           (* Number of predicates *)
  branches: rel_context;    (* branchr,...,branch1 *)
  nbranches: int;             (* Number of branches *)
  args: rel_context;        (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;                 (* number of arguments *)
  indarg: rel_declaration option; (* Some (H,I prm1..prmp x1...xni)
                                                if HI is in premisses, None otherwise *)
  concl: types;               (* Qi x1...xni HI (f...), HI and (f...)
                                  are optional and mutually exclusive *)
  indarg_in_concl: bool;      (* true if HI appears at the end of conclusion *)
  farg_in_concl: bool;        (* true if (f...) appears at the end of conclusion *)
}

let empty_scheme =
  {
    elimt = mkProp;
    indref = None;
    params = [];
    nparams = 0;
    predicates = [];
    npredicates = 0;
    branches = [];
    nbranches = 0;
    args = [];
    nargs = 0;
    indarg = None;
    concl = mkProp;
    indarg_in_concl = false;
    farg_in_concl = false;
  }







(**
What does the induction tactic do ?
[induction expr in x, y, z as intropattern with (P := a) using elim_ind.] (+ funelim)

0a. Get type of expr, query [elim_ind] if not given
0b. Get the result of [e := elim_ind with (P := a)] (adapt for destruct, funelim)
0c. Get the result of [elim := e with progress_rev expr]

Shared trunk
2. Ensure the return type [T] of [elim] is of the shape [?P@{a1; .. an} t1 .. tn]
3. Unify [?Goal] against [?P₀@{a1; .. an} t1 .. tn], fully resolving the evars in [T] (evars in [?Goal] allowed, resolving those also allowed (after the ones in T))
4-pre. Store [x : Tx, y : Ty, z : Tz] (default list : all) in a container
4. Do a pattern search for the now solved [t1 .. tn] in the container types (first as [_ t1 .. tn], then one at a time),
  replace them with their names [a, b, c] from [?P]'s (product) type.
5. If [dependent], add [(a; b .. ; c) = (t1 ; .. ; tn)] to the container (to be dealt with equations' simplify)
5b. If [eqn:e] check if [tn = expr], check that [c]'s type doesn't depend on [a, b] (else redirect to dependent), then add [e : c = tn] to the container
6. If the list [x, y, z] was not given explicitly, restrict the container to only variables who depend on [a, b, .. c]
7. Set [?P := fun a b c => forall container, ?P₀], refine with [e container]
8. Clear all variables which are in the container. For all [t1 .. tn] which are in fact variables, try clearing them as well. (cannot erase hypothesis warning goes here)
9. If applicable, for all branch goals, equations simplify container.
10. (Now that branches have been pruned) apply the intropattern; intros until ?P, then for the length of the container
11. Close the tactic (check for remaining evars in [e])

elim_ind is an induction principle, with its uniform parameters, predicates, some branches for obligations, non-uniform parameters and the proved predicate.

Identify and unify the induction discriminee inside the induction principle type; either as last product domain of the type (regular induction) or last argument of the final codomain (functional induction)
This means the induction principle has shape (∀ _ .. _, P x1 .. xn T, case 2) or else (∀ _ .. _, ∀ (x : T), P x1 .. xn, case 1) where T is the location of the discriminee

in the unification, extract the list of non-uniform parameters:
3 cases: (in induction principle vs in discriminee)

variable x vs variable y: normal case, rename y into x, regular procedure
variable x vs term: do a [set (x := t) in [in_list, default *].], then regular procedure with x (+ if dependent, add in [x = t] as hypothesis)
term vs term: if unifiable, then do as above for the found unification matches
if in case 2, do a [set (fx := T) in [in_list, default *].] and proceed as in case 1

Generalize over all hypotheses whose types depend on x1 .. xn (+ fx)

(Generalize over the dependent equalities)
Generalize over all remaining hypotheses listed in the [in_list] (cannot erase hypothesis warning goes here)
Invert the goal as a function of x1 .. xn (+ fx)
(If given in the binding, unify the found proved predicate with the given value, don't bother accepting if they don't unify)
We now have constructed the proved predicate, the instances of the non-uniform parameter arguments, and also some uniform parameters as extracted from the discriminee

refine elim_ind, using the given uniform parameters, found predicate, non-uniform parameters, and with help from the given additional bindings

There remains holes / goals, of two classes: goals which mention the proved predicate in the final codomain (proof obligations) and the others (proof parameters)

All parameter goals are left as-is

In the obligation branches (the other goals), introduce the variables until the proved predicate (using the names from the induction principle or from the intropattern, somewhat unfortunate that we can't have more custom name generation method here)
then reintroduce the generalized variables with their original names (freshened), (then dependent equalities), then generalized hypotheses with their original names (freshened)

Give back control to the user

Good: Almost no constraint on elim_ind type (only the final codomain is constrained)
Bad: Not the expected behavior for induction principles with >1 mutual predicate

Alternative with the expected behavior : enforce shape being ∀ p1 .. pn P1 .. Pn, B1 -> .. Bn -> ∀ pu1 .. pun, P x1 .. xn (order of pi, Pi, Bi, pui wouldn't in fact matter); identify branches as nondependent and predicates as their final codomains. If no branches, only P is taken as predicate
Then, for all obligation branches, introduce the variables in the same way (requires that all predicates are as generalized as P which is annoying to do by hand)

Also, we could not require that the final codomain of elim_ind be [P x1 .. xn (T)] but allow [P t1 .. tn (T)]; the disambiguation between case 1 or 2 of discriminee location would become entirely external (funind vs induction), and we would do for all t [set xi := ti in [in_list, default *].], as is done with [fx] in funind.

Finally, I didn't include eqn: here, I assume it's straightforward enough (similar to dependent equalities but for the whole discriminee ?); I also didn't include occurrences, since I don't know where they fit exactly.
*)



type elim_scheme = {
  elimc: constr;
  elimt: types; (* [?P@{a1 .. an} t1 .. tn] *)

  preds : Evar.t list; (* nonempty, starts with ?P *)
  shared_inst: int list; (* subset of indices of [t1 .. tk] which is shared by all preds *)

  main_branches : Evar.t list; (* Type is ?P u1 .. un *)
  other_branches : Evar.t list; (* Type is ?Q v1 .. vp *)
  other_holes : Evar.t list;

}


let eliminator_of_constr env sigma ?decider elimc with_bindings =

  let elimt = Retyping.get_type_of env sigma elimc in

  let rec get_ccls sigma elimc elimt =
    let sigma, cl = EClause.make_evar_clause env sigma elimt in
    let elimc = mkApp (elimc, Array.map_of_list (fun hole -> hole.EClause.hole_evar) cl.cl_holes) in
    let ccl_head, ccl_inst = decompose_app sigma cl.cl_concl in
    match EConstr.kind sigma ccl_head with
    | Evar (evk, _) -> [sigma, cl.cl_holes, (evk, ccl_inst)]
    | _ ->
      if Hipattern.is_tuple env sigma cl.cl_concl then
        let sigma, projtys = make_projections env sigma elimc in
        let ccls = List.map_append (fun (elimc, elimt) -> get_ccls sigma elimc elimt) projtys in
        let ccls = List.map (fun (sigma, holes, evkinst) -> (sigma, cl.cl_holes @ holes, evkinst)) ccls in
        ccls
      else failwith "Not an inductive scheme, ccl doesn't start with a bound variable"
  in
  let ccls = get_ccls sigma elimc elimt in

  let sigma, holes, main_pred, preds, shared_inst =
    match ccls, decider with
    | [sigma, holes, (evk, inst)], _ -> sigma, holes, evk, [], inst
    | [], _ -> assert false
    | _, None -> failwith "More than one branch, cannot decide"
    | ccls, Some decider ->
      let ty = Retyping.get_type_of env sigma decider in
      let j = Environ.make_judge decider ty in

      let t = Retyping.get_type_of env sigma ev in
      let (sigma, j, _trace) = Coercion.inh_conv_coerce_to ~program_mode:false ~resolve_tc:true env sigma j t in

  let non_dep_evars =
    let cache = Evarutil.create_undefined_evars_cache () in
    let on_evar ev =
      let evi = Evd.find_undefined sigma ev in
      Evarutil.filtered_undefined_evars_of_evar_info ~cache sigma evi
    in
    let depevars =
      List.fold_left (fun set ev -> Evar.Set.union set (on_evar ev))
        Evar.Set.empty evars
    in
    Evar.Set.diff evar_set depevars
  in

  let evar_concl_evars =
    let on_evar ev =
      let evi = Evd.find_undefined sigma ev in
      let evty = Evd.evar_concl evi in
      let _, ev_ccl = EConstr.decompose_prod_decls sigma evty in
      isEvar sigma ev_ccl
    in
    Evar.Set.filter on_evar evar_set
  in

  let branches = Evar.Set.inter non_dep_evars evar_concl_evars in

  let main_branches =
    Evar.Set.filter (fun ev ->
      let evi = Evd.find_undefined sigma ev in
      let evty = Evd.evar_concl evi in
      let _, ev_ccl = EConstr.decompose_prod_decls sigma evty in
      match EConstr.kind sigma ev_ccl with
      | Evar (ev, inst) -> Evar.equal ev elim_pred
      | _ -> false) evar_concl_evars
  in

  if not (Evar.Set.subset main_branches branches) then
    failwith "Not an inductive scheme, some branches appear dependently in other arguments";

  let other_branches = Evar.Set.diff branches main_branches in

  let other_predicates =
    let on_evar ev =
      let evi = Evd.find_undefined sigma ev in
      let evty = Evd.evar_concl evi in
      let _, ev_ccl = EConstr.decompose_prod_decls sigma evty in
      fst @@ destEvar sigma ev_ccl
    in
    Evar.Set.map on_evar other_branches
  in

  let scheme = { elimc; elim_pred; elim_instance; main_branches; other_predicates; other_branches } in
  sigma, scheme, evars





let main discrs patopt inclauseopt (elimc, elimt) with_bindings =


  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.concl gl in

  let inclause = Option.default allHypsAndConcl inclauseopt in

  let elim_shape = compute_elim_sig sigma elimt in
  let prods = elim_shape.prods in
  let main_pred_id = elim_shape.main_pred in

  let discrts = Array.map (typ_of env evd) discrs in
  let discrt_pats = Array.sub prods (Array.length prods - Array.length discrs) (Array.length discrs) in

  let evd, unification_results = Array.fold_left2 (fun (evd, results) typat ty -> _unify env evd typat ty) (evd, _) discrt_pats discrts in

  let () = M.fold (fun (var, term) -> Tactics.set var term inclause) unification_results in

  let vars = M.get_all_vars unification_results in

  let () = if Option.has_some inclauseopt then
    Tactics.revert inclause
  else
    Proofview.Goal.hyps gl
    |> List.filter (occur_vars_in_decl env evd vars)
    |> List.map (NamedDecl.get_id)
    |> Tactics.revert
  in

  let evd, main_pred =
    match Bindings.find main_pred_id with_bindings with
    | Some c ->
        let evd = _unify  env evd c ccl in (* TODO: What about sets and reverts ?? *)
        evd, c
    | None -> evd, ccl (* TODO: What about sets and reverts ?? *)
  in


  let () = Tactics.eapply_with_bindings (elim, with_bindings) in


  let () = Array.map (fun gl -> Tactics.intro gl) preds in






  end






































type ccl_args =
  | AllVars of int array
  | Free of constr array
(*
type elim_scheme = {
  elimt: types;
  indref: GlobRef.t option;
  params: rel_context;      (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;               (* number of parameters *)
  predicates: rel_context;  (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;           (* Number of predicates *)

  args: rel_context;        (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;                 (* number of arguments *)
  indarg: rel_declaration option; (* Some (H,I prm1..prmp x1...xni)
                                                if HI is in premisses, None otherwise *)
  concl: types;               (* Qi x1...xni HI (f...), HI and (f...)
                                  are optional and mutually exclusive *)
  indarg_in_concl: bool;      (* true if HI appears at the end of conclusion *)

  branches: Int.Set.t;
  preds: Int.Set.t; (* From the top, indices of the products for the predicates. Alternatively, indices of the arguments in the application of the principle (1-indexed) *)
  ccl_pred: int;        (* From the top, index of the product for the predicate used in the conclusion. Alternatively, index of the argument in the application of the principle (1-indexed) *)
  ccl_args: ccl_args;
} *)


(* Logs all rels which appear in the term, shifted by some amount *)
let add_free_rels_shf sigma shf set m =
  let rec frec depth acc c = match EConstr.kind sigma c with
    | Rel n -> if n >= depth then Int.Set.add (shf - (n - depth)) acc else acc
    | Evar (_, args) -> SList.Skip.fold (frec depth) acc args
    | _ -> EConstr.fold_with_binders sigma succ frec depth acc c
  in
  frec 1 set m

let add_free_rels_decl_shf sigma shf set d =
  let open Context.Rel.Declaration in
  let set = Option.fold_left (add_free_rels_shf sigma shf) set (get_value d) in
  add_free_rels_shf sigma shf set (get_type d)

let rec find_branches_and_preds sigma doms =
  let branches = Array.fold_left_i (fun i s m -> add_free_rels_decl_shf sigma i s m) Int.Set.empty doms in

  let preds = Array.mapi (fun i d ->
    if not (Int.Set.mem i branches) then None else
    let t = Context.Rel.Declaration.get_type d in
    let _, ccl = EConstr.decompose_prod_decls sigma t in
    let ccl_pred, _ = EConstr.decompose_app sigma ccl in
    match EConstr.destRel sigma ccl_pred with
    | n -> Some (i - n + 1)
    | exception DestKO -> None)
    doms
  in

  let real_branches = Int.Set.filter (fun i -> Option.has_some (preds.(i))) in
  let preds_set = Array.fold_left (Option.fold_left (fun s i -> Int.Set.add i s)) Int.Set.empty preds in
  real_branches, preds_set



let decompose_elimt_prods sigma elimt =
  let doms, ccl = EConstr.decompose_prod_decls sigma elimt in
  let doms = Array.rev_of_list doms in
  let nprods = Array.length doms in

  let ccl_pred, ccl_args = EConstr.decompose_app sigma ccl in

  let ccl_pred = match EConstr.kind sigma ccl_pred with
    | Rel j -> nprods - j + 1
    | _ -> failwith "Not an inductive scheme, ccl doesn't start with a bound variable"
  in

  let branches, preds = find_branches_and_preds sigma doms in

  let ccl_args =
    match Array.map (EConstr.destRel sigma) ccl_args with
    | a -> AllVars a
    | exception DestKO -> Free ccl_args
  in


  0

let intropattern_of_name = function
  | Anonymous -> IntroAnonymous
  | Name id -> IntroIdentifier id

let subst_red env sigma subst c =
  let c = esubst lift_substituend subst c in
  let c = Reductionops.nf_beta env sigma c in
  c


let rec elim_apply_evars ?handler env sigma subst evars elimc elimt =
  (* Use [whd_prod_app_gen] instead *)
  match EConstr.kind sigma elimt with
  | Cast (ccl, _, _) ->
    elim_apply_evars env sigma subst evars elimc elimt
  | LetIn (_, def, _, ccl) ->
    let subst = Esubst.subs_cons (make_substituend def) subst in
    elim_apply_evars env sigma subst evars elimc elimt
  | Prod (na, ty, ccl) ->
    let ty = subst_red env sigma subst ty in

    let ev, evc =
      (* If dependent, then definitely not a branch, otherwise it may be so we do intros later *)
      if occur_rel sigma 1 ccl then
        let ty_hyps, ty_ccl = EConstr.decompose_prod_decls sigma ty in
        let env = Environ.push_rel_context (EConstr.Unsafe.to_rel_context ty_hyps) env in
        (* This env is only used to make a named env for evar creation *)

        let sigma, evc = Evarutil.new_evar
          ~relevance:(Context.binder_relevance na)
          ~naming:(intropattern_of_name (Context.binder_name na))
          env sigma ty_ccl
        in
        let ev, _ = destEvar sigma evc in
        let evc = it_mkLambda_or_LetIn evc ty_hyps in
        ev, evc
      else
        let sigma, evc = Evarutil.new_evar
          ~relevance:(Context.binder_relevance na)
          ~naming:(intropattern_of_name (Context.binder_name na))
          env sigma ty
        in
        let ev, _ = destEvar sigma evc in
        ev, evc
    in
    let subst = Esubst.subs_cons (make_substituend evc) subst in
    let elimc = mkApp (elimc, [|evc|]) in
    elim_apply_evars env sigma subst (ev :: evars) elimc ccl
  | _ ->
    match Option.map (fun f -> f sigma elimc elimt) handler with
    | Some (sigma, elimc, elimt) ->
      elim_apply_evars env sigma subst evars elimc elimt
    | None ->
      let ccl = subst_red env sigma subst elimt in
      (sigma, elimc, evars, ccl)

let elim_apply_evars ?handler env sigma elimc elimt =
  elim_apply_evars ?handler env sigma (Esubst.subs_id 0) [] elimc elimt


let do_intros sigma ?(intropattern=IntroAnonymous) evk =
  let evi = Evd.find_undefined sigma evk in
  let evty = Evd.evar_concl evi in
  let ev_hyps, ev_ccl = EConstr.decompose_prod_decls sigma evty in
  assert false



type elim_scheme = {
  elimc: constr;
  elim_pred: Evar.t;
  elim_instance: constr list;

  main_branches: Evar.Set.t;
  other_predicates: Evar.Set.t;
  other_branches: Evar.Set.t;
}


let eliminator_of_constr env sigma elimc elimt (* TODO: How and where do we get these *) =

  let sigma, elimc, evars, ccl = elim_apply_evars env sigma elimc elimt in
  let evar_set = Evar.Set.of_list evars in

  let elim_pred, elim_instance = match EConstr.kind sigma ccl with
    | Evar (ev, inst) ->
      let inst = List.map Option.get @@ SList.to_list inst in
      (* There should be no Var since this is a well typed reduct of (fun Γ -> ?P@{Γ}) args *)
      ev, inst
    | _ -> failwith "Not an inductive scheme, ccl doesn't start with a bound variable"
  in

  let non_dep_evars =
    let cache = Evarutil.create_undefined_evars_cache () in
    let on_evar ev =
      let evi = Evd.find_undefined sigma ev in
      Evarutil.filtered_undefined_evars_of_evar_info ~cache sigma evi
    in
    let depevars =
      List.fold_left (fun set ev -> Evar.Set.union set (on_evar ev))
        Evar.Set.empty evars
    in
    Evar.Set.diff evar_set depevars
  in

  let evar_concl_evars =
    let on_evar ev =
      let evi = Evd.find_undefined sigma ev in
      let evty = Evd.evar_concl evi in
      let _, ev_ccl = EConstr.decompose_prod_decls sigma evty in
      isEvar sigma ev_ccl
    in
    Evar.Set.filter on_evar evar_set
  in

  let branches = Evar.Set.inter non_dep_evars evar_concl_evars in

  let main_branches =
    Evar.Set.filter (fun ev ->
      let evi = Evd.find_undefined sigma ev in
      let evty = Evd.evar_concl evi in
      let _, ev_ccl = EConstr.decompose_prod_decls sigma evty in
      match EConstr.kind sigma ev_ccl with
      | Evar (ev, inst) -> Evar.equal ev elim_pred
      | _ -> false) evar_concl_evars
  in

  if not (Evar.Set.subset main_branches branches) then
    failwith "Not an inductive scheme, some branches appear dependently in other arguments";

  let other_branches = Evar.Set.diff branches main_branches in

  let other_predicates =
    let on_evar ev =
      let evi = Evd.find_undefined sigma ev in
      let evty = Evd.evar_concl evi in
      let _, ev_ccl = EConstr.decompose_prod_decls sigma evty in
      fst @@ destEvar sigma ev_ccl
    in
    Evar.Set.map on_evar other_branches
  in

  let scheme = { elimc; elim_pred; elim_instance; main_branches; other_predicates; other_branches } in
  sigma, scheme, evars



let destruct_make_elim env sigma c indt brnas (* TODO: How and where do we get it *) =
  let open Inductiveops in
  let IndType (indupar, _) = indt in
  let (ind, u) as indu, pms = dest_ind_family indupar in
  let pms = Array.of_list pms in
  let ci = make_case_info env ind MatchStyle in

  let mib, mip = Inductive.lookup_mind_specif env ind in

  let pnas : (_, Evd.erelevance) pbinder_annot array =
    match EConstr.Unsafe.relevance_eq with Refl ->
    let decls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let decls = Context.make_annot Anonymous mip.mind_relevance :: List.map Context.Rel.Declaration.get_annot decls in
    Array.rev_of_list decls
  in
  let pctx = expand_return_context env sigma indu pms pnas in
  let penv = Environ.push_rel_context (EConstr.Unsafe.to_rel_context pctx) env in
  (* This env is only used to make a named env for evar creation *)
  let sigma, (evret, _) = Evarutil.new_type_evar penv sigma UState.univ_flexible_alg in

  let brctxs = expand_branch_contexts env sigma indu pms (Array.map (Array.map annotR) brnas) in

  let sigma, brs = Array.fold_left_map (fun sigma brctx ->
    let brenv = Environ.push_rel_context (EConstr.Unsafe.to_rel_context brctx) env in
    (* This env is only used to make a named env for evar creation *)
    let sigma, (evbr, _) = Evarutil.new_evar penv sigma UState.univ_flexible_alg in

    ) sigma brctxs

  let elimc = new_make_case_or_project
    env sigma indt ci ((pnas, evret), ERelevance.relevant) c


  in
  sigma, scheme











let main discrs patopt inclauseopt (elim, elimt) with_bindings =

  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.concl gl in

  let inclause = Option.default allHypsAndConcl inclauseopt in

  let elim_shape = compute_elim_sig sigma elimt in
  let prods = elim_shape.prods in
  let main_pred_id = elim_shape.main_pred in

  let discrts = Array.map (typ_of env evd) discrs in
  let discrt_pats = Array.sub prods (Array.length prods - Array.length discrs) (Array.length discrs) in

  let evd, unification_results = Array.fold_left2 (fun (evd, results) typat ty -> _unify env evd typat ty) (evd, _) discrt_pats discrts in

  let () = M.fold (fun (var, term) -> Tactics.set var term inclause) unification_results in

  let vars = M.get_all_vars unification_results in

  let () = if Option.has_some inclauseopt then
    Tactics.revert inclause
  else
    Proofview.Goal.hyps gl
    |> List.filter (occur_vars_in_decl env evd vars)
    |> List.map (NamedDecl.get_id)
    |> Tactics.revert
  in

  let evd, main_pred =
    match Bindings.find main_pred_id with_bindings with
    | Some c ->
        let evd = _unify  env evd c ccl in (* TODO: What about sets and reverts ?? *)
        evd, c
    | None -> evd, ccl (* TODO: What about sets and reverts ?? *)
  in


  let () = Tactics.eapply_with_bindings (elim, with_bindings) in


  let () = Array.map (fun gl -> Tactics.intro gl) preds in






  end


let induction_gen clear_flag isrec with_evars elim
    ((_pending,(c,lbind)),(eqname,names) as arg) cls =
  let inhyps = match cls with
  | Some {onhyps=Some hyps} -> List.map (fun ((_,id),_) -> id) hyps
  | _ -> [] in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.concl gl in
  let cls = Option.default allHypsAndConcl cls in
  let t = typ_of env evd c in
  let is_arg_pure_hyp =
    isVar evd c && not (mem_named_context_val (destVar evd c) (Global.named_context_val ()))
    && lbind == NoBindings && not with_evars && Option.is_empty eqname
    && clear_flag == None
    && has_generic_occurrences_but_goal cls (destVar evd c) env evd ccl in
  let enough_applied = check_enough_applied env evd elim t in
  if is_arg_pure_hyp && enough_applied then
    (* First case: induction on a variable already in an inductive type and
       with maximal abstraction over the variable.
       This is a situation where the induction argument is a
       clearable variable of the goal w/o occurrence selection
       and w/o equality kept: no need to generalize *)
    let id = destVar evd c in
    Tacticals.tclTHEN
      (clear_unselected_context id inhyps cls)
      (induction_with_atomization_of_ind_arg
         isrec with_evars elim names id inhyps)
  else
  (* Otherwise, we look for the pattern, possibly adding missing arguments and
     declaring the induction argument as a new local variable *)
    let id =
    (* Type not the right one if partially applied but anyway for internal use*)
      let avoid = match eqname with
        | Some {CAst.v=IntroIdentifier id} -> Id.Set.singleton id
        | _ -> Id.Set.empty in
      let x = id_of_name_using_hdchar env evd t Anonymous in
      new_fresh_id avoid x gl in
    let info_arg = (is_arg_pure_hyp, not enough_applied) in
    pose_induction_arg_then
      isrec with_evars info_arg elim id arg t inhyps cls
    (induction_with_atomization_of_ind_arg
       isrec with_evars elim names id)
  end

(* Induction on a list of arguments. First make induction arguments
   atomic (using letins), then do induction. The specificity here is
   that all arguments and parameters of the scheme are given
   (mandatory for the moment), so we don't need to deal with
    parameters of the inductive type as in induction_gen. *)
let induction_gen_l isrec with_evars elim names lc =
  let newlc = ref [] in
  let lc = List.map (function
    | (c,None) -> c
    | (c,Some{CAst.loc;v=eqname}) ->
      error ?loc (DontKnowWhatToDoWith eqname)) lc in
  let rec atomize_list l =
    match l with
      | [] -> Proofview.tclUNIT ()
      | c::l' ->
          Proofview.tclEVARMAP >>= fun sigma ->
          match EConstr.kind sigma c with
            | Var id when not (mem_named_context_val id (Global.named_context_val ()))
                && not with_evars ->
                let () = newlc:= id::!newlc in
                atomize_list l'

            | _ ->
                Proofview.Goal.enter begin fun gl ->
                let sigma, t = pf_apply Typing.type_of gl c in
                let x = id_of_name_using_hdchar (Proofview.Goal.env gl) sigma t Anonymous in
                let id = new_fresh_id Id.Set.empty x gl in
                let newl' = List.map (fun r -> replace_term sigma c (mkVar id) r) l' in
                let () = newlc:=id::!newlc in
                Tacticals.tclTHENLIST [
                  tclEVARS sigma;
                  Tactics.letin_tac None (Name id) c None allHypsAndConcl;
                  atomize_list newl';
                ]
                end in
  Tacticals.tclTHENLIST
    [
      (atomize_list lc);
      (Proofview.tclUNIT () >>= fun () -> (* ensure newlc has been computed *)
        induction_without_atomization isrec with_evars elim names !newlc)
    ]

(* Induction either over a term, over a quantified premisse, or over
   several quantified premisses (like with functional induction
   principles).
   TODO: really unify induction with one and induction with several
   args *)
let induction_destruct isrec with_evars (lc,elim) =
  match lc with
  | [] -> assert false (* ensured by syntax, but if called inside caml? *)
  | [c,(eqname,names as allnames),cls] ->
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    match elim with
    | Some elim when is_functional_induction elim gl ->
      (* Standard induction on non-standard induction schemes *)
      (* will be removable when is_functional_induction will be more clever *)
      if not (Option.is_empty cls) then error (UnsupportedInClause true);
      let _,c = force_destruction_arg false env sigma c in
      onInductionArg
        (fun _clear_flag c ->
          induction_gen_l isrec with_evars elim names
            [with_no_bindings c,eqname]) c
    | _ ->
      (* standard induction *)
      onOpenInductionArg env sigma
      (fun clear_flag c -> induction_gen clear_flag isrec with_evars elim (c,allnames) cls) c
    end
  | _ ->
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    match elim with
    | None ->
      (* Several arguments, without "using" clause *)
      (* TODO: Do as if the arguments after the first one were called with *)
      (* "destruct", but selecting occurrences on the initial copy of *)
      (* the goal *)
      let (a,b,cl) = List.hd lc in
      let l = List.tl lc in
      (* TODO *)
      Tacticals.tclTHEN
        (onOpenInductionArg env sigma (fun clear_flag a ->
          induction_gen clear_flag isrec with_evars None (a,b) cl) a)
        (Tacticals.tclMAP (fun (a,b,cl) ->
          Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Tacmach.project gl in
          onOpenInductionArg env sigma (fun clear_flag a ->
            induction_gen clear_flag false with_evars None (a,b) cl) a
          end) l)
    | Some elim ->
      (* Several induction hyps with induction scheme *)
      let lc = List.map (on_pi1 (fun c -> snd (force_destruction_arg false env sigma c))) lc in
      let newlc =
        List.map (fun (x,(eqn,names),cls) ->
          if cls != None then error UnsupportedEqnClause;
          match x with (* FIXME: should we deal with ElimOnIdent? *)
          | _clear_flag,ElimOnConstr x ->
              if eqn <> None then error (UnsupportedInClause false);
              (with_no_bindings x,names)
          | _ -> error DontKnowWhereToFindArgument)
          lc in
      (* Check that "as", if any, is given only on the last argument *)
      let names,rest = List.sep_last (List.map snd newlc) in
      if List.exists (fun n -> not (Option.is_empty n)) rest then
        error MultipleAsAndUsingClauseOnlyList;
      let newlc = List.map (fun (x,_) -> (x,None)) newlc in
      induction_gen_l isrec with_evars elim names newlc
    end

let induction ev clr c l e =
  induction_gen clr true ev e
    ((None,(c,NoBindings)),(None,l)) None

let destruct ev clr c l e =
  induction_gen clr false ev e
    ((None,(c,NoBindings)),(None,l)) None













































































(* This function splits the products of the induction scheme [elimt] into four
   parts:
   - branches, easily detectable (they are not referred by rels in the subterm)
   - what was found before branches (acc1) that is: parameters and predicates
   - what was found after branches (acc3) that is: args and indarg if any
   if there is no branch, we try to fill in acc3 with args/indargs.
   We also return the conclusion.
*)
let decompose_paramspred_branch_args sigma elimt =
  let open Context.Rel.Declaration in
  let rec cut_noccur elimt acc2 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,elimt') ->
          let hd_tpe,_ = decompose_app sigma (snd (decompose_prod_decls sigma tpe)) in
          if not (occur_rel sigma 1 elimt') && isRel sigma hd_tpe
          then cut_noccur elimt' (LocalAssum (nme,tpe)::acc2)
          else let acc3,ccl = decompose_prod_decls sigma elimt in acc2 , acc3 , ccl
      | App(_, _) | Rel _ -> acc2 , [] , elimt
      | _ -> error_ind_scheme "" in
  let rec cut_occur elimt acc1 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,c) when occur_rel sigma 1 c -> cut_occur c (LocalAssum (nme,tpe)::acc1)
      | Prod(nme,tpe,c) -> let acc2,acc3,ccl = cut_noccur elimt [] in acc1,acc2,acc3,ccl
      | App(_, _) | Rel _ -> acc1,[],[],elimt
      | _ -> error_ind_scheme "" in
  let acc1, acc2 , acc3, ccl = cut_occur elimt [] in
  (* Particular treatment when dealing with a dependent empty type elim scheme:
     if there is no branch, then acc1 contains all hyps which is wrong (acc1
     should contain parameters and predicate only). This happens for an empty
     type (See for example Empty_set_ind, as False would actually be ok). Then
     we must find the predicate of the conclusion to separate params_pred from
     args. We suppose there is only one predicate here. *)
  match acc2 with
  | [] ->
    let hyps,ccl = decompose_prod_decls sigma elimt in
    let hd_ccl_pred,_ = decompose_app sigma ccl in
    begin match EConstr.kind sigma hd_ccl_pred with
      | Rel i  -> let acc3,acc1 = List.chop (i-1) hyps in acc1 , [] , acc3 , ccl
      | _ -> error_ind_scheme ""
    end
  | _ -> acc1, acc2 , acc3, ccl









let exchange_hd_app sigma subst_hd t =
  let hd,args= decompose_app sigma t in mkApp (subst_hd, args)






(* Builds an elim_scheme from its type and calling form (const+binding). We
   first separate branches.  We obtain branches, hyps before (params + preds),
   hyps after (args <+ indarg if present>) and conclusion.  Then we proceed as
   follows:

   - separate parameters and predicates in params_preds. For that we build:
 forall (x1:Ti_1)(xni:Ti_ni) (HI:I prm1..prmp x1...xni), DUMMY x1...xni HI/farg
                             ^^^^^^^^^^^^^^^^^^^^^^^^^                  ^^^^^^^
                                       optional                           opt
     Free rels appearing in this term are parameters (branches should not
     appear, and the only predicate would have been Qi but we replaced it by
     DUMMY). We guess this heuristic catches all params.  TODO: generalize to
     the case where args are merged with branches (?) and/or where several
     predicates are cited in the conclusion.

   - finish to fill in the elim_scheme: indarg/farg/args and finally indref. *)
let compute_elim_sig sigma elimt =
  let open Context.Rel.Declaration in
  let params_preds,branches,args_indargs,conclusion =
    decompose_paramspred_branch_args sigma elimt in

  let ccl = exchange_hd_app sigma (mkVar (Id.of_string "__QI_DUMMY__")) conclusion in
  let concl_with_args = it_mkProd_or_LetIn ccl args_indargs in
  let nparams = Int.Set.cardinal (free_rels sigma concl_with_args) in
  let preds,params = List.chop (List.length params_preds - nparams) params_preds in

  (* A first approximation, further analysis will tweak it *)
  let res = ref { empty_scheme with
    (* This fields are ok: *)
    elimt = elimt; concl = conclusion;
    predicates = preds; npredicates = List.length preds;
    branches = branches; nbranches = List.length branches;
    farg_in_concl = isApp sigma ccl && isApp sigma (last_arg sigma ccl);
    params = params; nparams = nparams;
    (* all other fields are unsure at this point. Including these:*)
    args = args_indargs; nargs = List.length args_indargs; } in
  try
    (* Order of tests below is important. Each of them exits if successful. *)
    (* 1- First see if (f x...) is in the conclusion. *)
    if !res.farg_in_concl
    then begin
      res := { !res with
        indarg = None;
        indarg_in_concl = false; farg_in_concl = true };
      raise_notrace Exit
    end;
    (* 2- If no args_indargs (=!res.nargs at this point) then no indarg *)
    if Int.equal !res.nargs 0 then raise_notrace Exit;
    (* 3- Look at last arg: is it the indarg? *)
    ignore (
      match List.hd args_indargs with
        | LocalDef (hiname,_,hi) -> error_ind_scheme ""
        | LocalAssum (hiname,hi) ->
            let hi_ind, hi_args = decompose_app sigma hi in
            let hi_is_ind = (* hi est d'un type globalisable *)
              match EConstr.kind sigma hi_ind with
                | Ind (mind,_)  -> true
                | Var _ -> true
                | Const _ -> true
                | Construct _ -> true
                | _ -> false in
            let hi_args_enough = (* hi a le bon nbre d'arguments *)
              Int.equal (Array.length hi_args) (List.length params + !res.nargs -1) in
            (* FIXME: Ces deux tests ne sont pas suffisants. *)
            if not (hi_is_ind && hi_args_enough) then raise_notrace Exit (* No indarg *)
            else (* Last arg is the indarg *)
              res := {!res with
                indarg = Some (List.hd !res.args);
                indarg_in_concl = occur_rel sigma 1 ccl;
                args = List.tl !res.args; nargs = !res.nargs - 1;
              };
            raise_notrace Exit);
    raise_notrace Exit(* exit anyway *)
  with Exit -> (* Ending by computing indref: *)
    match !res.indarg with
      | None -> !res (* No indref *)
      | Some (LocalDef _) -> error_ind_scheme ""
      | Some (LocalAssum (_,ind)) ->
          let indhd,indargs = decompose_app sigma ind in
          try {!res with indref = Some (fst (destRef sigma indhd)) }
          with DestKO ->
            error CannotFindInductiveArgument
