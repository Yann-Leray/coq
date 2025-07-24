(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Context
open EConstr
open Vars
open Declarations
open Reductionops
open Tacred
open Evarutil
open Locus



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










type elim_scheme = {
  elimc: constr;
  elimt: types; (* [?P@{a1 .. an} t1 .. tn] *)

  main_pred : Evar.t; (* ?P *)
  main_inst : (variable * constr) list; (* a1 .. an t1 .. tn, but no section variable *)
  other_preds : Evar.t list;

  main_branches : EClause.hole list; (* Type is ∀Γ, ?P u1 .. un *)
  other_branches : EClause.hole list; (* Type is ∀Δ, ?Q v1 .. vp *)
  other_holes : EClause.hole list;

  all_holes : EClause.hole list;

}


let eliminator_of_constr env sigma ?(discr=[]) (elimc, with_bindings) =

  let elimt = Retyping.get_type_of env sigma elimc in

  let rec get_ccls sigma elimc elimt =
    let sigma, cl = EClause.make_evar_clause env sigma elimt in
    let elimc = mkApp (elimc, Array.map_of_list (fun hole -> hole.EClause.hole_evar) cl.cl_holes) in
    let ccl_head, ccl_args = decompose_app sigma cl.cl_concl in
    match EConstr.kind sigma ccl_head with
    | Evar ev ->
      let sigma, ev = Evardefine.evar_absorb_arguments env sigma ev (Array.to_list ccl_args) in
      let inst = Evarutil.make_evar_instance sigma ev in
      [sigma, cl.cl_holes, (elimc, elimt, fst ev, inst)]
    | _ ->
      if Hipattern.is_tuple env sigma cl.cl_concl then
        let sigma, projtys = make_projections env sigma elimc in
        let ccls = List.map_append (fun (elimc, elimt) -> get_ccls sigma elimc elimt) projtys in
        let ccls = List.map (fun (sigma, holes, evkinst) -> (sigma, cl.cl_holes @ holes, evkinst)) ccls in
        ccls
      else failwith "Not an inductive scheme, ccl doesn't start with a bound variable"
  in
  let ccls = get_ccls sigma elimc elimt in

  let sigma, elimc, elimt, holes, main_pred, main_inst, other_preds =
    match ccls, List.nth_opt discr 0 with
    | [sigma, holes, (elimc, elimt, evk, inst)], _ ->
      sigma, elimc, elimt, holes, evk, inst, []
    | [], _ -> assert false
    | _, None -> failwith "More than one branch, cannot decide"
    | ccls, Some decider ->
      let _, j = EClause.find_progress_evar_clause env ccls decider in
      let ccls, (sigma, holes, (elimc, elimt, evk, inst)) = List.extract_nth j ccls in
      sigma, elimc, elimt, holes, evk, inst, List.map (fun (_, _, (_, _, evk, _)) -> evk) ccls
  in

  let clause = EClause.{ cl_holes = holes; cl_concl = elimt } in
  let sigma = EClause.solve_evar_clause env sigma true clause with_bindings in
  let sigma = List.fold_right (fun c sigma -> EClause.progress_evar_clause env sigma clause c) discr sigma in

  let test_head_evar sigma evks c =
    let _, ty = decompose_prod_decls sigma c in
    let head, _ = decompose_app sigma ty in
    match EConstr.kind sigma head with Evar (evk, _) -> Evar.Set.mem evk evks | _ -> false
  in
  let main_branches, other_holes = List.partition (fun hole -> test_head_evar sigma (Evar.Set.singleton main_pred) hole.EClause.hole_type) holes in
  let other_branches, other_holes = List.partition (fun hole -> test_head_evar sigma (Evar.Set.of_list other_preds) hole.EClause.hole_type) other_holes in

  sigma, { elimc; elimt = Retyping.get_type_of env sigma elimc; main_inst; main_pred; other_preds; main_branches; other_branches; other_holes; all_holes = holes }




let replace_term env sigma occs (var, arg) ty =
  let test, out =
    let test = Find_subterm.make_eq_univs_test env sigma arg in
    test, fun () -> test.testing_state
  in
  let ty = Find_subterm.replace_term_occ_modulo env sigma occs test (fun () -> mkVar var) ty in
  out(), ty


let match_with_pred env sigma occs inst ty =
  List.fold_right2 (fun inst_elt occs (sigma, ty) -> replace_term env sigma occs inst_elt ty) (List.rev inst) (List.rev occs) (sigma, ty)


let match_with_pred env sigma ?occs inst ty =
  let fo_heuristic = true in
  let occs' = match occs with Some occs -> occs | None -> List.make (List.length inst) (AtOccs AllOccurrences) in

  if not fo_heuristic || Option.has_some occs then
    match_with_pred env sigma occs' inst ty
  else
    let sign, cod = decompose_prod_decls sigma ty in
    let head, args = decompose_app sigma cod in
    let test c = (Find_subterm.make_eq_univs_test env sigma c).match_fun 0 in

    let rec on_args sigma inst_pre args =
      match inst_pre, args with
      | [], _ | _,  [] ->
          let ty = mkApp (head, Array.rev_of_list args) in
          match_with_pred env sigma occs' inst ty
      | (v, c) :: inst_pre, (arg :: args as all_args) ->
          match test c sigma arg with
          | Ok sigma ->
            let sigma, ty = on_args sigma inst_pre args in
            sigma, mkApp (ty, [|mkVar v|])
          | Error () ->
            let ty = mkApp (head, Array.rev_of_list all_args) in
            match_with_pred env sigma occs' inst ty
    in
    let sigma, cod = on_args sigma (List.rev inst) (Array.rev_to_list args) in
    let sigma, sign =
      let sigmaref = ref sigma in
      let sign = Context.Rel.map (fun c -> let (sigma, c) = match_with_pred env !sigmaref occs' inst c in sigmaref := sigma; c) sign in
      !sigmaref, sign
    in
    sigma, it_mkProd_or_LetIn cod sign


type inhyps =
  | InList of variable list
  | AllMatchingBut of Id.Set.t


let trunk env sigma elim inhyps hyps ccl =
  let inst = elim.main_inst in
  let all_hole_evars = elim.all_holes |> List.to_seq |> Seq.filter_map EClause.(fun h -> if h.hole_deps then Some h.hole_evar_key else None) |> Evar.Set.of_seq in
  if List.exists (fun (_, c) -> not @@ Evar.Set.disjoint (undefined_evars_of_term sigma c) all_hole_evars) inst then
    assert false;

  let hyps = match inhyps with
    | AllMatchingBut l -> List.filter (fun decl -> not @@ Id.Set.mem (Context.Named.Declaration.get_id decl) l) hyps
    | InList l -> List.map (fun var -> Context.Named.lookup var hyps) l
  in

  let sigma, ccl' = match_with_pred env sigma inst ccl in
  let sigma, hyps' =
    let sigmaref = ref sigma in
    let sign = Context.Named.map (fun c -> let (sigma, c) = match_with_pred env !sigmaref inst c in sigmaref := sigma; c) hyps in
    !sigmaref, sign
  in

  let hyps' =
    match inhyps with InList _ -> hyps' | AllMatchingBut _ ->
    let vars = Id.Set.of_list @@ List.map fst inst in
    let _, hyps' =
      Context.Named.fold_inside ~init:(vars, [])
        (fun (vars, r) decl ->
          let id = Context.Named.Declaration.get_id decl in
          if not (Id.Set.mem id vars) && Termops.occur_vars_in_decl env sigma vars decl then
            Id.Set.add id vars, decl :: r
          else
            vars, r)
        hyps'
    in
    List.rev hyps'
  in

  (* generalize_list can contain some inst patterns to match (become hypotheses instead of in the inst proper) *)
  (* retypecheck and somehow generalize over erroneous subterms *)

  let env' = Evd.evar_filtered_env (Global.env ()) (Evd.find_undefined sigma elim.main_pred) in

  let sigma, hyps' =
    let sigma = Context.Named.fold_inside ~init:sigma
      (fun sigma -> function
        | LocalAssum (na, ty) ->
            let sigma, _ = Typing.sort_of env' sigma ty in
            sigma
        | LocalDef (na, b, ty) ->
            let sigma, _ = Typing.sort_of env' sigma ty in
            let sigma = Typing.check env' sigma b ty in
            sigma)
      hyps
    in
    sigma, hyps'
  in
  let sigma, ccl' =
    let sigma, _ = Typing.sort_of env' sigma ccl' in
    sigma, ccl'
  in


  (* if dependent, generalize over eq *)
  (* if eqn, generalize over eq *)


  (* Instantiate, refine, hook *)

  let pred_value = it_mkNamedProd_or_LetIn sigma ccl' hyps' in
  let sigma = Evd.define elim.main_pred pred_value sigma in

  sigma, mkApp (elim.elimc, Context.Named.instance mkVar hyps')




let destVar_opt sigma c = match destVar sigma c with v -> Some v | exception Constr.DestKO -> None


let warn_cannot_remove_as_expected =
  CWarnings.create ~name:"cannot-remove-as-expected2" ~category:CWarnings.CoreCategories.tactics
         Pp.(fun (id,inglobal) ->
           let pp = match inglobal with
             | None -> mt ()
             | Some ref -> str ", it is used implicitly in " ++ Printer.pr_global ref in
           str "Cannot remove " ++ Id.print id ++ pp ++ str ".")

let clear_for_destruct ids =
  Proofview.tclORELSE
    (Tactics.Internal.clear_gen (fun env sigma id err inglobal -> raise (ClearDependencyError (id,err,inglobal))) ids)
    (function
     | ClearDependencyError (id,err,inglobal),_ -> warn_cannot_remove_as_expected (id,inglobal); Proofview.tclUNIT ()
     | e -> Exninfo.iraise e)

(* Either unfold and clear if defined or simply clear if not a definition *)
let expand_hyp id =
  let open Proofview.Notations in
  Tacticals.tclTRY (Tactics.unfold_body id) <*> clear_for_destruct [id]


let guard_no_unifiable =
  let open Proofview.Notations in
  Proofview.guard_no_unifiable >>= function
  | None -> Proofview.tclUNIT ()
  | Some l ->
    Proofview.tclENV     >>= function env ->
    Proofview.tclEVARMAP >>= function sigma ->
    let info = Exninfo.reify () in
    Proofview.tclZERO ~info Logic.(RefinerError (env, sigma, UnresolvedBindings l))


let induction_tac ~with_evars ~inhyps lc elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let hyps = Proofview.Goal.hyps gl in
  let ccl = Proofview.Goal.concl gl in
  let state = Proofview.Goal.state gl in

  let sigma, elim = match elim with
  | Some elim -> sigma, elim
  | None ->
    let constr = match lc with constr :: _ -> constr | [] -> CErrors.user_err Pp.(str"cannot guess eliminator with no argument") in
    let ty = Retyping.get_type_of env sigma constr in
    let (ind, _), _ = find_hnf_rectype env sigma ty in
    let s = Tacticals.elimination_sort_of_goal gl in
    let gr = Indrec.lookup_eliminator env ind s in
    let sigma, elimc = Evd.fresh_global env sigma gr in
    sigma, (elimc, Tactypes.NoBindings)
  in

  let sigma, elim = eliminator_of_constr env sigma ~discr:lc elim in

  let inhyps = match inhyps with
    | InList _ -> inhyps
    | AllMatchingBut set ->
      let set = List.fold_right Id.Set.add (List.filter_map (destVar_opt sigma) lc) set in
      AllMatchingBut set
  in

  let sigma, res = trunk env sigma elim inhyps hyps ccl in

  let goal = Proofview.Goal.goal gl in
  let sigma = Evd.define goal res sigma in

  let future_goals, sigma = Evd.pop_future_goals sigma in
  let gls = List.rev (Evd.FutureGoals.comb future_goals) in
  let sigma = Evd.push_future_goals sigma in

  Tacticals.tclTHENLIST [
    Proofview.Unsafe.tclEVARS sigma;
    Proofview.Unsafe.tclNEWGOALS (CList.map (fun evk -> Proofview.goal_with_state evk state) gls);
    Tacticals.tclTHENLIST (List.filter_map (fun c -> destVar_opt sigma c |> Option.map expand_hyp) (List.map snd elim.main_inst @ lc));
    Tactics.reduce_after_refine;
    if with_evars then Proofview.shelve_unifiable else guard_no_unifiable
  ]
  end
