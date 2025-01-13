There is not enough sharing between all functionalities required during typechecking of a case or elaboration of a case

Also, many go through lambdas because of the old representation of case, but no longer need this

# Summary of all functionalities

## What typing needs to check
[`match c as x in ind {pms} indices return P with C constructargs => br end`]
- discriminee `c` has type `ct` (regular typing)
- `pms` and `case_invert`:
  + Both `pms` and `case_invert` have types such that `ind pms iv` is well-typed
    * With the arity of `ind` being `forall paramslet, forall indiceslet, Sort s`,
      construct and typecheck `Γ ⊢ pmssubst : paramslet` and typecheck `Γ ⊢ pmssubst+ivsubst : paramslet + indiceslet`

      ⇒`subst_of_rel_instance Δ u inst` and `type_of_parameters env Δ u inst insttys`
  + They correspond to those of `ct` :
    `find_rectype ct = ind' pms' indices'` and `ind = ind'`, `pms' ≤ pms`, `indices' ≤ iv` (in Γ)

- Return predicate: `P` has type `Sort s` (for some s) in context `pctx = [indiceslet x]`
  + Construct `pctx`:
    * From previous info (check relevances):
      `return_context specif u pms pmssubst nas` (`= instantiate_context u pmssubst nas indiceslet ,, vass na (ind pms 0 .. n)`)
    * From no info (no check):
      `return_context ind u pms nas`
    * From no info, no names:
      `return_context ind u pms` (`= instantiate_context u pmssubst indiceslet ,, vass na (ind pms 0 .. n)`)

- Branches: `br` has type `P@{indicesC, C pms 0 .. n}` in context `brctx = [constructargslet]`
  + Construct `brctx`:
    * From previous info (check relevances):
      `branch_context specif i u pmssubst nas` (`= instantiate_context u pmssubst nas constructargslet`)
    * From no info (no check):
      `branch_context ind u i pms nas`
    * From no info, no names:
      `branch_context ind u i pms` (`= instantiate_context u pmssubst constructargslet`)
  + Construct this type:
    * From previous info:
      `branch_type specif i u P pms`
        ```ocaml
        let indices = get_indices specif ind i in
        let instance = map (esubst u (↑^#|brctx| pmssubst)) indices @ [C@{u} (↑^#|brctx| pms) 0 .. n]
        let indicessubst = subst_of_rel_instance pctx instance in
        esubst indicessubst P
        ```

    * From no info:
      `branch_type ind u i P pms`
