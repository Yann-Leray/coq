# What would the `induction` tactic do ?

## Tactic usage

```coq
induction expr, expr' in x, y, z as intropattern with (P := a) using elim_ind.
```
(+ `dependent`, `funelim`)

## Naming

Using the names above:
- `expr, expr'` are the discriminees (may have an inductive type in regular induction, are function applications in functional elimination)
- `x, y, z` are the generalised hypotheses (present in the context)
- `intropattern` is the intro pattern
- `elim_ind` is the induction principle or eliminator. Its type has a distinct shape that will be used to construct the induction

## Implementation

### Grouping the behaviour of induction and destruct

Since most of what the tactic does is the same between destruct and induction, we can do a first step to make sure that the same function can do the following steps in both cases.

The idea is that `elim_ind ?p1 .. ?pn ?P1 .. ?Pn ?H1 .. ?Hn ?i1 .. ?in ?t` behaves similarly to `match ?t as t in I _ _ i1 .. in return ?P@{?i1; ..; ?in} with C1 a1 .. an => ?H1 | .. | Cn a1 .. an => ?Hn end`

The pattern matching is pretty much the ending point we want to reach, so a situation where we have
- a main predicate `?P@{i1; ..; in} : Sort`
- `[the whole term] : ?P@{i1 := t1; .. in := tn}`, with main instance `t1; ..; tn`
- `?Hk@{a1; ..; an} : forall Γk, ?Pj@{i1 := iC1; .. in := iCn}` (called obligations or branches, we keep a mix of products and partially instantiated evars)
- other evars (including other predicates `?P1 .. ?Pn`)


For our eliminator, this means that we need to:
- apply it fully to evars (and instantiate with given bindings) [done through eclauses]
  + if we find products [Hipattern tuples] (as with combined schemes), we can project using the so-called main argument as a needed hint [instantiability test, any hole starting from the end]
- identify the main predicate (`?P`), all other predicates [types of the elim's other branches] and all obligations, among the created evars [holes]
  + the main predicate is `?P` from the return type of the eliminator `?P t1 .. tn` (needs to be of that shape)
    * instantiate `?P` as a lambda such that the return type becomes `?P@{t1; ..; tn}`
  + the obligations are the hypotheses which (1) return `?P@{u1; ..; un}`
  + the other predicates are the predicates from the other branches that could have been taken, other obligations similar [not sure if and how to use]
- Apply the `with_bindings`; potential conflict with definition of `?P` to be caught here
- If the discriminator(s) / main argument(s) (exists and) is given, instantiate it; potential conflict with `with_bindings` to be caught here

### Main part

Input: eliminator (see above), occurences matrix, in_list : list of (hyp or 'pat/constr as intro_var'), goal hyps and conclusion, is_dependent / eqn

- Check that the instance of `?P` in the eliminator return type has no remaining evars (only pre-existing as those stay allowed) [no evar from eliminator hole list]

- If dependent, prepend `refl : variable = instance element :> variable type` as `?e` in the in_list (no need for subterm matching)
- If eqn:e, prepend `refl : variable = argument :> variable type` as `e` in the in_list for the main argument(s ?) (no need for subterm matching)



- Iteratively, over the in_list and then the conclusion:
  + if `hyp`, then it shall be generalised and cleared from the regular context; no additional work to do since it's already the correct variable
  + If `pat/constr as intro_var` (this can include `H as H'` to not forget a hypothesis but still generalise)
    * if `pat`, we look for it in conclusion, listed hypotheses in reverse, remaining hypotheses in reverse until we find it (then do as for constr)
    * when `constr`, we add it to the "to-match" list

  + Recognise the different arguments in the instance of the main predicate (+ to-match list)
    * One occurence set per instance element
    * Still, whole instance every time
    * FO heuristic if no occurence set is given: if the type is `forall Γ, c args`, test args against *main* instance whole terms from the end until it fails
    * For the rest (or whole term if no heuristic), find subterm for each instance element  and replace with asociated variable (using occurence sets)
    * NB: The result is only well typed in the environment extended with local *defs*, not merely local abstractions (to be dealt with later)

  + Restoring typing: we are confronted to a problem where
    Γ, vars := inst ⊢ hyp : hyptype : □, i.e. Γ ⊢ hyp : hyptype[vars := inst] : □
    but we want Γ , vars : vartypes ⊢ hyp : hyptype' : □
    * if dependent, we repair hyptype by adding transports of the equalities generated in the inst (ETT to ITT style), as best as we can (no introducing funext or UIP)
    * if repair mode on, we repair by generalising the problematic subterms (and give a warning since this can and probably should be done explicitly ?)
    * if repair mode off, try to give a good error message, specific to the situation (shouldn't be too hard) (give a specific message for eqn hyp when applicable)


- Do the actual work:
  + Try clearing all hypotheses in the list, all variables which appear in the main instance
  + Instantiate `?P := forall ?Γ, ?Goal`
  + Append Γ to intro pattern for Hi
  + Instantiate `[whole term] @ Γ`

- Post:
  + Hook for generated equalities with dependent
  + Apply intropatterns
  + If evars disallowed, check whether all remaining evars are nondependent

## rest
elim_ind is an induction principle, with its uniform parameters, predicates, some branches for obligations, non-uniform parameters and the proved predicate.

- Identify and unify the induction discriminee inside the induction principle type; either as last product domain of the type (regular induction) or last argument of the final codomain (functional induction)
  This means the induction principle has shape (`∀ _ .. _, P x1 .. xn T`, case 2) or else (`∀ _ .. _, ∀ (x : T), P x1 .. xn`, case 1) where T is the location of the discriminee
  + in the unification, extract the list of non-uniform parameters:
    3 cases: (in induction principle vs in discriminee)
    * variable `x` vs variable `y`: normal case, rename `y` into `x`, regular procedure
    * variable `x` vs term: do a [`set (x := t) in [in_list, default *].`], then regular procedure with `x` (+ if dependent, add in [`x = t`] as hypothesis)
    * term vs term: if unifiable, then do as above for the found unification matches

  + if in case 2, do a [`set (fx := T) in [in_list, default *].`] and proceed as in case 1

- Generalize over all hypotheses whose types depend on `x1 .. xn (+ fx)`
- (Generalize over the dependent equalities)
- Generalize over all remaining hypotheses listed in the [`in_list`] (cannot erase hypothesis warning goes here)
- Invert the goal as a function of `x1 .. xn (+ fx)`
- (If given in the binding, unify the found proved predicate with the given value, don't bother accepting if they don't unify)
  We now have constructed the proved predicate, the instances of the non-uniform parameter arguments, and also some uniform parameters as extracted from the discriminee

- `refine elim_ind`, using the given uniform parameters, found predicate, non-uniform parameters, and with help from the given additional bindings

  There remains holes / goals, of two classes: goals which mention the proved predicate in the final codomain (proof obligations) and the others (proof parameters)

- All parameter goals are left as-is
- In the obligation branches (the other goals), introduce the variables until the proved predicate (using the names from the induction principle or from the `intropattern`, somewhat unfortunate that we can't have more custom name generation method here)
  then reintroduce the generalized variables with their original names (freshened), (then dependent equalities), then generalized hypotheses with their original names (freshened)

- Give back control to the user

Good: Almost no constraint on elim_ind type (only the final codomain is constrained)
Bad: Not the expected behavior for induction principles with >1 mutual predicate


Alternative with the expected behavior : enforce shape being `∀ p1 .. pn P1 .. Pn, B1 -> .. Bn -> ∀ pu1 .. pun, P x1 .. xn` (order of `pi, Pi, Bi, pui` wouldn't in fact matter); identify branches as nondependent and predicates as their final codomains. If no branches, only P is taken as predicate
Then, for all obligation branches, introduce the variables in the same way (requires that all predicates are as generalized as `P` which is annoying to do by hand)


Also, we could not require that the final codomain of `elim_ind` be [`P x1 .. xn (T)`] but allow [`P t1 .. tn (T)`]; the disambiguation between case 1 or 2 of discriminee location would become entirely external (`funind` vs `induction`), and we would do for all t [`set xi := ti in [in_list, default *].`], as is done with [`fx`] in `funind`.

Finally, I didn't include `eqn:` here, I assume it's straightforward enough (similar to dependent equalities but for the whole discriminee ?); I also didn't include occurrences, since I don't know where they fit exactly.
