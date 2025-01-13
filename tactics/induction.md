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

The idea is that `elim_ind ?p1 .. ?pn ?P1 .. ?Pn ?H1 .. ?Hn ?i1 .. ?in ?t` behaves similarly to `match ?t as t in I _ _ i1 .. in return ?P ?i1 .. ?in with C1 a1 .. an => ?H1 | .. | Cn a1 .. an => ?Hn end`

The pattern matching is the ending point we want to reach, so a situation where we have
- a main predicate `?P@{i1; ..; in} : Sort`
- `[the whole term] : ?P@{i1 := ?i1; .. in := ?in}` (might not all be pure evars, pattern recognition if not)
- `?Hk@{a1; ..; an} : ?Pj@{i1 := iC1; .. in := iCn}` (called obligations or branches)
- other evars (including other predicates `?P1 .. ?Pn`)
- (optional) a special evar `?t` (or many ?) for the discriminee / main argument


For our eliminator, this means that we need to:
- apply it fully to evars (and instantiate with given bindings)
  + if we find products (as with combined schemes), we can project using the inductive type as a needed hint
- identify the main predicate (`?P`), all other predicates and all obligations, among the created evars
  + the main predicate is `?P` if the return type of the eliminator is `?P i1 .. in` (needs to be of that shape, ik need not be variables)
  + the obligations are the hypotheses which (1) return `?P j1 .. jn` / (2) don't appear dependently in the type
  + the other predicates are (only with 2) the `?Pi` for all return types of the obligations with shapes `?Pi j1 .. jn` (need to be of that shape)
  + the special evar(s) are the last hypotheses if regular induction, the last argument(s) of the return type if functional induction
- for the main predicate, intros the indices / parameters
  + use the names in the return type of the eliminator if they are variables, create name otherwise
- (only if 2) for the other predicates, intros the indices / parameters (no given names !)
- for obligations, intros the hypotheses before the final goal (one of the predicates) -> using the intropattern


### Main part

- If given, unify the discriminee(s) with the discriminee evar(s) (be it inductive value or function application or anything)
- (unsure) Check that the instance of `?P` in the eliminator return type has no remaining evars
- Recognise the different arguments in the instance of the main predicate among the generalised hypotheses
  + In the hypotheses and the goal, we want to recognise each instance argument as a pattern and replace it with the associated variable in the named context of `?P`.
    This pattern recognition is done successively for each argument, in the given list of generalised hypotheses.

    There is a question to be had on how to direct this pattern recognition.

  + If the list of generalised hypotheses is not given and we are not `dependent`, infer it to be the list of all hypotheses where the above pattern recognition would find something

  + If `dependent`, we generalise over `refl : pack variable = pack instance arguments :> instance telescope`
    If the list of generalised hypotheses is not given, infer it to be [if induction, empty|if destruct, the instance arguments which are variables and everything that depends on it, but no pattern recognition]

  + If `eqn:H`, find the argument which corresponds to the discriminee (error if doesn't exist or if > 1) and generalise over `refl : variable = argument :> variable type`.
    If the discriminee is a variable, generalise as above [+ when destruct, warning "was generalised automatically as a variable"]
    Else if `variable type` depends on some part of the instance, error "cannot generalise"

    If the list of generalised hypotheses is not given, infer it to be the same as with `dependent`

  + (ONLY IF 2) Mirror somewhat this to all predicates (How ?)

- Do the actual generalisation:
    + Try clearing all generalised hypotheses, all variables which appear in the main argument and its indices (if any)
    + Instantiate `?P := forall ?Γ, ?Goal`
    + Instantiate `?Hi := fun (Γ : Γ) => ?Hi` (?? what do we do if 2)
    + Instantiate `[whole term] := [whole term] @ Γ`

- If `dependent`, hook(?) to do [injection, discrimination, noconfusion] on added equalities
- If evars disallowed, check whether all remaining evars are nondependent
- return


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
