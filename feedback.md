In addition to the feedback that can be found in the original notes, issue #1, and the notes on the Isabelle experiments, here are some additional comments I have received from others that are worth recording.

Larry Paulson pointed out that I should have made it clear in the notes that Sledgehammer uses resolution theorem provers and SMT solvers to prove theorems.

Manuel Eberl finds these things useful:

- algebraic transformations (rearranging, cancelling terms)
- Gröbner basis methods (e.g. for systems of equalities in a ring)
- linear arithmetic and (occasionally) Presburger arithmetic
- occasionally Isabelle's connection to Z3 (via the "smt" method), but that's very specialised
- his own limit automation tactic (although it still has a long way to go)

He would find useful:

- more and better automation for algebraic transformations, equations, inequalities, cross-multiplying fractions etc. Especially in connection with special functions (exp, log, roots, powers with real exponents, etc.)

Johan Commelin observes that when it comes to formalization, we may care about different features:

- brevity
- readability
- ease of discovery/development
- maintainability
- speed of compilation and verification

and maybe more. These features are at odds with one another. Informal mathematicians are used to tradeoffs between brevity and readability. But maintainability and speed of compilation and verification are something new, specific to formal proofs.

Larry Paulson sent me a workaround for Sledgehammer's weakness with binders: suppose that you know
```
        P (integral S f)
```
and you want to show
```
        P (integral S g)
```
Sledgehammer may fail to prove f=g even if it’s quite easy, but there’s nothing to stop you from simply writing
```
        have "!!x. x : S ==> f x = g x"
```
when it might then work.

Inspired by Isabelle's `simp`, a couple of years ago Johannes Hölzl wrote a nice [wiki post](https://github.com/leanprover/lean/wiki/Simplifier-Features) detailing a number of features that could benefit Lean's simplifier.

Patrick Massot's wish list (for Lean in particular) is as follows:

- elaboration that works, including coercions, especially to functions, and type class resolution
- calculations where I only give the intermediate steps I would write on paper, using `ring`, `abel` and their non-existent extensions to other algebraic structures, and non-linear `linarith`
- packing/unpacking stuff

The last refers to theorems that basically move information around and therefore have no real mathematical content, like this:
```
example {α : Type*} [has_sub α] (S T : set $ set α) :
 (∀ {V : set α}, V ∈ S → (∃ (t : set α) (H : t ∈ T), set.prod t t ⊆ (λ (x : α × α), x.2 - x.1) ⁻¹' V)) ↔
    ∀ (U : set α), U ∈ S → (∃ (M : set α) (H : M ∈ T), ∀ (x y : α), x ∈ M → y ∈ M → y - x ∈ U) := sorry
```
