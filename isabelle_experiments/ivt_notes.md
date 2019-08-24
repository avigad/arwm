Notes
-----

My third experiment involved proving the intermediate value theorem. This states that if a function `f` is continuous on a nonempty closed interval `[a, b]` with `f(a) < 0` and `f(b) > 0`, there is a point `y` in the interval with `f(y) = 0`. This is usually proved in libraries by showing more generally that for continuous functions between topological spaces, the image of a connected set is connected, and that in the reals, the connected sets are exactly the intervals (possibly open or unbounded at either end).

Instead, I chose to formalize directly the proof one would typically show undergraduates. Given the data above, let `y` be the sup of the set of elements `x` of `[a, b]` satisfying `f(x) < 0`. If `f(y) < 0`, then `y < b`, and by continuity one can find a point `y'` to the right of `y` satisfying `f(y) < 0`, contradicting the fact that `y` is the sup. If `f(y) > 0`, then `y > a`, and the argument is similar (but not symmetric). By continuity, there is a neighborhood around `y` where all elements `x` in `[a, b]` satisfy `f(x) > 0`. But since `y` is the least upper bound, there will be points `y'` arbitrarily close to `y` such that `f(y') < 0`, again a contradiction. Since `f(y)` is neither greater than nor less than zero, we have `f(y') = 0`.

For this proof, `auto`, `simp`, and `linarith` were extremely helpful. In particular, both contradictory cases involved messing around with inequalities involving epsilons and deltas and absolute values, and `linarith` was very helpful with those. In fact, after I wrote the original proof, I golfed it a few lines shorter by combining steps involving those three.

Sledgehammer was only mildly helpful. It did helpfully tell me that the smt tactic could prove
```
  from ‹y ∈ {a..b}› ‹f y < 0› ‹f b > 0› have "y < b"
```
where `{a..b}` is Isabelle's notation for the closed interval `[a, b]`. This falls just out of the range of linarith, because it involves a bit of equational reasoning to show that `y` is not equal to `b`. A couple of times when a goal could be solved by `linarith`, Sledgehammer found the relevant hypotheses for me so that I did not have to name them myself.

There are two places where Sledgehammer *could* have been more helpful, and the reasons it was not are informative. The first involved proving basic properties involving `Sup`, and the second involved unfolding the definition of continuity.

As an example of the first, after defining `y` to be the supremum of the elements `x` of `[a, b]` satisfying `f(x) < 0`, it is easy to see that `y` itself is an element of `[a, b]`. But Sledgehammer could not do this, probably due to the mild use of second-order reasoning required, and proving it by hand took some effort. I had to use the find command to find the relevant properties of `Sup`, and since it is defined more abstractly I needed to know that the instance for conditionally complete lattices was the relevant one. Applying the relevant lemmas manually told me the side conditions I needed; in particular, I needed that the sets in question are nonempty and bounded above. `auto` proves these easily, and it turned out that once these were added to the context, Sledgehammer *could* perform the inference. I used the Sledgehammer proof because it is shorter, but I kept the manual proof `ivt_original_beginning` at the bottom of the file, for reference.

The other place where I had hoped Sledgehammer would be more helpful was in unfolding the definition of continuity. Given `continuous_on {a..b} f`, `y ∈ {a..b}` and `- f y > 0`, I knew that we should have
```
∃ δ. δ > 0 ∧
  (∀ x. x ∈ {a..b} ∧ abs (x - y) < δ ⟶ abs (f x - f y) < - f y)
```
I wanted Sledgehammer to just give me that fact. But Isabelle's analysis library is developed at a higher level of generality and abstraction, and, in particular, designed to avoid the need for epsilon-delta reasoning where possible. It seems that the chain of definitions and unpacking lemmas that was needed was just too long. So I started unfolding things manually. That wasn't easy, and when I could not guess an unfolding lemma I had to resort to search. For example, the lemma that translates `dist x y` to `abs (x - y)` on the reals is called `dist_real_def`. Unfolding things also yielded notation like a long arrow for convergence or notation `∀⇩F xa in at x within {a..b}. ...` for an `eventually` predicate on filters, and I had to know or figure out that these represented `tendsto` and `eventually` to find the right lemmas. Once things were suitably unfolded, Sledgehammer could prove the result equivalent to what I had stated.
```
  apply (simp add: continuous_on_def tendsto_iff dist_real_def
    eventually_at)
  by (metis ‹0 < - f y› ‹y ∈ {a..b}› abs_zero atLeastAtMost_iff
    cancel_comm_monoid_add_class.diff_cancel)
```

The first failure of Sledgehammer underscored conclusions that I had already reached:

- More capacity for second-order reasoning would go a long way.

- It would have been great if Sledgehammer could tell me that easy facts like `a ∈ {a..b}` and `bdd_above {a..b}` might be helpful, because I could easily supply them.

- Even better, if would be great if Sledgehammer could interact with `auto` or some special-purpose tool to get these itself.

I don't know what to say about the second failure. Of course, Sledgehammer would have an easier time if something closer to the equivalence I wanted was already in the library. But the library was developed at the current level of abstraction precisely because there are too many variations, and stating them all would involve an explosion of definitions. Still, maybe it is possible to seed the library with common unwinding patterns, and, even better, have the relevance filter trained to add them when they might be helpful.