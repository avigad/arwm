Notes
-----

I felt bad that my first experiment (with the mutilated chessboard problem) concluded with a mixed assessment of Sledgehammer. Larry Paulson gave me some points to keep in mind:

> One is that first you should always call auto. We always discourage this (on the grounds that the resulting proof might be fragile), but the alternative is too often no proof at all. The reason to call auto is first, to perform all obvious simplifications (sledgehammer is no good at this), and second, to split up a monolithic goal into multiple subgoals. The second point is really critical; it’s always worth the effort to separate out the separate statements that need to be proved. If the resulting proof is messy, you can always sort it out later.

> Another thing: if the problem involves variable binding, e.g. through a summation or integral, then try to get rid of this. Sledgehammer can prove only the simplest statements involving bound variables.

I had reached the first conclusion on my own, and begun to suspect the second.

I decided that the way of setting up the first experiment, namely, writing out a template and then trying to fill it in rigidly, is somewhat unfair. The whole point to the *interactive* part of interactive theorem proving is that we can use feedback to guide our effort. Moreover, as Jasmin Blanchette pointed out to me, we should not expect to use Sledgehammer on its own. Isabelle has good tools for structuring proofs, and a very good `find` command for finding theorems, and so the challenge is to figure out how to use all the tools effectively.

So, this time around, I decided to be less dogmatic in proving that there are infinitely many primes congruent to three modulo four. Rather than making up a template first, I wrote and adjusted the lemmas while proving the theorem. I also relied more on Isabelle documentation and the `find` command as I went.

I chose this theorem for reasons of nostalgia: I proved this many years ago when learning to use Isabelle. The proof is a slight variation of Euclid's proof of that there are infinitely many primes. The key lemma is that if the product of two numbers is congruent to 3 mod 4, then one of the factors must be congruent to 3 mod 4, a fact that is easily proved by ruling out the other cases. From that, it follows that if we factor any number `n` congruent to 3 mod 4 into primes, then at least one of the prime factors is congruent to 3 mod 4. There are two ways to implement this argument: either make use of the factorization of `n` into primes explicitly, or do a direct induction on `n`. I chose to do the latter.

Remarkably, Sledgehammer proved `aux1`, the key lemma, right away using CVC4. In the file, I also include a more explicit proof. Here Sledgehammer helpfully proved the first three goals. When I wrote that proof, surprisingly, using `find` with pattern `(_ mod ?k) * (_ mod ?k)` did not help me find the lemma I needed for the third goal, so I was happy that Sledgehammer did.

For the second lemma, `aux2`, I needed to use total induction. It requires some expertise to figure out how to do that in Isabelle, but fortunately Google found a pattern for me to follow here: [https://isabelle.in.tum.de/Isar/Isar-induct.pdf](https://isabelle.in.tum.de/Isar/Isar-induct.pdf). (Search on "complete induction.") The mixture of object level arrows and quantifiers on the one hand and metalevel arrows and quantifiers on the other is a bit clunky, but following the template blindly worked pretty well.

I thought I would need a lemma `(n ::nat) mod 4 = 3 ⟶ n ≥ 2`, but Sledgehammer pointed out to me again that `linarith` gets it immediately, so I could inline those proofs when needed. In the case where `n` is not prime, to use the inductive hypothesis, I need to write `n = m * k` for `n` and `k` a product of smaller numbers. Happily, Sledgehammer let me do this as well, using the `E` theorem prover with the fact `n ≥ 2`. The other provers failed at this task however. Earlier I had added the requirements `m ≥ 2` and `k ≥ 2`, and Sledgehammer failed there as well, so I was lucky that my later formulation did not require those.

The very good news is that Sledgehammer supplied every single justification in the proof of the main theorem, except for one. The exception is the proof that `?u mod 4 = 3`; only CVC4 returns a proof, but the `smt` tactic could not reconstruct it. But in this case it was easy to convey the proof I had in mind by carrying out the substitution by hand and then calling `auto`.

Overall, in this case my experience using Sledgehammer was rather pleasant. Even though I had to do some mucking around to get things to work, Sledgehammer definitely saved time, and that felt good.