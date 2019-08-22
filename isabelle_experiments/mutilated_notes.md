Overview
--------

Suppose we are given a set of dominos such that each domino covers two adjacent squares on ordinary 8 x 8 chessboard. Remove two opposite corners. The *mutilated chessboard* problem asks whether it is possible to cover the remaining squares with dominos. The answer is no: the two squares that have been removed have the same color, and every domino covers one black square and one white square.

The files [mutilated_ideal.thy](mutilated_ideal.thy) and [mutilated_ideal.pdf](mutilated_ideal.pdf) contain an Isar outline of the proof, at the level one would write a careful and detailed informal proof. If automation could fill in every `sorry`, we could declare victory. Students learning to do mathematics can be taught to write proofs at that level of detail. At the other end of the spectrum, a mathematician who comes up with a subtle argument and wants confirmation that it is correct could be expected to write it down in that fashion. My goal was then to use fill out the templates using automation and take detailed notes along the way, to get a sense of how far we are from that ideal.

The rules I set for myself are as follows. I wanted to prove the theorem only by adding intermediate statements and relying on Isabelle's basic automation, `auto`, `simp`, and Sledgehammer. I allowed myself to browse theory files online to figure out how to *state* things, e.g. to discover that `bij_betw f s t` says that `f` is a bijection between sets `s` and `t`. Of course, knowing basic notation and identifiers like this were necessary even to write down the original proof sketch. But I wanted to avoid looking for particular theorems or using other tactics. I have been away from Isabelle for a while, and the details of the library, the proof language, and the tactics are not fresh in my mind. So I did not really have to pretend to be a user who wanted to avoid dealing with those details.

Here is some more background: `auto` and `simp` represent internal automation, and Sledgehammer calls battery of external provers and then uses the results to construct a proof. I used the default: resolution provers E, Spass, and Vampire, and SMT solvers CVC4 and Z3. I made use of Isar's mechanisms to manage the context. Intermediate statements can be labeled, phrases like `from ... have`, `hence`, and `with` control which previous statements appear in the local goal. (Keywords `hence` and `with` are syntactic sugar for `from this have` and `from this ... have`, where `this` refers to the previous goal.) Additionally, one can tell `auto` and `simp` to use additional facts with expressions like `auto simp add: ....` or `auto add: ...`. The first adds the fact for use by the simplifier, and the second adds it to the tableau search. The keyword `using` before `auto` or `simp` simply adds the facts to the hypotheses in the goal.

The files [mutilated_actual.thy](mutilated_actual.thy) and [mutilated_actual.pdf](mutilated_actual.pdf) are the proofs that I came up with. They are not meant to be pretty. The tendency among formalizers upon completing a proof like this is to clean it up and shorten it to leave only a record of what *should* have been done. Instead, I tried to leave an accurate record of what I actually *did*, to better measure the level of difficulty. I even left the senseless numbering scheme for auxiliary hypotheses. Whenever I needed a label, I made one up, without concern for uniformity or structure.

What follows is a detailed play-by-play account of my mucking around. My hope is to provide developers with information as to what an ordinary user might do, and what the pain points are.

Notes
-----

Starting with the template in [mutilated_ideal.thy](mutilated_ideal.thy), I tried Sledgehammer on the first main statement of the template proof:
```
  bij_betw flip (chessboard ∩ white) (chessboard ∩ -white)
```
It was no help. Calling `auto` with simplifier rules to unfold all definitions in sight made progress, though. Looking at the remaining goals gave some hints as to what the problem was. I then decided to call `auto` and unfold only the main definitions. This enabled me to extract `aux1` to `aux4` as auxiliary statements and confirm that `auto` succeeds with these.

Curiously, Sledgehammer didn't help at all with `aux1` to `aux3`, but `auto` and `simp` did fine. In fact, my first two attempts to state `aux4` were wrong -- they proved the goal, but were not themselves provable -- but once again, mucking around with `auto` and seeing what remained made it clear what I had done wrong. I had expected `aux4` to be harder for the automation, because proving surjectivity -- i.e. that something is in the image of a function -- requires instantiating an extra quantifier. This explains why the hint `aux4a` was needed. Happily, with that hint, Sledgehammer did succeed on `aux4`. In fact, all the provers returned proofs.

Once I had `aux1` to `aux4`, I tried Sledgehammer on the first goal again. Only CVC4 succeeded and told me to use this:
```
  by (smt Compl_iff IntD1 IntD2 IntI aux1 aux2 aux3 aux4 bij_betwI' imageE inj_onD)
```
But when I inserted this line in the file Isabelle gave me an error message telling me that Z3 had timed out. So I stuck with `auto`.

The second main statement of the template proof is this:
```
  card (chessboard ∩ white) = card (chessboard ∩ -white)
```
Here, Sledgehammer was great. All five provers told me right away that `bij_betw_same_card` would solve it using the previous fact.

Sledgehammer didn't get the next two claims in the template:
```
  (0, 0) ∈ chessboard ∩ white
  (7, 7) ∈ chessboard ∩ white
```
but `simp` did easily.

The next claim was more disappointing:
```
  card (mchessboard ∩ white) < card (mchessboard ∩ -white)
```
I had hoped that, with the previous facts and the definition of `mchessboard`, the result would be in reach. But Sledgehammer just failed, and what you see is me flailing around desperately trying to come up with enough intermediate facts for the automation to help. Here I had some unfair advantages over a naive user: from my past experience with Isabelle, I knew that theorems about cardinality often require knowing that the relevant sets are finite and I had a pretty good sense of what an explicit formal proof would look like. But even with these advantages, Sledgehammer was very little help, and trying to guess facts to throw at the system was like stumbling around in the dark. It would have been much easier to succumb, look up the particular theorems, and resort to manual inference. I am sure there is a more efficient proof using the automation, but what appears in the file is the first one I found.

The next claim was this:
```
  ∀ x. card (covers x ∩ white) = card (covers x ∩ -white)
```
Sledgehammer failed on the original claim (and `auto` and `simp` did not help either), so I started by reducing the problem to these:
```
  ∀ x. card (covers x ∩ white) = 1
  ∀ x. card (covers x ∩ -white) = 1
```
Again, automation did nothing helpful here. I helped it out by splitting on cases (either `x` is a horizontal domino or a vertical one). This enabled `auto` to make some progress, but it still got stuck, and Sledgehammer didn't help. I decided to help automation out by claiming these:
```
  ∀ a b. {(a, b), (Suc a, b)} ∩ white = {(a, b)} ∨
         {(a, b), (Suc a, b)} ∩ white = {(Suc a, b)}

  ∀ a b. {(a, b), (a, Suc b)} ∩ white = {(a, b)} ∨
         {(a, b), (a, Suc b)} ∩ white = {(a, Suc b)}
```
I also stated the versions with `white` replaced by `-white`. With this hint, Sledgehammer could prove `∀ x. card (covers x ∩ white) = 1`. Four of the five provers told me to use Isabelle's internal resolution theorem prover, `metis`, but one determined that Isabelle's `force` tactic, a tableau prover, could also do it.

There remained the task of proving the hints. Sledgehammer still needed help. For the ones above, it was sufficient to add these facts:
```
  ∀ a b. (a, b) ∈ white ⟷ (Suc a, b) ∉ white
  ∀ a b. (a, b) ∈ white ⟷ (a, Suc b) ∉ white
```
The simplifier could prove these easily. It was actually a big help that Sledgehammer could finish off the proof using these, since a manual proof would have been tedious.

The last substantial claim in the template proof is this:
```
  card ((⋃ x ∈ s. covers x) ∩ white) = card ((⋃ x ∈ s. covers x) ∩ -white)
```
Again, Sledgehammer didn't succeed, so I started to spell out the proof. It was easy to reduce the proof to the following fact and the corresponding claim for `-white`:
```
  card ((⋃ x ∈ s. covers x) ∩ white) = (∑ x ∈ s. card (covers x ∩ white))
```
At this point, I realized that my original statement of the theorem did not include the assumption that `s` is finite. In fact, because Isabelle assigns 0 to the `card` of an infinite set, the theorem was provable as stated, but not really what was intended. So I added the assumption. With this hypothesis, the claim is almost immediate: modulo distributing the intersection into the union, this is just an identity for a finite union of disjoint finite sets. But none of Sledgehammer, `auto`, or `simp` could do it. For Sledgehammer, the problem may be that it is a higher-order inference: it involves instantiating a summation rule to the particular expression in the body of the sum. For `auto` and `simp`, another problem is that the simplifier factors the predicate `white` *out* of the union, rather than distributing it in. I tried to help Sledgehammer by throwing more hypotheses into the mix:
```
  ∀ x. finite (covers x)
  ∀ x. finite (covers x ∩ white)
  ∀ x ∈ s. ∀ y ∈ s. x ≠ y ⟶ (covers x ∩ white) ∩ (covers y ∩ white) = {}
  (⋃ x ∈ s. covers x) ∩ white = (⋃ x ∈ s. covers x ∩ white)
```
With all of these, Sledgehammer succeeded, but just barely: only CVC4 got it. As a reality check, I confirmed that the following three-line manual proof would have worked:
```
  apply (simp only: aux10a)
  apply (rule card_UN_disjoint)
  by auto
```
These lines use the simplifier to push `white` into the union, apply the identity, and dispel the subgoals. It was much harder to coax Sledgehammer to do it instead, especially because that involved guessing the hypotheses rather than generating them by applying the rule. In any case, once Sledgehammer succeeded, it was easy to go back and prove the hypotheses, and the proof was done.

Additional Notes
----------------

It was nice using Isabelle again. Both the main system and the jEdit interface are impressive. And Isabelle is incredibly easy to install: just download, unpack, and run. Sledgehammer and all the automated reasoning tools are bundled with it.

It took me a while to figure out how to use tab completion. It would have been helpful to have an out-of-the box tutorial to jEdit to tell me things like that. The functionality of jEdit is good, and the symbols panel and easy access to Isabelle documentation is helpful. My biggest gripe is that tab completion is annoyingly sluggish. And, in contrast to VSCode, the look-and-feel makes jEdit feel dated in a way that Emacs, for example, does not. In particular, the icons and controls hark back to the early days of GUIs.

Here is one glitch. By default, the jEdit panel calls CVC4, Z3, Spass, E, and Vampire, but it is configured to call Vampire remotely. The call to `remote_vampire` did not work, but changing it to `vampire` did. It seems that Isabelle now ships with a local copy. I had to set a flag somewhere to indicate that I am using Vampire for noncommercial use, but the system told me to do that.

Calls to Sledgehammer invariably involve spending a lot of time waiting for the system to return. The jEdit interface allows you work on other things while a Sledgehammer call is being processed, but I found it hard to multitask in this way. When I was focused on a particular goal, I wanted to stay focused on that goal, not drop it and come back to it.

I had recently proved the same theorem in Lean, and used the type `zmod 8 × zmod 8` for the chessboard. This is a natural thing to do, but it involved mucking around with theorems specific to the type `zmod 8`, which was a pain in the neck. It was nicer just dealing with `nat × nat` and treating the chessboard as a subset. The moral is that types are sometimes helpful and sometimes a hindrance, and there is wisdom in being able to tell the difference.

Assessment
----------

For comparison, I recently formalized mutilated chessboard problem in Lean, relying only on the simplifier. (The formalization is available here: http://www.andrew.cmu.edu/user/avigad/Papers/mutilated.pdf.) Searching for low-level facts and chaining them together in precise ways is also tedious, and it would be nice to avoid that. But the use of Sledgehammer in this example did not make the task less onerous.

I think I got unluck with this one. Larry Paulson gave me some points to keep in mind:

> One is that first you should always call auto. We always discourage this (on the grounds that the resulting proof might be fragile), but the alternative is too often no proof at all. The reason to call auto is first, to perform all obvious simplifications (sledgehammer is no good at this), and second, to split up a monolithic goal into multiple subgoals. The second point is really critical; it’s always worth the effort to separate out the separate statements that need to be proved. If the resulting proof is messy, you can always sort it out later.

> Another thing: if the problem involves variable binding, e.g. through a summation or integral, then try to get rid of this. Sledgehammer can prove only the simplest statements involving bound variables.

I had reached the first conclusion on my own, and begun to suspect the second. At least some of my struggles can be attributed to that.

Moreover, I have decided that the way of setting up this experiment, namely, writing out a template and then trying to fill it in rigidly, is somewhat unfair. The whole point to the *interactive* part of interactive theorem proving is that we can use feedback to guide our effort. Moreover, as Jasmin Blanchette pointed out to me, we should not expect to use Sledgehammer on its own. Isabelle has good tools for structuring proofs, and a very good `find` command for finding theorems, and so the challenge is to figure out how to use all the tools effectively. The files [mutilated.thy](mutilated.thy) and [mutilated.pdf](mutilated.pdf) are a cleaned up version of the proof, that reflects a more holistic approach: `auto` and `simp` are used where they are useful, some things are done by hand (like splitting on cases and rewriting the cardinality of a disjoint union as a sum), and Sledgehammer is called selectively. The places were Sledgehammer was successful, it certainly saved time. 

Nonetheless, the difficulties I had point to one of the main problem with the use of Sledgehammer, namely, that it is an all-or-nothing affair: when it fails, users have no recourse except to guess at the reasons that it failed and blindly throw extra information at it. As Jasmin Blanchette has pointed out to me, it would be helpful if Sledgehammer could report near misses to the user. For example, unit clauses or short clauses at the point of failure suggest hypotheses that are sufficient to prove the goal. But, as Jasmin points out, the nature of superposition calculi is that the search may get stuck on a clause that could otherwise be shortened, thereby failing to identify the real sticking points. And I don't know whether this method could be used to suggest candidate equations as well.

The tools `auto` and `simp` do much better in this respect, since they do whatever they can and leave the resulting goals for the user to inspect. Squinting at complicated goals is not fun, but it often makes it clear what has gone wrong and what additional information is needed. It seems to me that the main problem with these tools is that they work best when the search space is limited, that is, basically when the solution boils down to doing the obvious things. When they work, they work extremely well, but when a goal requires a bit of creativity -- picking a term instantiation, or relating one concept to another in a manner that amounts to more than unpacking a definition -- the tools fall short.
