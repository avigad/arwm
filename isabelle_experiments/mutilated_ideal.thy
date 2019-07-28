theory mutilated_ideal
imports "Main"

begin 

definition chessboard :: "(nat \<times> nat) set" where 
  "chessboard = {..7} \<times> {..7}"

definition mchessboard :: "(nat \<times> nat) set" where
  "mchessboard = chessboard - {(0, 0), (7, 7)}"

datatype domino = 
  horizontal "nat \<times> nat" 
| vertical   "nat \<times> nat"

fun covers :: "domino \<Rightarrow> (nat \<times> nat) set" where
  "covers (horizontal (i, j)) = {(i, j), (i+1, j)}"
| "covers (vertical (i, j)) = {(i, j), (i, j+1)}"

definition white :: "(nat \<times> nat) set" where
  "white = {p. even (fst p + snd p)}"

definition flip :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat)" where
  "flip p = (7 - fst p, snd p)"

theorem mutilated_chessboard:
  fixes s :: "domino set"
  assumes h1: "\<forall> x \<in> s. \<forall> y \<in> s. x \<noteq> y \<longrightarrow> covers x \<inter> covers y = {}" and
          h1a: "finite s"
  shows "(\<Union> x \<in> s. covers x) \<noteq> mchessboard" 
proof
  have "bij_betw flip (chessboard \<inter> white) (chessboard \<inter> -white)"
    sorry
  hence h2: "card (chessboard \<inter> white) = card (chessboard \<inter> -white)"
    sorry
  have "(0, 0) \<in> chessboard \<inter> white" and "(7, 7) \<in> chessboard \<inter> white"
    sorry
  with h2 have h3: "card (mchessboard \<inter> white) < card (mchessboard \<inter> -white)"
    sorry
  have "\<forall> x. card (covers x \<inter> white) = card (covers x \<inter> -white)"
    sorry
  with h1 have h4: "card ((\<Union> x \<in> s. covers x) \<inter> white) = card ((\<Union> x \<in> s. covers x) \<inter> -white)"
    sorry
  assume "(\<Union> x \<in> s. covers x) = mchessboard"
  with h3 h4 show False
    sorry
qed

end