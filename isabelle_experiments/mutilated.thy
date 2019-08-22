theory mutilated
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
  assumes "finite s" and "\<forall> x \<in> s. \<forall> y \<in> s. x \<noteq> y \<longrightarrow> covers x \<inter> covers y = {}"
  shows "(\<Union> x \<in> s. covers x) \<noteq> mchessboard" 
proof
  have h1: "finite chessboard" by (auto simp add: chessboard_def)
  have "bij_betw flip (chessboard \<inter> white) (chessboard \<inter> -white)"
  proof -
    have aux1: "\<forall> x. x \<in> chessboard \<longrightarrow> flip x \<in> chessboard"
      by (auto simp add: chessboard_def flip_def)
    have aux2: "\<forall> x \<in> chessboard. flip x \<in> white \<longleftrightarrow> x \<in> -white"
      by (auto simp add: chessboard_def flip_def white_def)
    have aux3: "inj_on flip (chessboard \<inter> white)"
      by (auto simp add: inj_on_def flip_def chessboard_def white_def)
    have aux4: "\<forall> x \<in> chessboard. flip (flip x) = x"
      by (auto simp add: flip_def chessboard_def)
    have aux5: "\<forall> x \<in> chessboard \<inter> -white. x \<in> flip ` (chessboard \<inter> white)"
      by (metis IntI Int_iff aux1 aux2 aux4 imageI)
    show ?thesis
      by (auto simp add: bij_betw_def aux1 aux2 aux3 aux4 aux5)
  qed
  hence h2: "card (chessboard \<inter> white) = card (chessboard \<inter> -white)"
    using bij_betw_same_card by blast
  have "card (mchessboard \<inter> white) < card (mchessboard \<inter> -white)"
  proof -
    have "(7, 7) \<in> chessboard \<inter> white"
      by (simp add: chessboard_def white_def)
    moreover have "mchessboard \<inter> white = chessboard \<inter> white - {(0, 0), (7, 7)}"
      by (auto simp add: mchessboard_def white_def)
    moreover have "mchessboard \<inter> -white = chessboard \<inter> -white"
      by (auto simp add: mchessboard_def white_def)
    ultimately show ?thesis
      by (metis Diff_insert Diff_insert0 card_Diff1_less card_Diff2_less finite_Int h1 h2)
  qed
  moreover have "card ((\<Union> x \<in> s. covers x) \<inter> white) = card ((\<Union> x \<in> s. covers x) \<inter> -white)"
  proof -
    have aux6: "\<forall> x. finite (covers x)"
    proof fix x show "finite (covers x)" by (cases x, auto) qed
    have "\<forall> x. card (covers x \<inter> white) = card (covers x \<inter> -white)"
    proof 
      fix x 
      show "card (covers x \<inter> white) = card (covers x \<inter> -white)"
        by (induction x, auto simp add: Int_insert_left white_def)
    qed
    with assms aux6 show ?thesis 
      by (subst UN_simps(4) [symmetric], subst card_UN_disjoint, auto)+
  qed
  moreover assume "(\<Union> x \<in> s. covers x) = mchessboard"
  ultimately show False by auto
qed

end