theory mutilated_actual
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
  assumes h1 : "\<forall> x \<in> s. \<forall> y \<in> s. x \<noteq> y \<longrightarrow> covers x \<inter> covers y = {}" and
          h1a : "finite s"
  shows "(\<Union> x \<in> s. covers x) \<noteq> mchessboard" 
proof
  have "bij_betw flip (chessboard \<inter> white) (chessboard \<inter> -white)"
  proof -
    have aux1: "\<forall> x. x \<in> chessboard \<longrightarrow> flip x \<in> chessboard"
      by (auto simp add: chessboard_def flip_def)
    have aux2: "\<forall> x \<in> chessboard. flip x \<in> white \<longleftrightarrow> x \<in> -white"
      by (auto simp add: chessboard_def flip_def white_def)
    have aux3: "inj_on flip (chessboard \<inter> white)"
      by (auto simp add: inj_on_def flip_def chessboard_def white_def)
    have aux4: "\<forall> x \<in> chessboard \<inter> -white. x \<in> flip ` (chessboard \<inter> white)"
    proof -
      have aux4a: "\<forall> x \<in> chessboard. flip (flip x) = x"
        by (auto simp add: flip_def chessboard_def)
      show ?thesis
        by (metis IntI Int_iff aux1 aux2 aux4a imageI)
    qed
    show ?thesis
      by (auto simp add: bij_betw_def aux1 aux2 aux3 aux4)
  qed
  hence h2: "card (chessboard \<inter> white) = card (chessboard \<inter> -white)"
    using bij_betw_same_card by blast
  have h2a: "(0, 0) \<in> chessboard \<inter> white" and h2b: "(7, 7) \<in> chessboard \<inter> white"
    by (simp add: chessboard_def white_def)+
  have h3: "card (mchessboard \<inter> white) < card (mchessboard \<inter> -white)"
  proof -
    have aux5: "mchessboard \<inter> white = chessboard \<inter> white - {(0, 0), (7, 7)}"
      by (auto simp add: mchessboard_def)
    have aux6: "mchessboard \<inter> -white = chessboard \<inter> -white"
      by (auto simp add: mchessboard_def chessboard_def white_def)
    have aux7: "(chessboard \<inter> white = mchessboard \<inter> white \<union> {(0, 0), (7, 7)}) \<and> 
                  (mchessboard \<inter> white) \<inter> {(0, 0), (7, 7)} = {}"
      using aux5 h2a h2b by auto
    have aux7a: "finite chessboard \<and> finite mchessboard"
      by (auto simp add: chessboard_def mchessboard_def)
    have aux7b: "(0, 0) \<notin> insert (7, 7) (mchessboard \<inter> white)"
      using h2a mchessboard_def by auto
    have aux7c: "(7, 7) \<notin> mchessboard \<inter> white"
      by (simp add: aux5)
    have aux7d: "card (insert (0, 0) (insert (7, 7) (mchessboard \<inter> white))) =
                   Suc (Suc (card (mchessboard \<inter> white)))"
      using aux7a aux7b aux7c by auto 
    have aux8: "card (chessboard \<inter> white) = card (mchessboard \<inter> white) + 2"
      using aux7 by (auto simp add: aux7d)
    show ?thesis
      by (auto simp add: aux5 aux6 aux8 h2 [symmetric])
  qed    
  have h9: "\<forall> x. card (covers x \<inter> white) = card (covers x \<inter> -white)"
  proof -
    have aux9a: "\<forall> a b. (a, b) \<in> white \<longleftrightarrow> (Suc a, b) \<notin> white"
      by (auto simp add: white_def)
    have aux9b: "\<forall> a b. {(a, b), (Suc a, b)} \<inter> white = {(a, b)} \<or> 
                        {(a, b), (Suc a, b)} \<inter> white = {(Suc a, b)}"
      by (metis Int_insert_left_if0 Int_insert_left_if1 aux9a inf_bot_right inf_commute)
    have aux9c: "\<forall> a b. (a, b) \<in> white \<longleftrightarrow> (a, Suc b) \<notin> white"
      by (auto simp add: white_def)
    have aux9d: "\<forall> a b. {(a, b), (a, Suc b)} \<inter> white = {(a, b)} \<or> 
                        {(a, b), (a, Suc b)} \<inter> white = {(a, Suc b)}"
      by (metis Int_insert_left_if1 Int_insert_right_if0 aux9c inf_bot_right inf_commute)
    have aux9e: "\<forall> x. card (covers x \<inter> white) = 1"
    proof
      fix x
      show "card (covers x \<inter> white) = 1"
        apply (induction x)
         apply auto
        using aux9b card_Suc_eq apply force
        using aux9d card_Suc_eq by force
    qed
    have aux9f: "\<forall> a b. {(a, b), (Suc a, b)} \<inter> - white = {(a, b)} \<or> 
                        {(a, b), (Suc a, b)} \<inter> - white = {(Suc a, b)}"
      by (metis Compl_disjoint Compl_iff Int_insert_left aux9a inf_commute inf_compl_bot_left1)
    have aux9g: "\<forall> a b. {(a, b), (a, Suc b)} \<inter> - white = {(a, b)} \<or> 
                        {(a, b), (a, Suc b)} \<inter> - white = {(a, Suc b)}"
      by (metis Compl_disjoint Compl_iff Int_insert_left_if0 Int_insert_left_if1 aux9c inf_right_idem)
    have aux9h: "\<forall> x. card (covers x \<inter> -white) = 1"
    proof
      fix x
      show "card (covers x \<inter> - white) = 1"
        apply (induction x)
        apply auto
        using aux9f card_Suc_eq apply force
        using aux9g card_Suc_eq by force        
    qed
    show ?thesis
      using aux9e aux9h by simp
  qed
  with h1 h1a have h4: "card ((\<Union> x \<in> s. covers x) \<inter> white) = card ((\<Union> x \<in> s. covers x) \<inter> -white)"
  proof -
    have aux10e: "\<forall> x. finite (covers x)"
    proof
      fix x
      show "finite (covers x)"
        apply (cases x)
        by auto
    qed
    have aux10f: "\<forall> x. finite (covers x \<inter> white)"
      using aux10e by auto
    have aux10g: "\<forall> x \<in> s. \<forall> y \<in> s. x \<noteq> y \<longrightarrow> (covers x \<inter> white) \<inter> (covers y \<inter> white) = {}"
      using h1 by auto
    have aux10h: "\<forall> x \<in> s. \<forall> y \<in> s. x \<noteq> y \<longrightarrow> (covers x \<inter> - white) \<inter> (covers y \<inter> - white) = {}"
      using h1 by auto
    have aux10a: "(\<Union> x \<in> s. covers x) \<inter> white = (\<Union> x \<in> s. covers x \<inter> white)"
      by simp
    have aux10b: "(\<Union> x \<in> s. covers x) \<inter> -white = (\<Union> x \<in> s. covers x \<inter> -white)"  
      by simp
    with h1a aux10e aux10g have aux10c: 
        "card ((\<Union> x \<in> s. covers x) \<inter> white) = (\<Sum> x \<in> s. card (covers x \<inter> white))"
     by (smt aux10a card_UN_disjoint finite_Int sum.cong)
    with h1 h1a aux10e aux10h have aux10d: 
        "card ((\<Union> x \<in> s. covers x) \<inter> - white) = (\<Sum> x \<in> s. card (covers x \<inter> - white))"
      by (smt aux10b card_UN_disjoint finite_Int sum.cong)
    show ?thesis
      by (simp add: aux10c aux10d h9)
  qed
  assume "(\<Union> x \<in> s. covers x) = mchessboard"
  with h3 h4 show False
    by auto
qed

end