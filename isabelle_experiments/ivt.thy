theory ivt

imports Complex_Main

begin

theorem ivt:
  fixes f :: "real \<Rightarrow> real" and a b :: real
  assumes ctsf: "continuous_on {a..b} f" 
      and "a < b" and fa1: "f a < 0" and fa2: "f b > 0"
  shows "\<exists> x \<in> {a..b}. f x = 0"
proof -
  have "a \<in> {a..b}" using assms by auto
  have [simp]: "a \<in> {x. x \<in> {a..b} \<and> f x < 0}" using assms by auto
  have "bdd_above {a..b}" by auto
  have "bdd_above {x. x \<in> {a..b} \<and> f x < 0}" by auto
  define y where "y = Sup {x. x \<in> {a..b} \<and> f x < 0}"
  have "y \<in> {a..b}"
    by (smt \<open>a \<in> {x \<in> {a..b}. f x < 0}\<close> \<open>bdd_above {a..b}\<close> 
          \<open>bdd_above {x \<in> {a..b}. f x < 0}\<close> atLeastAtMost_iff 
          cSup_atLeastAtMost cSup_mono empty_iff mem_Collect_eq y_def)
  have "\<not> f y < 0"
  proof
    assume "f y < 0"
    hence "- f y > 0" by linarith
    with ctsf have "\<exists> \<delta>. \<delta> > 0 \<and> 
        (\<forall> x. x \<in> {a..b} \<and> abs (x - y) < \<delta> \<longrightarrow> abs (f x - f y) < - f y)"
      apply (simp add: continuous_on_def tendsto_iff dist_real_def 
              eventually_at)
      by (metis \<open>0 < - f y\<close> \<open>y \<in> {a..b}\<close> abs_zero atLeastAtMost_iff 
            cancel_comm_monoid_add_class.diff_cancel)
    then obtain \<delta> where "\<delta> > 0" and 
        h: "\<And>x. x \<in> {a..b} \<Longrightarrow> abs (x - y) < \<delta> \<Longrightarrow> abs (f x - f y) < - f y"
      by auto
    let ?\<delta>' = "min (\<delta> / 2) (b - y)"
    let ?y' = "y + ?\<delta>'"
    from \<open>y \<in> {a..b}\<close> \<open>f y < 0\<close> \<open>f b > 0\<close> have "y < b"
      by (smt atLeastAtMost_iff)
    with \<open>\<delta> > 0\<close> have "?y' > y" by linarith
    from \<open>y \<in> {a..b}\<close> \<open>\<delta> > 0\<close> have "?y' \<in> {a..b}" and "abs (?y' - y) < \<delta>" 
      by auto
    hence "abs (f ?y' - f y) < - f y" by (auto intro: h)
    with \<open>- f y > 0\<close> have "f ?y' < 0" by auto
    with \<open>?y' \<in> {a..b}\<close> have "y \<ge> ?y'"
      by - (subst (3) y_def, rule cSup_upper, auto)      
    thus False
      using \<open>0 < \<delta>\<close> \<open>y < b\<close> by linarith
  qed
  moreover have "\<not> f y > 0"
  proof
    assume "f y > 0"
    with ctsf have "\<exists> \<delta>. \<delta> > 0 \<and> 
        (\<forall> x. x \<in> {a..b} \<and> abs (x - y) < \<delta> \<longrightarrow> abs (f x - f y) < f y)"
      apply (simp add: continuous_on_def tendsto_iff dist_real_def 
              eventually_at)
      by (metis \<open>0 < f y\<close> \<open>y \<in> {a..b}\<close> abs_zero atLeastAtMost_iff 
            cancel_comm_monoid_add_class.diff_cancel)
    then obtain \<delta> where "\<delta> > 0" and 
        h: "\<And>x. x \<in> {a..b} \<Longrightarrow> abs (x - y) < \<delta> \<Longrightarrow> abs (f x - f y) < f y"
      by auto
    from \<open>y \<in> {a..b}\<close> \<open>f y > 0\<close> \<open>f a < 0\<close> have "y > a"
      by (smt atLeastAtMost_iff)
    let ?\<delta>' = "min (\<delta> / 2) (y - a)"
    let ?y' = "y - ?\<delta>'"
    from \<open>0 < \<delta>\<close> \<open>a < y\<close> \<open>a \<in> {x. x \<in> {a..b} \<and> f x < 0}\<close> 
        have "\<exists> y'' \<in> {x. x \<in> {a..b} \<and> f x < 0}. ?y' < y''"
      by (subst y_def, subst less_cSup_iff [symmetric], auto)
    then obtain y'' where "y'' > ?y'" 
           and hy'': "y'' \<in> {x. x \<in> {a..b} \<and> f x < 0}" by auto
    hence "y'' \<le> y"
      by (metis \<open>bdd_above {x \<in> {a..b}. f x < 0}\<close> cSup_upper y_def)
    with \<open>y'' > ?y'\<close> \<open>y \<in> {a..b}\<close> \<open>\<delta> > 0\<close> hy'' have "abs (f y'' - f y) < f y"
      by (auto intro: h)
    hence "f y'' > 0" by auto
    with hy'' show False by auto
  qed
  ultimately have "f y = 0" by linarith
  with \<open>y \<in> {a..b}\<close> show ?thesis by blast
qed

theorem ivt_original_beginning:
  fixes f :: "real \<Rightarrow> real" and a b :: real
  assumes ctsf: "continuous_on {a..b} f" 
      and "a < b" and fa1: "f a < 0" and fa2: "f b > 0"
  shows "True"
proof -
  define y where "y = Sup {x. x \<in> {a..b} \<and> f x < 0}"
  have "y \<in> {a..b}"
  proof -
    have "y \<le> Sup {a..b}"
      apply (subst y_def)
      apply (rule cSup_mono)
      using assms apply auto
      apply (rule_tac x = "a" in exI)
      by auto
    hence "y \<le> b" using \<open>a < b\<close> by auto
    moreover have "a \<le> y"
      apply (auto simp add: y_def)
      apply (rule cSup_upper)
      using assms by auto
    ultimately show ?thesis by auto
  qed
  show ?thesis by auto
qed

end

(* Notes
To state the theorem, need to remember {a..b}, and find notation Sup in file.

The problem is that the library is deep. 

Sledgehammer didn't get y \<in> {a..b} or even y \<le> b, so I added y \<le> Sup {a..b}.

Golfed down -- automation

Arithmetic -- auto, smt, and linarith

Two places where sledgehammer might have helped: figuring out how to go from continuity to the
property I knew it had, and little properties of suprema. (In generality. Side conditions, set
not empty, bounded above.)
*)
