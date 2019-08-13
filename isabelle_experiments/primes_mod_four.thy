theory primes_mod_four
imports "Main"
        "HOL-Computational_Algebra.Primes"
begin 

lemma aux1: 
  fixes m k :: "nat"
  assumes "(m * k) mod 4 = 3"
  shows "m mod 4 = 3 \<or> k mod 4 = 3"
  by (smt One_nat_def add_Suc_right assms mod_double_modulus mod_mod_trivial 
       mod_mult_right_eq mult.right_neutral mult_0_right mult_2_right 
       not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_3_eq_3 
       numeral_Bit0 one_add_one zero_le zero_less_Suc zero_neq_numeral)

\<comment> \<open>an alternative proof\<close> 
lemma aux1': 
  fixes m k :: "nat"
  assumes "(m * k) mod 4 = 3"
  shows "m mod 4 = 3 \<or> k mod 4 = 3"
proof (rule ccontr)
  assume "\<not> (m mod 4 = 3 \<or> k mod 4 = 3)"
  moreover have "m mod 4 = 0 \<or> m mod 4 = 1 \<or> m mod 4 = 2 \<or> m mod 4 = 3"
    by linarith
  moreover have "k mod 4 = 0 \<or> k mod 4 = 1 \<or> k mod 4 = 2 \<or> k mod 4 = 3"
    by linarith
  moreover have "(m * k) mod 4 = ((m mod 4) * (k mod 4)) mod 4"
    by (simp add: mod_mult_eq)
  ultimately show False
    using \<open>(m * k) mod 4 = 3\<close> by auto
qed

lemma aux2:
  fixes n :: "nat"
  shows "n mod 4 = 3 \<longrightarrow> (\<exists> p. prime p \<and> p dvd n \<and> p mod 4 = 3)"
proof (induct n rule: less_induct)
  case (less n)
  then have IH: "\<And> m. m < n \<Longrightarrow> m mod 4 = 3 \<longrightarrow> 
                    (\<exists> p. prime p \<and> p dvd m \<and> p mod 4 = 3)" by simp
  show "n mod 4 = 3 \<longrightarrow> (\<exists> p. prime p \<and> p dvd n \<and> p mod 4 = 3)" 
  proof (clarify)
    assume h: "n mod 4 = 3"
    show "(\<exists> p. prime p \<and> p dvd n \<and> p mod 4 = 3)"
    proof cases
      assume "prime n"
      with h show ?thesis by auto
    next
      assume "\<not> prime n"
      moreover from h have "n \<ge> 2" by linarith
      ultimately obtain m k where "m < n" and "k < n" and "n = m * k"
        by (metis Suc_1 dvd_def dvd_imp_le le_neq_implies_less 
              less_le_trans mult.commute mult.right_neutral 
              nat_mult_eq_cancel_disj prime_nat_naiveI zero_less_Suc)       
      have "m mod 4 = 3 \<or> k mod 4 = 3"
        using \<open>n = m * k\<close> aux1 h by blast
      show "\<exists>p. prime p \<and> p dvd n \<and> p mod 4 = 3"
        using IH \<open>k < n\<close> \<open>m < n\<close> \<open>m mod 4 = 3 \<or> k mod 4 = 3\<close> \<open>n = m * k\<close>
              prime_dvd_mult_eq_nat by blast
    qed
  qed
qed

theorem infinite_primes_three_mod_four: "infinite {p :: nat. prime p \<and> p mod 4 = 3}"
proof
  let ?S = "{p :: nat. prime p \<and> p mod 4 = 3}"
  assume fS: "finite ?S"
  let ?u = "4 * (\<Prod> x \<in> ?S. x) - 1"
  have h1: "(\<Prod> x \<in> ?S. x) \<ge> 1"
    by (metis (no_types, lifting) mem_Collect_eq prime_ge_1_nat prod_ge_1)
  hence h2: "(\<Prod> x \<in> ?S. x) = (\<Prod> x \<in> ?S. x) - 1 + 1"
    by linarith 
  have "?u mod 4 = 3"
    by (subst h2) (simp add: ring_distribs)
  then obtain p where "prime p" and "p dvd ?u" and "p mod 4 = 3"
    using aux2 by blast
  have "p \<notin> ?S"
  proof
    assume "p \<in> ?S"
    hence "p dvd 4 * (\<Prod> x \<in> ?S. x)"
      by (simp add: dvd_prod_eqI fS)
    with \<open>p dvd ?u\<close> have "p dvd 1"
      by (metis (no_types, lifting) dvd_diffD1 h1 less_one 
          mult_eq_0_iff not_le zero_neq_numeral)
    thus False
      using \<open>prime p\<close> not_prime_unit by blast
  qed
  moreover with \<open>prime p\<close> \<open>p mod 4 = 3\<close> have "p \<in> ?S" by auto
  ultimately show False by simp
qed

end