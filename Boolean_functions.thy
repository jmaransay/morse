
theory Boolean_functions
  imports 
    Main
    "HOL-Analysis.Cartesian_Euclidean_Space"
    Enum_mod
begin

(*definition monotone :: "'a set => 'a set set => bool"
  where "monotone u P = (\<forall>s. subset s u \<longrightarrow> s \<in> P)"

definition simplicial_complex :: "nat => nat set set set"
  where "simplicial_complex n = {s. s \<subseteq> Pow {..n} \<and> (\<forall>(u::nat set)\<in>s. monotone u s)}"

definition simplex :: "nat => nat set set"
  where "simplex n = {s. subset s {..n}}"

lemma "monotone {..n} (Pow {..n})"
  by (simp add: Scratch.monotone_def psubset_imp_subset)

lemma "monotone {1,2} {{},{1},{2},{1,2}}"
  unfolding Scratch.monotone_def by auto

lemma "{} \<in> simplex 0"
  unfolding simplex_def by auto

lemma "{1,2} \<in> (simplex 9)"
  unfolding simplex_def by auto

lemma "{{},{1},{2},{1,2}} \<in> (simplicial_complex 2)"
  unfolding simplicial_complex_def simplex_def Scratch.monotone_def by auto

lemma "{{},{1},{2},{3},{1,2}} \<in> (simplicial_complex 3)" 
  unfolding simplicial_complex_def simplex_def Scratch.monotone_def by auto

lemma "{{},{1},{2},{3},{1,2},{2,3}} \<in> (simplicial_complex 3)" 
  unfolding simplicial_complex_def simplex_def Scratch.monotone_def by auto*)

text\<open>Boolean functions\<close>

term "A::bool^'n"

term "f :: bool^'n => bool"

definition bool_fun_dim_n :: "nat => (bool^'n => bool) set"
  where "bool_fun_dim_n n = {f. CARD ('n) = n}"

term "mono_on"

text\<open>Definition of monotonicity\<close>

definition monotone_bool_fun :: "(bool^'n => bool) => bool"
  where "monotone_bool_fun f = mono_on f UNIV"

text\<open>Some examples of Boolean functions\<close>

definition bool_fun_top :: "bool^'n => bool"
  where "bool_fun_top f = True"

definition bool_fun_bot :: "bool^'n => bool"
  where "bool_fun_bot f = False"

text\<open>Threshold function, as defined by Scoville in Problem 6.5\<close>

definition count_true :: "bool^'n => nat"
  where "count_true v = (\<Sum> i \<in> UNIV. if v $ i then 1 else 0::nat)"

lemma "count_true (\<chi> i. False) = 0"
  by (simp add: count_true_def)

lemma "count_true (\<chi> i::'a::CARD_1. True) = 1"
  unfolding count_true_def
  using Cardinality.CARD_1_class.CARD_1 by auto

lemma "count_true (\<chi> i::finite_mod_1. True) = 1"
  unfolding count_true_def UNIV_finite_mod_1 by simp

lemma "count_true (\<chi> i::finite_mod_2. True) = 2"
  unfolding count_true_def UNIV_finite_mod_2 by simp

lemma "count_true (\<chi> i::finite_mod_5. True) = 5"
  unfolding count_true_def UNIV_finite_mod_5 by simp

lemma "count_true (\<chi> i::finite_mod_5. case (i) of finite_mod_5.a\<^sub>1 \<Rightarrow> True | (_) \<Rightarrow> False) = 1"
  unfolding count_true_def UNIV_finite_mod_5 by simp

lemma "count_true (\<chi> i::finite_mod_5. case (i) of finite_mod_5.a\<^sub>1 \<Rightarrow> True 
                                                | finite_mod_5.a\<^sub>2 \<Rightarrow> True 
                                                | (_) \<Rightarrow> False) = 2"
  unfolding count_true_def UNIV_finite_mod_5 by simp

definition bool_fun_threshold :: "nat => (bool^'n => bool)"
  where "bool_fun_threshold i = (\<lambda>v. if i \<le> count_true v then True else False)"

text\<open>definition bool_fun_threshold_dim_n :: "(bool^'n => bool) set"
  where "bool_fun_threshold_dim_n = {f. bool_fun_threshold i }"\<close>

lemma "monotone_bool_fun bool_fun_top"
  by (simp add: bool_fun_top_def mono_onI monotone_bool_fun_def)

lemma "monotone_bool_fun bool_fun_bot"
  by (simp add: bool_fun_bot_def mono_onI monotone_bool_fun_def)

text\<open>The Isar proof of the following result has been produced by Isabelle automatically:\<close>

lemma
  monotone_threshold:
  assumes "(u::bool^'n) \<le> v"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
proof -
  have f1: "\<forall>n f v va. (\<not> (n::nat) \<le> f (v::(bool, 'n) vec) \<or> \<not> v \<le> va \<or> (\<exists>v va. v \<le> va \<and> \<not> f v \<le> f va)) \<or> n \<le> f va"
    by fastforce
  obtain vv :: "((bool, 'n) vec \<Rightarrow> nat) \<Rightarrow> (bool, 'n) vec" 
    and vva :: "((bool, 'n) vec \<Rightarrow> nat) \<Rightarrow> (bool, 'n) vec" 
    where
    "\<forall>x2. (\<exists>v4 v5. v4 \<le> v5 \<and> \<not> x2 v4 \<le> x2 v5) = (vv x2 \<le> vva x2 \<and> \<not> x2 (vv x2) \<le> x2 (vva x2))"
    by moura
  then have f2: "\<forall>n f v va. \<not> n \<le> f v \<or> \<not> v \<le> va \<or> vv f \<le> vva f \<and> \<not> f (vv f) \<le> f (vva f) \<or> n \<le> f va"
    using f1 by presburger
  obtain nn :: "('n \<Rightarrow> nat) \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> 'n set \<Rightarrow> 'n" where
    f3: "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> \<not> x1 v3 \<le> x0 v3) = (nn x0 x1 x2 \<in> x2 \<and> \<not> x1 (nn x0 x1 x2) \<le> x0 (nn x0 x1 x2))"
    by moura
    { assume "vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV \<le> vva count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV"
      moreover
      { assume "(vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV \<le> vva count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV) \<noteq> (bool_fun_threshold n u \<le> bool_fun_threshold n v)"
        moreover
        { assume "\<not> vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV"
          then have "(if vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1::nat else 0) = 0"
          by presburger
        then have "(if vva count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1::nat else 0) = 1 \<and> (if vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1::nat else 0) = 1 \<or> nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV \<notin> UNIV \<or> (if vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1::nat else 0) \<le> (if vva count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1 else 0)"
          by linarith }
        moreover
        { assume "nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV \<notin> UNIV \<or> (if vv count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1::nat else 0) \<le> (if vva count_true $ nn (\<lambda>n. if vva count_true $ n then 1 else 0) (\<lambda>n. if vv count_true $ n then 1 else 0) UNIV then 1 else 0)"
          then have "(\<Sum>n\<in>UNIV. if vv count_true $ n then 1::nat else 0) \<le> (\<Sum>n\<in>UNIV. if vva count_true $ n then 1 else 0)"
            using f3 by (meson sum_mono)
        then have "\<not> vv count_true \<le> vva count_true \<or> count_true (vv count_true) \<le> count_true (vva count_true)"
          by (metis count_true_def)
        then have "n \<le> count_true u \<longrightarrow> n \<le> count_true v"
          using f2 assms by blast }
      ultimately have "n \<le> count_true u \<longrightarrow> (\<not> bool_fun_threshold n u \<or> bool_fun_threshold n v) \<or> (\<not> bool_fun_threshold n u \<or> bool_fun_threshold n v) \<or> n \<le> count_true v"
        by fastforce }
    ultimately have "n \<le> count_true u \<longrightarrow> (\<not> bool_fun_threshold n u \<or> bool_fun_threshold n v) \<or> (\<not> bool_fun_threshold n u \<or> bool_fun_threshold n v) \<or> n \<le> count_true v \<or> bool_fun_threshold n u \<le> bool_fun_threshold n v"
      by linarith }
  then have "bool_fun_threshold n u \<le> bool_fun_threshold n v \<or> \<not> bool_fun_threshold n u \<or> bool_fun_threshold n v"
    using f2 by (meson assms bool_fun_threshold_def less_eq_vec_def)
  then show ?thesis
    by force
qed

text\<open>It seems that the previous result does not require any assumption in the
  natural number n defining the threshold, even if it seems sensible to introduce it,
  as in the result below\<close>

lemma
  assumes "(u::bool^'n) \<le> v"
  and "n < CARD ('n)"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  using assms unfolding less_eq_vec_def less_vec_def vec_eq_iff bool_fun_threshold_def count_true_def  
  by (smt le_boolI le_less_trans nat_le_linear not_less not_one_le_zero sum_mono)

text\<open>The threshold functions are monotone\<close>

lemma "monotone_bool_fun (bool_fun_threshold n)"
  by (meson mono_onI monotone_bool_fun_def monotone_threshold)

end