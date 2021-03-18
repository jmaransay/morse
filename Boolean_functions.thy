
theory Boolean_functions
  imports 
    Main
    "HOL-Analysis.Cartesian_Euclidean_Space"
    Finite_mod_type
begin

text\<open>Boolean functions\<close>

definition bool_fun_dim_n :: "nat => (bool^'n => bool) set"
  where "bool_fun_dim_n n = {f. CARD ('n) = n}"

text\<open>Definition of monotonicity\<close>

text\<open>Following Scoville, we remove the constant vector 1 from the definition of monotonicity,
  since otherwise its preimage by ceros_of_bool_input, the empty set, would be an element of the
  simplicial set.\<close>

definition monotone_bool_fun :: "(bool^'n => bool) => bool"
  where "monotone_bool_fun f = mono_on f (Set.remove (\<chi> i. True) UNIV)"

definition monotone_bool_fun_set :: "(bool^'n => bool) set"
  where "monotone_bool_fun_set = (Collect monotone_bool_fun)"

text\<open>Some examples of Boolean functions\<close>

definition bool_fun_top :: "bool^'n => bool"
  where "bool_fun_top f = True"

definition bool_fun_bot :: "bool^'n => bool"
  where "bool_fun_bot f = False"

text\<open>Threshold function, as defined by Scoville in Problem 6.5\<close>

(*definition count_true :: "bool^'n => nat"
  where "count_true v = (\<Sum> i \<in> UNIV. if v $ i then 1 else 0::nat)"*)

definition count_true :: "bool^'n => nat"
  where "count_true v = card {i. v $ i}"

lemma "count_true (\<chi> i. False) = 0"
  by (simp add: count_true_def)

lemma "count_true (\<chi> i::'a::CARD_1. True) = 1"
  unfolding count_true_def
  using Cardinality.CARD_1_class.CARD_1
  by (metis Collect_cong UNIV_def vec_lambda_beta)

lemma "count_true (\<chi> i::finite_mod_1. True) = 1"
  unfolding count_true_def
  unfolding Collect_code
  unfolding enum_finite_mod_1_def by simp

lemma "count_true (\<chi> i::finite_mod_2. True) = 2"
  unfolding count_true_def
  unfolding Collect_code
  unfolding enum_finite_mod_2_def by simp

lemma "count_true (\<chi> i::finite_mod_5. True) = 5"
  unfolding count_true_def
  unfolding Collect_code
  unfolding enum_finite_mod_5_def by simp

lemma "Collect (($) (vec_lambda (case_finite_mod_5 True False False False False))) = {finite_mod_5.a\<^sub>0}"
  unfolding Collect_code
  unfolding enum_finite_mod_5_def by simp

lemma "count_true (\<chi> i::finite_mod_5. case (i) of finite_mod_5.a\<^sub>0 \<Rightarrow> True | (_) \<Rightarrow> False) = 1"
  unfolding count_true_def 
  unfolding Collect_code
  unfolding enum_finite_mod_5_def by simp

lemma "count_true (\<chi> i::finite_mod_5. case (i) of finite_mod_5.a\<^sub>1 \<Rightarrow> True 
                                                | finite_mod_5.a\<^sub>2 \<Rightarrow> True 
                                                | (_) \<Rightarrow> False) = 2" 
  unfolding count_true_def 
  unfolding Collect_code
  unfolding enum_finite_mod_5_def by simp

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
  monotone_collect:
  assumes ulev: "(u::bool^'n) \<le> v"
  shows "Collect (($) u) \<subseteq> Collect (($) v)"
  using ulev
  unfolding less_eq_vec_def
  by auto

lemma
  monotone_count_true:
  assumes ulev: "(u::bool^'n) \<le> v"
  shows "count_true u \<le> count_true v"
  unfolding count_true_def
  using monotone_collect [OF ulev]
  by (simp add: card_mono)

lemma
  monotone_threshold:
  assumes ulev: "(u::bool^'n) \<le> v"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  unfolding bool_fun_threshold_def
  using monotone_count_true [OF ulev] by simp

text\<open>It seems that the previous result does not require any assumption in the
  natural number n defining the threshold, even if it seems sensible to introduce it,
  as in the result below\<close>

lemma
  assumes "(u::bool^'n) \<le> v"
  and "n < CARD ('n)"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  using monotone_threshold [OF assms(1), of n] .

text\<open>The threshold functions are monotone\<close>

lemma "monotone_bool_fun (bool_fun_threshold n)"
  by (meson mono_onI monotone_bool_fun_def monotone_threshold)

end