
theory Boolean_functions
  imports 
    Main
    "Jordan_Normal_Form.Matrix"
    Finite_mod_type
begin

text\<open>Boolean functions\<close>

text\<open>Definition of monotonicity\<close>

locale boolean_functions
  = fixes n::"nat"
begin

definition bool_fun_dim_n :: "(bool vec => bool) set"
  where "bool_fun_dim_n = {f. f \<in> carrier_vec n \<rightarrow> (UNIV::bool set)}"

text\<open>Ideally, we would like to restrict ourselves to the functions
  over vectors of length n, so that we could later prove that those functions
  are isomorphic to the simplicial complex of dimension n, but I did not
 find a suitable way to encode such assumption in this locale.

Therefore, the assumption of taking just the vectors of length n 
  will be later made explicit in the proof of the isomorphism.\<close>

definition monotone_bool_fun :: "(bool vec => bool) => bool"
  where "monotone_bool_fun f \<equiv> (mono_on f (carrier_vec n))"

definition monotone_bool_fun_set :: "(bool vec => bool) set"
  where "monotone_bool_fun_set = (Collect monotone_bool_fun)"

text\<open>Some examples of Boolean functions\<close>

definition bool_fun_top :: "bool vec => bool"
  where "bool_fun_top f = True"

definition bool_fun_bot :: "bool vec => bool"
  where "bool_fun_bot f = False"

end

text\<open>Threshold function, as defined by Scoville in Problem 6.5\<close>

definition count_true :: "bool vec => nat"
  where "count_true v = sum (\<lambda>i. if vec_index v i then 1 else 0::nat) {0..<dim_vec v}"

(*definition count_true :: "bool Matrix.vec => nat"
  where "count_true v = (\<Sum>i \<in> {0..<dim_vec v}. if vec_index v i then 1 else 0::nat)"
*)

lemma "vec_index (vec (5::nat) (\<lambda>i. False)) 2 = False"
  by simp

lemma "vec_index (vec (5::nat) (\<lambda>i. True)) 3 = True"
  by simp

lemma "count_true (vec (1::nat) (\<lambda>i. True)) = 1"
  unfolding count_true_def by simp
  
lemma "count_true (vec (2::nat) (\<lambda>i. True)) = 2"
  unfolding count_true_def by simp

lemma "count_true (vec (5::nat) (\<lambda>i. True)) = 5"
  unfolding count_true_def by simp

(*lemma "Collect ((vec_nth) (vec_lambda (case_finite_mod_5 True False False False False))) = {finite_mod_5.a\<^sub>0}"
  unfolding Collect_code
  unfolding enum_finite_mod_5_def by simp*)

(*lemma "count_true (Matrix.vec (5::nat) (\<lambda>i. if i = 3 then True else False)) = 1"
  unfolding count_true_def apply simp try apply auto
*)

(*lemma "count_true (\<chi> i::finite_mod_5. case (i) of finite_mod_5.a\<^sub>1 \<Rightarrow> True
                                                | finite_mod_5.a\<^sub>2 \<Rightarrow> True 
                                                | (_) \<Rightarrow> False) = 2" 
  unfolding count_true_def 
  unfolding Collect_code
  unfolding enum_finite_mod_5_def by simp
*)

definition bool_fun_threshold :: "nat => (bool vec => bool)"
  where "bool_fun_threshold i = (\<lambda>v. if i \<le> count_true v then True else False)"

(*definition bool_fun_threshold_dim_n :: "(bool^'n => bool) set"
  where "bool_fun_threshold_dim_n = {f. bool_fun_threshold i }"*)

context boolean_functions
begin

lemma "mono_on bool_fun_top UNIV"
  by (simp add: bool_fun_top_def mono_onI monotone_bool_fun_def)

lemma "monotone_bool_fun bool_fun_top"
  by (simp add: bool_fun_top_def mono_onI monotone_bool_fun_def)

lemma "mono_on bool_fun_bot UNIV"
  by (simp add: bool_fun_bot_def mono_onI monotone_bool_fun_def)

lemma "monotone_bool_fun bool_fun_bot"
  by (simp add: bool_fun_bot_def mono_onI monotone_bool_fun_def)

text\<open>The Isar proof of the following result has been produced by Isabelle automatically:\<close>

(*lemma
  monotone_collect:
  assumes ulev: "(u::bool Matrix.vec) \<le> v"
  shows "Collect (vec_index u) \<subseteq> Collect (vec_index v)"
  using ulev 
  unfolding Matrix.less_eq_vec_def
  try
  unfolding less_eq_vec_def
  by auto*)

lemma
  monotone_count_true:
  assumes ulev: "(u::bool vec) \<le> v"
  shows "count_true u \<le> count_true v"
  unfolding count_true_def
  using Groups_Big.ordered_comm_monoid_add_class.sum_mono 
    [of "{0..<dim_vec u}" 
      "(\<lambda>i. if vec_index u i then 1 else 0)" 
      "(\<lambda>i. if vec_index v i then 1 else 0)"]
  using ulev
  unfolding Matrix.less_eq_vec_def
  by fastforce

lemma
  monotone_threshold:
  assumes ulev: "(u::bool vec) \<le> v"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  unfolding bool_fun_threshold_def
  using monotone_count_true [OF ulev] by simp

text\<open>It seems that the previous result does not require any assumption in the
  natural number n defining the threshold, even if it seems sensible to introduce it,
  as in the result below\<close>

lemma
  assumes "(u::bool vec) \<le> v"
  and "n < dim_vec u"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  using monotone_threshold [OF assms(1)] .

text\<open>The threshold functions are monotone\<close>

lemma "mono_on (bool_fun_threshold n) UNIV"
  by (meson mono_onI monotone_bool_fun_def monotone_threshold)

lemma "monotone_bool_fun (bool_fun_threshold k)"
  unfolding monotone_bool_fun_def
  by (meson boolean_functions.monotone_threshold mono_onI)

end

end
