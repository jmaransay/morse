
theory Bij_betw_simplicial_complex_bool_func
  imports 
    Simplicial_complex
begin

section\<open>Bijection between simplicial complexes and Boolean functions\<close>

definition bool_vec_from_simplice :: "('n::finite) set => (bool^'n)"
  where "bool_vec_from_simplice \<sigma> = (\<chi> i::'n. if i \<in> \<sigma> then False else True)"

lemma
  true_not_bool_vec_from_simplice:
  fixes K::"'n::class_mod_type set set" and x::"'n set" 
  assumes K: "simplicial_complex (K::'n::class_mod_type set set)"
  and x: "x \<in> K"
  shows "bool_vec_from_simplice x \<noteq> (\<chi> i. True)"
proof (unfold bool_vec_from_simplice_def, rule) 
  assume "(\<chi> i. if i \<in> x then False else True) = (\<chi> i. True)"
  then have "x = {}" unfolding bool_vec_from_simplice_def
    by (smt (verit, ccfv_SIG) ceros_of_boolean_input_in_set emptyE vec_lambda_unique)
  with K show False
    using x simplicial_complex_not_empty_set by blast
qed

lemma "bool_vec_from_simplice {a\<^sub>0} = (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> False
                                        | (_) \<Rightarrow> True)"
  unfolding bool_vec_from_simplice_def using UNIV_finite_mod_4 by force

lemma "bool_vec_from_simplice {a\<^sub>1,a\<^sub>2} = (\<chi> i::finite_mod_4. case (i) of a\<^sub>1 \<Rightarrow> False
                                        | a\<^sub>2 \<Rightarrow> False
                                        | (_) \<Rightarrow> True)"
  unfolding bool_vec_from_simplice_def apply simp apply (rule ext)
  by (metis finite_mod_4.exhaust finite_mod_4.simps(13) finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16))

definition bool_vec_set_from_simplice_set :: "('n::finite) set set => (bool^'n) set"
  where "bool_vec_set_from_simplice_set K = {\<sigma>. \<exists>k\<in>K. \<sigma> = bool_vec_from_simplice k}"

lemma
  true_not_bool_vec_from_simplice_set:
  fixes K::"'n::class_mod_type set set"
  assumes mon: "simplicial_complex (K::'n::class_mod_type set set)"
  shows "(\<chi> i. True) \<notin> (bool_vec_set_from_simplice_set K)"
  by (smt (verit) bool_vec_set_from_simplice_set_def mem_Collect_eq mon true_not_bool_vec_from_simplice)

definition boolean_function_from_simplicial_complex :: "('n::finite) set set => (bool^'n => bool)"
  where "boolean_function_from_simplicial_complex K = (\<lambda>x. x \<in> (bool_vec_set_from_simplice_set K))"

lemma "Collect (boolean_function_from_simplicial_complex K) = (bool_vec_set_from_simplice_set K)"
  unfolding boolean_function_from_simplicial_complex_def by simp

lemma
  true_not_in_boolean_function_from_simplicial_complex:
  fixes K::"'n::class_mod_type set set"
  assumes mon: "simplicial_complex (K::'n::class_mod_type set set)"
  shows "\<not> boolean_function_from_simplicial_complex K (\<chi> i. True)"
  unfolding boolean_function_from_simplicial_complex_def
  using true_not_bool_vec_from_simplice_set [OF mon] .

text\<open>The Boolean function induced by a simplicial complex is monotone.
  This result is proven in Scoville as part of the proof of Proposition 6.16.\<close>

lemma
  simplicial_complex_induces_monotone_bool_fun:
  assumes mon: "simplicial_complex (K::'n::class_mod_type set set)"
  shows "mono_on (boolean_function_from_simplicial_complex K) (Set.remove (\<chi> i. True) UNIV)"
proof (intro mono_onI)
  fix r and s::"(bool, 'n) vec"
  assume r: "r \<in> Set.remove (\<chi> i. True) UNIV"
    and s: "s \<in> Set.remove (\<chi> i. True) UNIV" 
    and r_le_s: "r \<le> s"
  show "boolean_function_from_simplicial_complex K r \<le> boolean_function_from_simplicial_complex K s"
  proof (cases "boolean_function_from_simplicial_complex K r")
    case False then show ?thesis by simp
  next
    case True
    have ce: "ceros_of_boolean_input s \<subseteq> ceros_of_boolean_input r"
      using monotone_ceros_of_boolean_input [OF r_le_s] .
    from True obtain k where r_def: "r = (\<chi> i. if i \<in> k then False else True)" and k: "k \<in> K"
      unfolding boolean_function_from_simplicial_complex_def
      unfolding bool_vec_set_from_simplice_set_def
      unfolding bool_vec_from_simplice_def by auto
    from k and r_def have r_in_K: "ceros_of_boolean_input r \<in> K" unfolding ceros_of_boolean_input_def by auto
    have cs_ne: "ceros_of_boolean_input s \<noteq> {}"
    proof (rule ccontr, simp)
      assume "ceros_of_boolean_input s = {}"
      hence "s = (\<chi> i. True)"
        unfolding ceros_of_boolean_input_def
        unfolding one_vec_def one_bool_def
        by (metis (full_types) emptyE mem_Collect_eq vec_lambda_unique)
      with s show False by simp
    qed
    have "boolean_function_from_simplicial_complex K s"
    proof (unfold boolean_function_from_simplicial_complex_def bool_vec_set_from_simplice_set_def, rule,
        rule bexI [of _ "ceros_of_boolean_input s"], unfold bool_vec_from_simplice_def)
      show "s = (\<chi> i. if i \<in> ceros_of_boolean_input s then False else True)" 
        unfolding ceros_of_boolean_input_def by auto
      show "ceros_of_boolean_input s \<in> K"
         using simplicial_complex_monotone [OF mon r_in_K ce cs_ne] .
     qed
     thus ?thesis by simp
  qed
qed

text\<open>The following lemma holds for every function x (the premise on monotonicity 
  can be avoided), except in b = 1. The only reason to introduce the premise on monotonicity
  is that this way we know that x 1 = 0, and thus we can prove the result for every input vector.  
  This result is proven in Scoville as part of the proof of Proposition 6.16.\<close>

lemma
  boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id: 
  fixes x :: "(bool, 'a::class_mod_type) vec \<Rightarrow> bool"
  assumes mon_x: "monotone_bool_fun x"
  shows "boolean_function_from_simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function x) = x"
proof (rule ext)
  fix b :: "bool^'a::class_mod_type"
  show "boolean_function_from_simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function x) b =
         x b"
  proof (intro iffI)
    assume "boolean_function_from_simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function x) b"
    then show "x b"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding boolean_function_from_simplicial_complex_def 
      unfolding bool_vec_set_from_simplice_set_def
      unfolding mem_Collect_eq
      proof (simp)
        assume "\<exists>k. (\<exists>xa. xa \<noteq> 1 \<and> x xa \<and> ceros_of_boolean_input xa = k) \<and> b = bool_vec_from_simplice k"
        then obtain k and xa where "xa \<noteq> 1" and x: "x xa" and "ceros_of_boolean_input xa = k"
          and b: "b = bool_vec_from_simplice k" by auto
        then have "xa = b" 
           unfolding ceros_of_boolean_input_def bool_vec_from_simplice_def
           by auto
         with x show ?thesis by fast
       qed
  next
  assume xb: "x b" then have bnt: "b \<noteq> 1" using mon_x unfolding monotone_bool_fun_def
      by (metis (mono_tags, lifting) one_bool_def one_index vec_lambda_unique)
  show "boolean_function_from_simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function x) b"
  proof -
    have "b \<noteq> 1 \<and> x b \<and> b = bool_vec_from_simplice (ceros_of_boolean_input b)"
      unfolding ceros_of_boolean_input_def bool_vec_from_simplice_def
      using bnt xb by auto
      then show ?thesis
        unfolding simplicial_complex_induced_by_monotone_boolean_function_def
        unfolding boolean_function_from_simplicial_complex_def 
        unfolding bool_vec_set_from_simplice_set_def
        unfolding mem_Collect_eq by auto
    qed
  qed
qed

lemma
  simplicial_complex_induced_by_monotone_boolean_function_boolean_function_from_simplicial_complex_id:
  fixes y :: "'a::class_mod_type set set"
  assumes y: "y \<in> simplicial_complex_set"
  shows "simplicial_complex_induced_by_monotone_boolean_function (boolean_function_from_simplicial_complex y) = y" 
proof (intro equalityI)
  show "simplicial_complex_induced_by_monotone_boolean_function (boolean_function_from_simplicial_complex y) \<subseteq> y"
  proof
    fix x :: "'a set"
    assume x: "x \<in> simplicial_complex_induced_by_monotone_boolean_function
              (boolean_function_from_simplicial_complex y)"
    show "x \<in> y"
      using x
      unfolding boolean_function_from_simplicial_complex_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding bool_vec_from_simplice_def bool_vec_set_from_simplice_set_def
      by (smt (verit, ccfv_SIG) ceros_of_boolean_input_in_set mem_Collect_eq)
  qed
next
 show "y \<subseteq> simplicial_complex_induced_by_monotone_boolean_function (boolean_function_from_simplicial_complex y)"
 proof
   fix x :: "'a set"
   assume x: "x \<in> y" 
   hence bvs: "bool_vec_from_simplice x \<noteq> 1 \<and> ceros_of_boolean_input (bool_vec_from_simplice x) = x"
     using true_not_bool_vec_from_simplice [OF _ x]
     unfolding one_vec_def one_bool_def
     unfolding bool_vec_from_simplice_def 
     using ceros_of_boolean_input_in_set [of x] 
     using y unfolding simplicial_complex_set_def by simp 
   show "x \<in> simplicial_complex_induced_by_monotone_boolean_function (boolean_function_from_simplicial_complex y)"
     unfolding boolean_function_from_simplicial_complex_def
     unfolding simplicial_complex_induced_by_monotone_boolean_function_def
     unfolding bool_vec_from_simplice_def bool_vec_set_from_simplice_set_def
     using x bool_vec_from_simplice_def bvs by blast
 qed
qed

text\<open>Proposition 6.16 in Scoville\<close>

lemma
  shows "bij_betw simplicial_complex_induced_by_monotone_boolean_function monotone_bool_fun_set simplicial_complex_set"
proof (intro bij_betwI [of _ _ _ boolean_function_from_simplicial_complex])
  show "simplicial_complex_induced_by_monotone_boolean_function \<in> monotone_bool_fun_set \<rightarrow> (simplicial_complex_set::'a set set set)"
  proof
    fix x::"(bool, 'a) vec \<Rightarrow> bool"
    assume x: "x \<in> monotone_bool_fun_set"
    show "simplicial_complex_induced_by_monotone_boolean_function x \<in> simplicial_complex_set"
      using monotone_bool_fun_induces_simplicial_complex [of x] x
      unfolding monotone_bool_fun_set_def monotone_bool_fun_def simplicial_complex_set_def
      by auto
  qed
  show "boolean_function_from_simplicial_complex \<in> (simplicial_complex_set::'a set set set) \<rightarrow> monotone_bool_fun_set"
  proof
    fix x::"'a set set" assume x: "x \<in> simplicial_complex_set"
    show "boolean_function_from_simplicial_complex x \<in> monotone_bool_fun_set"
      unfolding monotone_bool_fun_set_def
      unfolding monotone_bool_fun_def
      using x unfolding simplicial_complex_set_def
      unfolding mem_Collect_eq using simplicial_complex_induces_monotone_bool_fun [of x]
      using true_not_in_boolean_function_from_simplicial_complex [of x] 
      by auto
  qed
  fix x::"(bool, 'a) vec \<Rightarrow> bool"
  assume "x \<in> monotone_bool_fun_set"
  hence x_mon: "monotone_bool_fun x"
    unfolding monotone_bool_fun_set_def unfolding mem_Collect_eq .
  show "boolean_function_from_simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function x) = x"
    by (rule boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id [OF x_mon])
  next
  fix y :: "'a set set"
  assume y: "y \<in> simplicial_complex_set"
  show "simplicial_complex_induced_by_monotone_boolean_function (boolean_function_from_simplicial_complex y) = y"
    using simplicial_complex_induced_by_monotone_boolean_function_boolean_function_from_simplicial_complex_id [OF y] .
qed

end