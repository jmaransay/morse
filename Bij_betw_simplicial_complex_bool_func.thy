
theory Bij_betw_simplicial_complex_bool_func
  imports 
    Simplicial_complex
begin

section\<open>Bijection between simplicial complexes and Boolean functions\<close>

definition bool_vec_from_simplice :: "('n::finite) set => (bool^'n)"
  where "bool_vec_from_simplice \<sigma> = (\<chi> i::'n. if i \<in> \<sigma> then False else True)"

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

definition boolean_function_from_simplicial_complex :: "('n::finite) set set => (bool^'n => bool)"
  where "boolean_function_from_simplicial_complex K = (\<lambda>x. x \<in> (bool_vec_set_from_simplice_set K))"

lemma "Collect (boolean_function_from_simplicial_complex K) = (bool_vec_set_from_simplice_set K)"
  unfolding boolean_function_from_simplicial_complex_def  by simp

text\<open>The Boolean function induced by a simplicial complex is monotone.
  This result is proven in Scoville as part of the proof of Proposition 6.16.\<close>

lemma
  simplicial_complex_induces_monotone_bool_fun:
  assumes mon: "simplicial_complex (K::'n::class_mod_type set set)" 
  shows "monotone_bool_fun (boolean_function_from_simplicial_complex K)"
proof (unfold monotone_bool_fun_def, intro mono_onI)
  fix r and s::"(bool, 'n) vec"
  assume r_le_s: "r \<le> s"
  show "boolean_function_from_simplicial_complex K r \<le> boolean_function_from_simplicial_complex K s"
  proof (cases "boolean_function_from_simplicial_complex K r")
    case False then show ?thesis by simp
  next
    case True
    have ce: "ceros_of_boolean_input s \<subseteq> ceros_of_boolean_input r"
      using monotone_ceros_of_boolean_input [OF r_le_s] .
    have "boolean_function_from_simplicial_complex K s"
      using True
      unfolding boolean_function_from_simplicial_complex_def bool_vec_set_from_simplice_set_def
      using ce
      unfolding bool_vec_from_simplice_def
      unfolding ceros_of_boolean_input_def apply auto try
      
    show ?thesis
      apply (intro subsetI)
      unfolding ceros_of_boolean_input_def
    proof
      fix x assume "x \<in> {x. s $ x = False}" hence nr: "s $ x = False" by simp
      show "r $ x = False" using r_le_s nr unfolding less_eq_vec_def by auto
      apply (intro CollectI)
      using r_le_s
      unfolding less_eq_vec_def apply auto 
      try
    "

    proof (rule ccontr)
      assume "\<not> boolean_function_from_simplicial_complex K s"
      from True obtain "\<sigma>\<^sub>r" where "\<sigma>\<^sub>r \<in> K" and "r = bool_vec_from_simplice \<sigma>\<^sub>r"
        unfolding boolean_function_from_simplicial_complex_def bool_vec_set_from_simplice_set_def 
        by auto
      find_theorems "?A::(bool^'a) => ('a::finite) set"
      
      with r_le_s and True and mon
      show False
        unfolding boolean_function_from_simplicial_complex_def
        unfolding bool_vec_set_from_simplice_set_def
        unfolding simplicial_complex_def
text\<open>Proposition 6.16 in Scoville\<close>

declare [[show_sorts]]

lemma 
  shows "bij_betw simplicial_complex_induced_by_monotone_boolean_function monotone_bool_fun_set simplicial_complex_set"
proof (intro bij_betwI [of _ _ _ boolean_function_from_simplicial_complex])
  show "simplicial_complex_induced_by_monotone_boolean_function \<in> monotone_bool_fun_set \<rightarrow> (simplicial_complex_set::'a set set set)"
  proof
    fix x::"(bool, 'a) vec \<Rightarrow> bool"
    assume x: "x \<in> monotone_bool_fun_set"
    show "simplicial_complex_induced_by_monotone_boolean_function x \<in> simplicial_complex_set"
      using monotone_bool_fun_induces_simplicial_complex [of x] x
      using monotone_bool_fun_set_def simplicial_complex_set_def by auto
  qed
  show "boolean_function_from_simplicial_complex \<in> (simplicial_complex_set::'a set set set) \<rightarrow> monotone_bool_fun_set"
  proof
    fix x::"'a set set" assume "x \<in> simplicial_complex_set"
    show "boolean_function_from_simplicial_complex x \<in> monotone_bool_fun_set"
      try
qed

end