
theory Simplicial_complex
  imports 
    Boolean_functions
    Finite_mod_type
begin

section\<open>Simplicial Complex\<close>

thm Pow_def

find_theorems "Pow"

definition Pow_ne :: "'a set => 'a set set"
  where "Pow_ne A = {B. B \<noteq> {} \<and> B \<subseteq> A}"

lemma Pow_ne_singleton: "Pow_ne {a} = {{a}}"
  unfolding Pow_ne_def by auto

lemma Pow_ne_pair: "Pow_ne {a,b} = {{a},{b},{a,b}}"
  unfolding Pow_ne_def by auto

definition simplicial_complex :: "('n::finite) set set => bool"
  where "simplicial_complex K = (\<forall>\<sigma>\<in>K. (Pow_ne \<sigma>) \<subseteq> K)"

(*definition simplicial_complex_w :: "('n::finite) set set => bool"
  where "simplicial_complex_w K = simplicial_complex K \<and> {} \<notin> K"

definition simplicial_complex :: "('n::finite) set set => bool"
  where "simplicial_complex K = (\<forall>\<sigma>\<in>K. \<forall>\<tau>\<subseteq>\<sigma>. \<tau> \<noteq> {} \<and> \<tau> \<in> K)"*)

text\<open>One example of simplicial complex with four points\<close>

lemma "simplicial_complex {{a\<^sub>0::finite_mod_4},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3}}"
  by (simp add: Pow_ne_singleton simplicial_complex_def)

lemma "\<not> simplicial_complex {{a\<^sub>0::finite_mod_4, a\<^sub>1},{a\<^sub>1}}"
  by (simp add: Pow_ne_pair simplicial_complex_def)

text\<open>Another  example of simplicial complex with four points\<close>

lemma "simplicial_complex {{a\<^sub>0::finite_mod_4},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0,a\<^sub>1}}" 
  by (simp add: Pow_ne_pair Pow_ne_singleton simplicial_complex_def)

text\<open>Another example of simplicial complex with four points; 
  the proof shall be improved, trying to reduce the repetitions.\<close>

lemma "simplicial_complex 
    {{a\<^sub>2,a\<^sub>3},{a\<^sub>1,a\<^sub>3},{a\<^sub>1,a\<^sub>2},{a\<^sub>0,a\<^sub>3},{a\<^sub>0,a\<^sub>2},{a\<^sub>3},{a\<^sub>2},{a\<^sub>1},{a\<^sub>0::finite_mod_4}}"
  by (simp add: Pow_ne_pair Pow_ne_singleton simplicial_complex_def)

text\<open>Simplicial complex induced by a monotone Boolean function\<close>

text\<open>The simplicial complex induced by a monotone Boolean function, Definition 6.9 in Scoville\<close>

text\<open>First we introduce the tuples that make cero a Boolean input\<close>

definition ceros_of_boolean_input :: "(bool^'n) => 'n set"
  where "ceros_of_boolean_input v = {x. v $ x = False}"

text\<open>In fact, the following result is trivial\<close>

lemma ceros_in_UNIV: "ceros_of_boolean_input f \<subseteq> (UNIV::'n::finite set)"
  using subset_UNIV .

text\<open>The indexes of Boolean inputs demand the underlying type to be a "mod_type",
that indeed should be a finite type, but it is not proven in the library\<close>

definition ceros_of_boolean_input_int :: "(bool^'n::class_mod_type) => int set"
  where "ceros_of_boolean_input_int v = image to_int (ceros_of_boolean_input v)"

lemma ceros_of_boolean_input_int_subset:
  "ceros_of_boolean_input_int (f::(bool^'n::class_mod_type)) \<subseteq> {0 ..< int CARD('n)}"
  by (metis Rep_in ceros_of_boolean_input_int_def imageE subsetI to_int_def)

text\<open>We introduce here two instantiations of the Boolean type for the type classes 0 and one
  that will simplify notation at some points:\<close>

instantiation bool :: one
begin

definition
 one_bool_def: "1 == True"

instance  proof  qed

end

instantiation bool :: zero
begin

definition
 zero_bool_def: "0 == False"

instance  proof  qed

end

definition
  simplicial_complex_induced_by_monotone_boolean_function_int
    :: "(bool^'n::class_mod_type => bool) => int set set"
  where "simplicial_complex_induced_by_monotone_boolean_function_int f = 
        {y. \<exists>x. x \<noteq> 1 \<and> f x = True \<and> ceros_of_boolean_input_int x = y}"

definition
  simplicial_complex_induced_by_monotone_boolean_function 
    :: "(bool^'n::class_mod_type => bool) => 'n set set"
  where "simplicial_complex_induced_by_monotone_boolean_function f = 
        {y. \<exists>x. x \<noteq> 1 \<and> f x \<and> ceros_of_boolean_input x = y}"

declare [[show_types]]

lemma
  assumes mon: "monotone_bool_fun (f::bool^'n::class_mod_type => bool)"
  shows "simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function f)"
  unfolding simplicial_complex_def
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
proof
  fix \<sigma>::"'n set"
  assume sigma: "\<sigma> \<in> {y. \<exists>x. x \<noteq> 1 \<and> f x \<and> ceros_of_boolean_input x = y}"
  from sigma obtain x where x_none: "x \<noteq> 1" 
                      and fx: "f x" and ceros_sigma: "ceros_of_boolean_input x = \<sigma>" by auto
  hence x_def: "x = (\<chi> i::'n. if i \<in> \<sigma> then False else True)"
    unfolding ceros_of_boolean_input_def by auto
  show "Pow_ne \<sigma> \<subseteq> {y. \<exists>x. x \<noteq> 1 \<and> f x \<and> ceros_of_boolean_input x = y}"
  proof (safe)
    fix \<tau>::"'n set"
    assume subset: "\<tau> \<in> Pow_ne \<sigma>"
    then have tau: "\<tau> = {i::'n. i \<in> \<tau>}" and sub: "\<tau> \<subseteq> \<sigma>" unfolding Pow_ne_def by simp_all
    show "\<exists>x. x \<noteq> 1 \<and> f x \<and> ceros_of_boolean_input x = \<tau>" 
    proof (rule exI [of _ "(\<chi> i. if i \<in> \<tau> then False else True)"], intro conjI) 
      show "ceros_of_boolean_input (\<chi> i::'n. if i \<in> \<tau> then False else True) = \<tau>"
        unfolding ceros_of_boolean_input_def by simp
      show "f (\<chi> i::'n. if i \<in> \<tau> then False else True)"
        using fx and x_def and sub and mon 
        using mono_onD [of f UNIV x "(\<chi> i::'n. if i \<in> \<tau> then False else True)"]
        apply auto try        
      show "(\<chi> i::'n. if i \<in> \<tau> then False else True) \<noteq> (1::(bool, 'n) vec)"
        using subset using x_none unfolding x_def one_vec_def one_bool_def
          apply (cases "\<tau> = {}", auto) try
        apply (simp add: Pow_ne_def)
  
sorry

text\<open>The simplicial complex induced by a Boolean function is a subset of the 
  powerset of the indexes\<close>

lemma
  "(simplicial_complex_induced_by_monotone_boolean_function (f::bool^'n::class_mod_type => bool)) 
    \<subseteq> Pow (UNIV)"
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  using ceros_of_boolean_input_int_subset by auto

lemma
  "(simplicial_complex_induced_by_monotone_boolean_function_int (f::bool^'n::class_mod_type => bool)) 
    \<subseteq> Pow {0..< int CARD('n)}"
  unfolding simplicial_complex_induced_by_monotone_boolean_function_int_def
  using ceros_of_boolean_input_int_subset by auto

text\<open>Example 6.10 in Scoville\<close>

definition bool_fun_threshold_2_3 :: "(bool^finite_mod_4 => bool)"
  where "bool_fun_threshold_2_3 = (\<lambda>v. if 2 \<le> count_true v then True else False)"

lemma "bool_fun_threshold_2_3 
          (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False) = True"
  unfolding bool_fun_threshold_2_3_def 
  unfolding count_true_def
  unfolding UNIV_finite_mod_4 by simp

lemma foo1:
  "a\<^sub>0 \<notin> ceros_of_boolean_input (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False)"
  and foo2: "a\<^sub>1 \<notin> ceros_of_boolean_input (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False)"
  and foo3: "a\<^sub>2 \<in> ceros_of_boolean_input (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False)"
  and foo4: "a\<^sub>3 \<in> ceros_of_boolean_input (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False)"
  unfolding ceros_of_boolean_input_int_def
  unfolding ceros_of_boolean_input_def
  unfolding Rep_finite_mod_4_def by simp_all

lemma "{a\<^sub>2,a\<^sub>3} \<subseteq> ceros_of_boolean_input (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False)"
  using foo1 foo2 foo3 foo4 UNIV_finite_mod_4 by simp

lemma "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> False
                                        | a\<^sub>1 \<Rightarrow> False
                                        | a\<^sub>2 \<Rightarrow> False
                                        | (_) \<Rightarrow> True) = False"
 unfolding bool_fun_threshold_2_3_def count_true_def UNIV_finite_mod_4 by simp

lemma "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> False
                                        | (_) \<Rightarrow> True)"
 unfolding bool_fun_threshold_2_3_def count_true_def UNIV_finite_mod_4 by simp

lemma
  boolean_vec_not_one:
  assumes A: "A \<subseteq> (UNIV::'n::class_mod_type set)" and ANE: "A \<noteq> {}"
  shows "(\<chi> i. if i \<in> A then False else True) \<noteq> 1"
proof -
  from A and ANE obtain x where x: "x \<in> A" by auto
  have "(\<chi> i. if i \<in> A then False else True) $ x = False" using x by simp
  thus ?thesis unfolding one_vec_def one_bool_def by fastforce
qed

lemma ceros_of_boolean_input_in_set:
  "ceros_of_boolean_input (\<chi> i::'n::class_mod_type. if i \<in> A then False else True) 
        = A"
  unfolding ceros_of_boolean_input_def by simp

lemma "{a\<^sub>1, a\<^sub>2}
    \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  (is "?A \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3")
proof (unfold simplicial_complex_induced_by_monotone_boolean_function_def, rule,
      rule exI [of _ "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"], 
      intro conjI)
  show "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True) \<noteq> (1::(bool, finite_mod_4) vec)"
    by (rule boolean_vec_not_one, simp_all)
  show "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"
    unfolding bool_fun_threshold_2_3_def count_true_def UNIV_finite_mod_4 ceros_of_boolean_input_def by auto
  show "ceros_of_boolean_input (\<chi> i::finite_mod_4. if i \<in> ?A then False else True) = ?A"
    by (rule ceros_of_boolean_input_in_set)
qed

lemma 
  assumes ANE: "A \<noteq> {}" and card: "card A \<le> 2"
  shows "A
    \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  (is "?A \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3")
proof (unfold simplicial_complex_induced_by_monotone_boolean_function_def, rule,
      rule exI [of _ "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"], 
      intro conjI)
  show "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True) \<noteq> (1::(bool, finite_mod_4) vec)"
    using boolean_vec_not_one [OF _ ANE] by simp
  show "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"
  proof (unfold bool_fun_threshold_2_3_def count_true_def UNIV_finite_mod_4 ceros_of_boolean_input_def,
      simp_all add: card finite_mod_4.exhaust finite_mod_4.nchotomy, safe)
    assume a2: "a\<^sub>2 \<in> A" and a3: "a\<^sub>3 \<in> A" and a1: "a\<^sub>1 \<in> A"
    hence "3 \<le> card A"
    proof (cases "a\<^sub>0 \<in> A")
      case True
      have "A = UNIV" using a1 a2 a3 True UNIV_finite_mod_4 try
        thus ?case 
      next
      case False
      have "card A = 3" using a1 a2 a3 False UNIV_finite_mod_4 try
    try
    using card UNIV_finite_mod_4 try apply auto
  qed
  have "card {a\<^sub>1, a\<^sub>2, a\<^sub>3} = 3" by simp
  show "ceros_of_boolean_input (\<chi> i::finite_mod_4. if i \<in> ?A then False else True) = ?A"
    by (rule ceros_of_boolean_input_in_set)
qed


find_theorems (999) "(?A \<subseteq> ?B)"

lemma "{{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0,a\<^sub>1},{a\<^sub>0,a\<^sub>2},{a\<^sub>0,a\<^sub>3},{a\<^sub>1,a\<^sub>2},{a\<^sub>1,a\<^sub>3},{a\<^sub>2,a\<^sub>3}} 
    \<subseteq> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  (is "{?a,?b,?c,?d,?e,?f,?g,?h,?i,?j} \<subseteq> _")
proof (intro subsetI)
  fix x
  assume x: "x \<in> {?a,?b,?c,?d,?e,?f,?g,?h,?i,?j}"
  show "x \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  proof (cases "x = ?a")
    unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def unfolding UNIV_finite_mod_4
  unfolding ceros_of_boolean_input_def
  apply (rule, rule)
  apply (rule exI [of _ "(\<chi> i::finite_mod_4. if i \<in> ?b then False else True)"])
  using exI [of _ "(\<chi> i::finite_mod_4. if i \<in> ?b then False else True)"]
  using boolean_vec_not_one
  using ceros_of_boolean_input_in_set apply auto
  try
  unfolding count_true_def using UNIV_finite_mod_4
  try

end