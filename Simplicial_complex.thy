
theory Simplicial_complex
  imports 
    Boolean_functions
    Finite_mod_type
begin

section\<open>Simplicial Complex\<close>

definition Pow_ne :: "'a set => 'a set set"
  where "Pow_ne A = {B. B \<noteq> {} \<and> B \<subseteq> A}"

lemma Pow_ne_singleton: "Pow_ne {a} = {{a}}"
  unfolding Pow_ne_def by auto

lemma Pow_ne_pair: "Pow_ne {a,b} = {{a},{b},{a,b}}"
  unfolding Pow_ne_def by auto

definition simplicial_complex :: "('n::finite) set set => bool"
  where "simplicial_complex K \<equiv>  ({} \<notin> K) \<and> (\<forall>\<sigma>\<in>K. (Pow_ne \<sigma>) \<subseteq> K)"

definition simplicial_complex_set :: "('n::finite) set set set"
  where "simplicial_complex_set = (Collect simplicial_complex)"

lemma simplicial_complex_not_empty_set:
  fixes K::"('n::finite) set set"
  assumes k: "simplicial_complex K"  
  shows "{} \<notin> K" using k unfolding simplicial_complex_def Pow_ne_def by simp

lemma
  simplicial_complex_monotone:
  fixes K::"('n::finite) set set"
  assumes k: "simplicial_complex K" and s: "s \<in> K" and rs: "r \<subseteq> s" and rne: "r \<noteq> {}"
  shows "r \<in> K"
  using k rs rne
  unfolding simplicial_complex_def Pow_ne_def
  by (smt (verit, del_insts) Diff_insert_absorb mem_Collect_eq s subset_Diff_insert)

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

lemma 
  ceros_of_boolean_input_complementary:
  shows "ceros_of_boolean_input v = - {x. v $ x}"
  unfolding ceros_of_boolean_input_def by auto

text\<open>In fact, the following result is trivial\<close>

lemma ceros_in_UNIV: "ceros_of_boolean_input f \<subseteq> (UNIV::'n::finite set)"
  using subset_UNIV .

lemma monotone_ceros_of_boolean_input:
  fixes r and s::"(bool, 'n::finite) vec"
  assumes r_le_s: "r \<le> s"
  shows "ceros_of_boolean_input s \<subseteq> ceros_of_boolean_input r"
proof (intro subsetI, unfold ceros_of_boolean_input_def, intro CollectI)
  fix x 
  assume "x \<in> {x. s $ x = False}" hence nr: "s $ x = False" by simp
  show "r $ x = False" using r_le_s nr unfolding less_eq_vec_def by auto
qed

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

text\<open>The simplicial complex induced by a Boolean function is a subset of the 
  powerset of the indexes\<close>

lemma
  "simplicial_complex_induced_by_monotone_boolean_function (f::bool^'n::class_mod_type => bool)
    \<subseteq> Pow (UNIV)"
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  using ceros_of_boolean_input_int_subset by auto

lemma empty_set_not_in_simplicial_complex_induced: 
  "{} \<notin> simplicial_complex_induced_by_monotone_boolean_function (f::bool^'n::class_mod_type => bool)"
proof (rule ccontr, simp)
  assume y: "{} \<in> simplicial_complex_induced_by_monotone_boolean_function f"
  then obtain x::"bool^'n::class_mod_type" where x: "x \<noteq> 1" and c: "ceros_of_boolean_input x = {}"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def by auto
  thus False unfolding ceros_of_boolean_input_def using x
    by (metis (full_types) Collect_empty_eq_bot empty_def one_bool_def one_index vec_eq_iff)
qed

lemma
  boolean_vec_not_one:
  assumes A: "A \<subseteq> (UNIV::'n::class_mod_type set)" and ANE: "A \<noteq> {}"
  shows "(\<chi> i. if i \<in> A then False else True) \<noteq> 1"
proof -
  from A and ANE obtain x where x: "x \<in> A" by auto
  have "(\<chi> i. if i \<in> A then False else True) $ x = False" using x by simp
  thus ?thesis unfolding one_vec_def one_bool_def by fastforce
qed

text\<open>The simplicial complex induced by a monotone Boolean function is a simplicial complex.
  This result is proven in Scoville as part of the proof of Proposition 6.16.\<close>

lemma
  monotone_bool_fun_induces_simplicial_complex:
  assumes mon: "monotone_bool_fun (f::bool^'n::class_mod_type => bool)"
  shows "simplicial_complex (simplicial_complex_induced_by_monotone_boolean_function f)"
  unfolding simplicial_complex_def
proof (intro conjI) 
  show "{} \<notin> simplicial_complex_induced_by_monotone_boolean_function f"
    using empty_set_not_in_simplicial_complex_induced [of f] .
  show "\<forall>\<sigma>\<in>simplicial_complex_induced_by_monotone_boolean_function f.
       Pow_ne \<sigma> \<subseteq> simplicial_complex_induced_by_monotone_boolean_function f"
  proof (rule, unfold simplicial_complex_induced_by_monotone_boolean_function_def)
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
      then have tau: "\<tau> = {i::'n. i \<in> \<tau>}" and sub: "\<tau> \<subseteq> \<sigma>" and tau_ne: "\<tau> \<noteq> {}" unfolding Pow_ne_def by simp_all
      show "\<exists>x. x \<noteq> 1 \<and> f x \<and> ceros_of_boolean_input x = \<tau>" 
      proof (rule exI [of _ "(\<chi> i. if i \<in> \<tau> then False else True)"], intro conjI) 
        show "ceros_of_boolean_input (\<chi> i::'n. if i \<in> \<tau> then False else True) = \<tau>"
          unfolding ceros_of_boolean_input_def by simp
        show "f (\<chi> i::'n. if i \<in> \<tau> then False else True)"
          using fx and x_def and sub and mon 
          unfolding monotone_bool_fun_def
          using mono_onD [of f UNIV x "(\<chi> i::'n. if i \<in> \<tau> then False else True)"]
          apply auto unfolding less_eq_vec_def le_bool_def
          by (metis subset_eq vec_lambda_beta)
        show "(\<chi> i::'n. if i \<in> \<tau> then False else True) \<noteq> (1::(bool, 'n) vec)"
          using boolean_vec_not_one [of \<tau>] tau_ne by simp
      qed
    qed
  qed
qed

text\<open>Example 6.10 in Scoville\<close>

definition bool_fun_threshold_2_3 :: "(bool^finite_mod_4 => bool)"
  where "bool_fun_threshold_2_3 = (\<lambda>v. if 2 \<le> count_true v then True else False)"

lemma "bool_fun_threshold_2_3 
          (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> True 
                                        | a\<^sub>1 \<Rightarrow> True 
                                        | (_) \<Rightarrow> False) = True"
  unfolding bool_fun_threshold_2_3_def 
  unfolding count_true_def
  unfolding Collect_code
  unfolding enum_finite_mod_4_def by simp

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
  unfolding bool_fun_threshold_2_3_def 
  unfolding count_true_def
  unfolding Collect_code
  unfolding enum_finite_mod_4_def by simp

lemma "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> False
                                        | (_) \<Rightarrow> True)"
  unfolding bool_fun_threshold_2_3_def 
  unfolding count_true_def 
  unfolding Collect_code
  unfolding enum_finite_mod_4_def by simp

lemma ceros_of_boolean_input_in_set:
  "ceros_of_boolean_input (\<chi> i::'n::class_mod_type. if i \<in> A then False else True) = A"
  unfolding ceros_of_boolean_input_def by simp

lemma singleton_in_simplicial_complex_induced:
  "{x} \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  (is "?A \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3")
proof (unfold simplicial_complex_induced_by_monotone_boolean_function_def, rule,
      rule exI [of _ "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"], 
      intro conjI)
  show "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True) \<noteq> (1::(bool, finite_mod_4) vec)"
    by (rule boolean_vec_not_one, simp_all)
  show "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"
    unfolding bool_fun_threshold_2_3_def count_true_def Collect_code enum_finite_mod_4_def by simp
  show "ceros_of_boolean_input (\<chi> i::finite_mod_4. if i \<in> ?A then False else True) = ?A"
    by (rule ceros_of_boolean_input_in_set)
qed

lemma pair_in_simplicial_complex_induced:
  "{x,y} \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  (is "?A \<in> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3")
proof (unfold simplicial_complex_induced_by_monotone_boolean_function_def, rule,
      rule exI [of _ "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"], 
      intro conjI)
  show "(\<chi> i::finite_mod_4. if i \<in> ?A then False else True) \<noteq> (1::(bool, finite_mod_4) vec)"
    by (rule boolean_vec_not_one, simp_all)
  show "bool_fun_threshold_2_3 (\<chi> i::finite_mod_4. if i \<in> ?A then False else True)"
    unfolding bool_fun_threshold_2_3_def count_true_def Collect_code enum_finite_mod_4_def by simp
  show "ceros_of_boolean_input (\<chi> i::finite_mod_4. if i \<in> ?A then False else True) = ?A"
    by (rule ceros_of_boolean_input_in_set)
qed

lemma finite_False: "finite {x.(a::bool^'n::finite) $ x = False}" by auto

lemma finite_True: "finite {x.(a::bool^'n::finite) $ x = True}" by auto

lemma UNIV_disjoint: "{x.(a::bool^'n::finite) $ x = False} \<inter> {x. a $ x = True} = {}"
  by auto

lemma UNIV_union: "{x. (a::bool^'n::finite) $ x = False} \<union> {x. a $ x = True} = UNIV"
  by auto

lemma card_UNIV_union: "card {x. (a::bool^'n::finite) $ x = False} + card {x. a $ x = True} = card (UNIV::'n set)"
  (is "card ?true + card ?false = _")
proof -
  have "card ?true + card ?false = card (?true \<union> ?false) + card (?true \<inter> ?false)"
    by (rule card_Un_Int [OF finite_False finite_True]) 
  also have "... = card (UNIV::'n set) + card {}"
    unfolding UNIV_union UNIV_disjoint by simp
  finally show ?thesis by simp
qed

lemma card_complementary: 
  "card (ceros_of_boolean_input (a::bool^'n::finite)) + card ({x. a $ x = True}) = card (UNIV::'n set)"
  by (metis card_UNIV_union ceros_of_boolean_input_def)

lemma card_ceros_count_UNIV: 
  "card (ceros_of_boolean_input a) + count_true ((a::bool^'n::finite)) = card (UNIV::'n set)"
  using card_complementary [of a]
  unfolding ceros_of_boolean_input_def
  unfolding count_true_def by simp

lemma "{{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0,a\<^sub>1},{a\<^sub>0,a\<^sub>2},{a\<^sub>0,a\<^sub>3},{a\<^sub>1,a\<^sub>2},{a\<^sub>1,a\<^sub>3},{a\<^sub>2,a\<^sub>3}}
    = simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
  (is "{?a,?b,?c,?d,?e,?f,?g,?h,?i,?j} = _")
proof (rule)
  show "{{a\<^sub>0}, {a\<^sub>1}, {a\<^sub>2}, {a\<^sub>3}, {a\<^sub>0, a\<^sub>1}, {a\<^sub>0, a\<^sub>2}, {a\<^sub>0, a\<^sub>3}, {a\<^sub>1, a\<^sub>2}, {a\<^sub>1, a\<^sub>3}, {a\<^sub>2, a\<^sub>3}}
    \<subseteq> simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3"
    by (simp add: singleton_in_simplicial_complex_induced pair_in_simplicial_complex_induced)+ 
  show "simplicial_complex_induced_by_monotone_boolean_function bool_fun_threshold_2_3
    \<subseteq> {{a\<^sub>0}, {a\<^sub>1}, {a\<^sub>2}, {a\<^sub>3}, {a\<^sub>0, a\<^sub>1}, {a\<^sub>0, a\<^sub>2}, {a\<^sub>0, a\<^sub>3}, {a\<^sub>1, a\<^sub>2}, {a\<^sub>1, a\<^sub>3}, {a\<^sub>2, a\<^sub>3}}"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding bool_fun_threshold_2_3_def
    proof
    fix y::"finite_mod_4 set"
      assume y: "y \<in> {y. \<exists>x. x \<noteq> 1 \<and> (if 2 \<le> count_true x then True else False) \<and> ceros_of_boolean_input x = y}"
      then obtain x::"(bool, finite_mod_4) vec" 
        where x_none: "x \<noteq> 1"
          and ct_ge_2: "(if 2 \<le> count_true x then True else False)" 
          and cx: "ceros_of_boolean_input x = y" by auto
      have y_nempty: "y \<noteq> {}"
      proof (rule ccontr)
        assume y_empty: "\<not> y \<noteq> {}"
        from cx have "ceros_of_boolean_input x = {}" using y_empty by simp
        thus False unfolding ceros_of_boolean_input_def
          using x_none
        by (metis (full_types) Collect_empty_eq_bot empty_def one_bool_def one_index vec_eq_iff y_empty)
      qed
      have "count_true x + card (ceros_of_boolean_input x) = card (UNIV::finite_mod_4 set)"
        by (metis add.commute card_ceros_count_UNIV)
      hence "card (ceros_of_boolean_input x) \<le> 2" 
        by (metis CARD_finite_mod_4 add.commute ct_ge_2 nat_add_left_cancel_le numeral_Bit0)
      hence card_le: "card y \<le> 2" using cx by simp
      have "y \<in> {{},{a\<^sub>0}, {a\<^sub>1}, {a\<^sub>2}, {a\<^sub>3}, {a\<^sub>0, a\<^sub>1},{a\<^sub>0, a\<^sub>2},{a\<^sub>0, a\<^sub>3},{a\<^sub>1, a\<^sub>2},{a\<^sub>1, a\<^sub>3},{a\<^sub>2, a\<^sub>3}}"
      proof (rule ccontr)
        assume "y \<notin> {{},{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0, a\<^sub>1},{a\<^sub>0, a\<^sub>2},{a\<^sub>0, a\<^sub>3},{a\<^sub>1, a\<^sub>2},{a\<^sub>1, a\<^sub>3},{a\<^sub>2, a\<^sub>3}}"
        then have y_nin: "y \<notin> set [{},{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0, a\<^sub>1},{a\<^sub>0, a\<^sub>2},{a\<^sub>0, a\<^sub>3},{a\<^sub>1, a\<^sub>2},{a\<^sub>1, a\<^sub>3},{a\<^sub>2, a\<^sub>3}]" by simp
        have y_in: "y \<in> Pow UNIV" by simp 
        have "y \<in> set [{a\<^sub>0,a\<^sub>1,a\<^sub>2},{a\<^sub>0,a\<^sub>1,a\<^sub>3},{a\<^sub>0,a\<^sub>2,a\<^sub>3},{a\<^sub>1,a\<^sub>2,a\<^sub>3},{a\<^sub>0,a\<^sub>1,a\<^sub>2,a\<^sub>3}]"
          using DiffI [OF y_in y_nin] 
          unfolding UNIV_finite_mod_4
          unfolding list_powerset_finite_mod_4 by simp
        hence "card y \<ge> 3" by auto
        thus False using card_le by simp
      qed
      then show "y \<in> {{a\<^sub>0}, {a\<^sub>1}, {a\<^sub>2}, {a\<^sub>3}, {a\<^sub>0, a\<^sub>1}, {a\<^sub>0, a\<^sub>2}, {a\<^sub>0, a\<^sub>3}, {a\<^sub>1, a\<^sub>2}, {a\<^sub>1, a\<^sub>3}, {a\<^sub>2, a\<^sub>3}}"
       using y_nempty by simp
 qed
qed

end