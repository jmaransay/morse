theory Binary_operations
  imports Bij_betw_simplicial_complex_bool_func
begin

definition bool_fun_or :: "(bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool)"
  where "(bool_fun_or f g) x \<equiv> (f x) \<or> (g x)"

definition bool_fun_and :: "(bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'n \<Rightarrow> bool)"
  where "(bool_fun_and f g) x \<equiv> (f x) \<and> (g x)"

definition bool_fun_ast :: "(bool^'n \<Rightarrow> bool) \<Rightarrow> (bool^'m \<Rightarrow> bool) \<Rightarrow> ((bool^'n) \<Rightarrow>(bool^'m) \<Rightarrow> bool)"
  where "(bool_fun_ast f g) x y \<equiv> (f x) \<and> (g y)"

definition
  simplicial_complex_induced_by_monotone_boolean_function_ast 
    :: "(bool^'n::class_mod_type => bool^'m::class_mod_type \<Rightarrow> bool) => ('n set * 'm set) set"
  where "simplicial_complex_induced_by_monotone_boolean_function_ast f = 
        {z. \<exists>x y. f x y \<and> ((ceros_of_boolean_input x), (ceros_of_boolean_input y)) = z}"

lemma fst_es_simplice:
  "a \<in> simplicial_complex_induced_by_monotone_boolean_function_ast f 
\<Longrightarrow> (\<exists>x y. f x y \<and> (ceros_of_boolean_input x) = fst(a))"
  by (smt (verit) fst_conv mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_ast_def)

lemma snd_es_simplice:
  "a \<in> simplicial_complex_induced_by_monotone_boolean_function_ast f 
\<Longrightarrow> (\<exists>x y. f x y \<and> (ceros_of_boolean_input y) = snd(a))"
  by (smt (verit) snd_conv mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_ast_def)

definition set_ast :: "('a set) \<Rightarrow> ('b set) \<Rightarrow> (('a*'b) set)"
  where "set_ast A B \<equiv> {c. \<exists>a\<in>A. \<exists>b\<in>B. c = (a,b)}"

definition set_fst :: "('a::class_mod_type*'b::class_mod_type) set \<Rightarrow> 'a set"
  where "set_fst AB = {a. \<exists>ab\<in>AB. a = fst ab}"

value "set_fst {a, b}"

lemma set_fst_simp [simp]:
  assumes "y \<noteq> {}"
  shows "set_fst (x \<times> y) = x"
proof
  show "set_fst (x \<times> y) \<subseteq> x"
    by (smt (verit) SigmaE mem_Collect_eq prod.sel(1) set_fst_def subsetI)
  show "x \<subseteq> set_fst (x \<times> y)"
  proof
    fix a::"'b"
    assume "a \<in> x"
    then obtain b where "b \<in> y" and "(a,b) \<in> (x\<times>y)"
      using assms by blast
    then show "a \<in> set_fst (x \<times> y)"
      using set_fst_def by fastforce
  qed
qed

definition set_snd :: "('a*'b) set \<Rightarrow> 'b set"
  where "set_snd AB = {b. \<exists>ab\<in>AB. b = snd(ab)}"

definition bool_fun_times :: "(bool^('n::class_mod_type) \<Rightarrow> bool) \<Rightarrow> (bool^('m::class_mod_type) \<Rightarrow> bool) \<Rightarrow> (bool^('n*'m) \<Rightarrow> bool)"
  where "(bool_fun_times f g) x \<equiv>
     f (bool_vec_from_simplice (set_fst (ceros_of_boolean_input x)))
   \<and> g (bool_vec_from_simplice (set_snd (ceros_of_boolean_input x)))"

(* La siguiente condición causa que el teorema pertinente sea incorrecto:
 \<and> (\<nexists>c. \<exists>d\<in>(ceros_of_boolean_input x). c\<in>(ceros_of_boolean_input x) \<and> (fst c < fst d) \<and> (snd c > snd d))*)

definition
  simplicial_complex_induced_by_monotone_boolean_function_times 
    :: "(bool^('n::class_mod_type*'m::class_mod_type) \<Rightarrow> bool) => (('n set)*('m set)) set"
  where "simplicial_complex_induced_by_monotone_boolean_function_times f = 
        {z. \<exists>x y. f (bool_vec_from_simplice (x \<times> y)) \<and> (x, y) = z}"

lemma simp_ceros [simp]: "ceros_of_boolean_input (bool_vec_from_simplice (x \<times> y)) = x \<times> y"
  unfolding bool_vec_from_simplice_def
  unfolding ceros_of_boolean_input_def by auto

lemma eq_union_or: 
"simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)
= simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
proof
  show "simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g \<subseteq> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)"
  proof
    fix \<sigma>::"'a set"
    assume "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<or> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
    hence "f (bool_vec_from_simplice \<sigma>) \<or> g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "bool_fun_or f g (bool_vec_from_simplice \<sigma>)"
      unfolding bool_fun_or_def
      by auto
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)"
      using simplicial_complex_induced_by_monotone_boolean_function_def
      by fastforce
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g) \<subseteq> simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
  proof
    fix \<sigma>::"'a set"
    assume sigma: "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_or f g)"
    hence "bool_fun_or f g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "(f (bool_vec_from_simplice \<sigma>)) \<or> (g (bool_vec_from_simplice \<sigma>))"
      unfolding bool_fun_or_def
      by auto
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<or> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by (smt (z3) sigma bool_fun_or_def mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<union> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
  qed
qed

lemma eq_inter_and: 
"simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)
= simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
proof
  show "simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g \<subseteq> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)"
  proof
    fix \<sigma>::"'a set"
    assume "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<and> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
    hence "f (bool_vec_from_simplice \<sigma>) \<and> g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "bool_fun_and f g (bool_vec_from_simplice \<sigma>)"
      unfolding bool_fun_and_def
      by auto
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)"
      using simplicial_complex_induced_by_monotone_boolean_function_def
      by fastforce
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g) \<subseteq> simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
  proof
    fix \<sigma>::"'a set"
    assume sigma: "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function (bool_fun_and f g)"
    hence "bool_fun_and f g (bool_vec_from_simplice \<sigma>)"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    hence "(f (bool_vec_from_simplice \<sigma>)) \<and> (g (bool_vec_from_simplice \<sigma>))"
      unfolding bool_fun_and_def
      by auto
    hence "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<and> \<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by (smt (z3) sigma bool_fun_and_def mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    thus "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function f \<inter> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
  qed
qed

lemma eq_ast: 
"simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g)
= set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g)"
proof
  show "set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g) \<subseteq> simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g)"
  proof
    fix \<gamma>::"'a set*'b set"
    assume pert: "\<gamma> \<in> set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g)"
    hence "(fst \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function f"
      unfolding set_ast_def
      by auto
    hence sigma: "f (bool_vec_from_simplice (fst \<gamma>))"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    from pert have "(snd \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      unfolding set_ast_def
      by auto
    hence tau: "g (bool_vec_from_simplice (snd \<gamma>))"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    from sigma and tau have sigtau: "bool_fun_ast f g (bool_vec_from_simplice (fst \<gamma>)) (bool_vec_from_simplice (snd \<gamma>))"
      unfolding bool_fun_ast_def
      by auto
    from sigtau show "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g)"
      using bool_vec_from_simplice_def ceros_of_boolean_input_in_set mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_ast_def
      by fastforce
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g) \<subseteq> set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g)"
  proof
    fix \<gamma>::"'a set*'b set"
    assume pert: "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g)"
    hence sigma: "(fst \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function f"
      by (smt (verit) bool_fun_ast_def fst_es_simplice mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    from pert have tau: "(snd \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by (smt (verit) bool_fun_ast_def snd_es_simplice mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    from sigma and tau show "\<gamma> \<in> set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g)"
      using set_ast_def
      by force
  qed
qed

(*The following theorem, from ``Homology of Boolean functions and the
complexity of simplicial homology'', Erick J. Chastain and Nicholas A. Scoville, apparently does not hold*)

(*lemma eq_times: 
"simplicial_complex_induced_by_monotone_boolean_function_times (bool_fun_times f g)
= (simplicial_complex_induced_by_monotone_boolean_function f) \<times> (simplicial_complex_induced_by_monotone_boolean_function g)"
proof
  show "(simplicial_complex_induced_by_monotone_boolean_function f) \<times> (simplicial_complex_induced_by_monotone_boolean_function g) \<subseteq> simplicial_complex_induced_by_monotone_boolean_function_times (bool_fun_times f g)"
  proof
    fix \<gamma>::"('a set)*('b set)"
    assume pert: "\<gamma> \<in> (simplicial_complex_induced_by_monotone_boolean_function f) \<times> (simplicial_complex_induced_by_monotone_boolean_function g)"
    hence "(fst \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function f"
      by auto
    hence sigma: "f (bool_vec_from_simplice (fst \<gamma>))"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    from pert have "(snd \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by auto
    hence tau: "g (bool_vec_from_simplice (snd \<gamma>))"
      by (metis (mono_tags, lifting) bool_vec_set_from_simplice_set_def boolean_function_from_simplicial_complex_def boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function_id mem_Collect_eq)
    from sigma and tau have sigtau: "bool_fun_times f g (bool_vec_from_simplice ((fst \<gamma>) \<times> (snd \<gamma>)))"
      using simp_ceros
      unfolding bool_fun_times_def
      unfolding set_fst_def
      unfolding set_snd_def
      by simp
    from sigma and tau show "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_times (bool_fun_times f g)"
      using bool_vec_from_simplice_def ceros_of_boolean_input_in_set mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_times_def
      by blast
  qed
next
  show "simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g) \<subseteq> set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g)"
  proof
    fix \<gamma>::"'a set*'b set"
    assume pert: "\<gamma> \<in> simplicial_complex_induced_by_monotone_boolean_function_ast (bool_fun_ast f g)"
    hence sigma: "(fst \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function f"
      by (smt (verit) bool_fun_ast_def fst_es_simplice mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    from pert have tau: "(snd \<gamma>) \<in> simplicial_complex_induced_by_monotone_boolean_function g"
      by (smt (verit) bool_fun_ast_def snd_es_simplice mem_Collect_eq simplicial_complex_induced_by_monotone_boolean_function_def)
    from sigma and tau show "\<gamma> \<in> set_ast (simplicial_complex_induced_by_monotone_boolean_function f) (simplicial_complex_induced_by_monotone_boolean_function g)"
      using simp_ceros
      by force
  qed
qed*)

end