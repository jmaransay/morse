
theory Alexander
  imports 
    Simplicial_complex
begin

section\<open>Definition of the Alexander dual of a simplicial complex\<close>

context simplicial_complex
begin

abbreviation "univ_n == {..<n}"

definition simplex_complement
  where "simplex_complement s == univ_n - s"

subsubsection \<open>Set complement\<close>

lemma
  simplex_complement_simplex:
  assumes v: "v \<in> simplices"
  shows "simplex_complement v \<in> simplices"
  using v
  by (simp add: atLeast0LessThan simplex_complement_def simplices_def)

lemma
  simplex_Compl_in:
  assumes s: "s \<in> simplices" and c: "c \<in> s"
  shows "c \<notin> simplex_complement s"
  using s c
  unfolding simplices_def 
  unfolding simplex_complement_def by simp

lemma
  simplex_Compl_notin:
  assumes s: "s \<in> simplices" and c: "c \<in> simplex_complement s"
  shows "c \<notin> s"
  using s c 
  unfolding simplices_def 
  unfolding simplex_complement_def by simp

lemma
  simplex_Compl_iff [simp]:
  assumes s: "s \<in> simplices" and c: "c < n"
  shows "c \<in> simplex_complement s \<longleftrightarrow> c \<notin> s"
  unfolding simplex_complement_def
  using s c unfolding simplices_def by simp

lemma
  assumes "x \<in> simplices"
  shows "x = simplex_complement (simplex_complement x)"
  using assms atLeast0LessThan simplex_complement_def simplices_def by auto

lemma
  simplice_complement:
  assumes "x \<in> simplices"
  obtains vx where "x = simplex_complement vx"
proof -
  have "simplex_complement (simplex_complement x) = x"
    using assms atLeast0LessThan simplex_complement_def simplices_def by auto
  then show ?thesis
    using that by blast 
qed

text\<open>We define the complement or the ``no faces'' of a simplicial complex
  as the simplices in @{term "{..n::nat}"} that are not in the simplicial 
  complex. Note that the set obtained is not a simplicial complex (except 
  for particular cases such as the empty set or the total set).\<close>

definition nofaces_simplicial_complex
  where "nofaces_simplicial_complex s = {v. v \<in> simplices \<and> v \<notin> s}"

lemma simpl_compl_not_in [simp]:
  assumes "v \<in> nofaces_simplicial_complex s" 
  shows "v \<notin> s"
  using assms nofaces_simplicial_complex_def by fastforce

lemma simpl_compl_simplice [simp]:
  assumes "v \<in> nofaces_simplicial_complex s" 
  shows "v \<in> simplices"
  by (metis (no_types, lifting) assms mem_Collect_eq nofaces_simplicial_complex_def)

definition Alexander_dual
  where "Alexander_dual s = 
            {v. \<exists>x. v = simplex_complement x \<and> x \<in> nofaces_simplicial_complex s}"

lemma Alexander_dual_empty: "Alexander_dual {} = Pow {..<n}"
  unfolding Alexander_dual_def
  unfolding nofaces_simplicial_complex_def
  unfolding simplex_complement_def
  unfolding simplices_def
  by auto

subsection\<open>The Alexander dual of a simplicial complex is a simplicial complex\<close>

lemma
  simplicial_complex_Alexander_dual:
  assumes "simplicial_complex s"
  shows "simplicial_complex (Alexander_dual s)"
proof (unfold simplicial_complex_def, standard, intro conjI)
  fix \<sigma> :: "nat set"
  assume sigma: "\<sigma> \<in> Alexander_dual s"
  show sigma_simplice: "\<sigma> \<in> simplices"
    using sigma unfolding Alexander_dual_def using simplex_complement_simplex [OF ]
    by fastforce
  show "Pow \<sigma> \<subseteq> Alexander_dual s"
  proof
    fix x :: "nat set"
    assume x: "x \<in> Pow \<sigma>"
    show "x \<in> Alexander_dual s"
    proof (rule ccontr)
      assume xnin: "x \<notin> Alexander_dual s"
      from x have x_in_sigma: "x \<subseteq> \<sigma>" and x_simplice: "x \<in> simplices" 
        using sigma_simplice
        apply simp
        using sigma_simplice simplices_def x by force
      from sigma obtain v
        where sigma_complement: "\<sigma> = simplex_complement v" 
          and v_noface: "v \<in> nofaces_simplicial_complex s"
        unfolding Alexander_dual_def by auto
      from x_simplice
      obtain vx where x_complement: "x = simplex_complement vx" and vx_simplice: "vx \<in> simplices"
        using simplice_complement [OF x_simplice]
        using simplex_complement_simplex [OF x_simplice]
        by (metis PowD Pow_top atLeast0LessThan double_diff simplex_complement_def simplices_def)
      show False
      proof (cases "vx \<in> nofaces_simplicial_complex s")
        case True
        hence "x \<in> Alexander_dual s" using x_complement unfolding Alexander_dual_def by auto
        thus ?thesis using xnin by contradiction
      next
        case False
        hence vx_in_s: "vx \<in> s"
          by (metis (mono_tags, lifting) mem_Collect_eq nofaces_simplicial_complex_def vx_simplice) 
        have "v \<subseteq> vx"
          using sigma_complement x_complement x_in_sigma
          by (smt (verit, ccfv_threshold) Diff_iff PowD atLeast0LessThan simplices_def simplicial_complex.simpl_compl_simplice simplicial_complex.simplex_complement_def subset_eq v_noface)
        hence "v \<in> s" using assms vx_in_s unfolding simplicial_complex_def by auto
        thus ?thesis using v_noface by simp
      qed
    qed
  qed
qed

end

section\<open>Definition of the Alexander dual of a Boolean function\<close>

context boolean_functions
begin

text\<open>The notion of @{const simplicial_complex.nofaces_simplicial_complex} 
  in simplicial complexes becomes now in boolean functions just the 
  @{const HOL.Not} boolean operator.\<close>

(*definition nofaces_boolean_function
  where "nofaces_boolean_function f = {b. b \<in> carrier_vec n \<and> \<not> f b}"

lemma nofaces_not [simp]:
  assumes "b \<in> nofaces_boolean_function f"
  shows "\<not> f b"
  using assms nofaces_boolean_function_def by fastforce

lemma nofaces_carrier_vec [simp]:
  assumes "b \<in> nofaces_boolean_function f"
  shows "b \<in> carrier_vec n"
  using assms nofaces_boolean_function_def by auto

lemma "nofaces_boolean_function f \<union> {b. b \<in> carrier_vec n \<and> f b} 
  = carrier_vec n"
  unfolding nofaces_boolean_function_def by auto*)

text\<open>The notion of @{const simplicial_complex.simplex_complement}
  becomes now in boolean functions the negation, or the complement in base 
  @{term "2::nat"}, of each @{typ "bool vec"}.}\<close>

definition not :: "bool vec \<Rightarrow> bool vec"  (*"\<not> _" [20] 20*)
  where "not v = vec (dim_vec v) (\<lambda>n. \<not> v $ n)"

lemma
  dim_vec_not:
  assumes d: "dim_vec v = k"
  shows "dim_vec (not v) = k"
  using d unfolding not_def by simp

lemma
  assumes d: "k < dim_vec v"
  shows "v $ k \<longleftrightarrow> \<not> (not v $ k)"
  using d unfolding not_def by simp

lemma
  not_v_in_carrier:
  assumes "v \<in> carrier_vec k"
  shows "not v \<in> carrier_vec k"
  using assms not_def by fastforce

lemma
  assumes d: "k < dim_vec v"
  shows "\<not> v $ k \<longleftrightarrow> (not v $ k)"
  using d unfolding not_def by simp

text\<open>The operation @{const not} is ``antimonotone'', in the sense that
  for every @{term x}, @{term y} such that @{term "x \<le> y"}, 
  then @{term "not y \<le> not x"}.\<close>

lemma
  not_vec_antimono: 
  assumes rs: "r \<le> s"
  shows "not s \<le> not r"
  using rs 
  unfolding not_def
  unfolding less_eq_vec_def by auto

text\<open>The operation @{const HOL.Not} is ``antimonotone'', in the sense that
  for every @{term x}, @{term y} such that @{term "x \<le> y"},
  and @{term f} such that @{term "monotone_bool_fun f"},
  then @{term "HOL.Not (f y) \<le> HOL.Not (f x)"}.\<close>

lemma
  not_antimono:
  assumes m: "monotone_bool_fun f"
  and x: "x \<in> carrier_vec n" and y: "y \<in> carrier_vec n"
  and xy: "x \<le> y"
  shows "(\<not> f y) \<le> (\<not> f x)"
  by (metis (mono_tags, hide_lams) le_boolE le_boolI' m mono_on_def monotone_bool_fun_def x xy y)

text\<open>The definition of the Alexander dual now for a Boolean function @{term f}
  becomes just the negation of @{term f} over the ``complement'' of every vector.\<close>

definition "Alexander_dual f = (\<lambda>x. \<not> f (not x))"

lemma Alexander_dual_False: 
  "boolean_functions.Alexander_dual (\<lambda>x. False) =
   (\<lambda>x. True)"
  unfolding Alexander_dual_def 
  by simp

subsection\<open>The Alexander dual of a \emph{monotone} Boolean function 
  is a \emph{monotone} Boolean function\<close>

lemma
  monotone_boolean_function_Alexander_dual:
  assumes f: "monotone_bool_fun f"
  shows "monotone_bool_fun (Alexander_dual f)"
proof (unfold monotone_bool_fun_def, unfold mono_on_def, intro allI, safe)
  fix r s :: "bool vec"
  assume r: "r \<in> carrier_vec n" and s: "s \<in> carrier_vec n" and r_le_s: "r \<le> s"
  have nr: "not r \<in> carrier_vec n" and ns: "not s \<in> carrier_vec n" and ns_le_nr: "not s \<le> not r"
    using not_v_in_carrier [OF r]
        and not_v_in_carrier [OF s] 
        and not_vec_antimono [OF r_le_s] by simp_all
  show "Alexander_dual f r \<le> Alexander_dual f s"
    unfolding Alexander_dual_def using not_antimono [OF f ns nr ns_le_nr] by simp
qed

end

lemmas [code] = boolean_functions.not_def boolean_functions.Alexander_dual_def

end