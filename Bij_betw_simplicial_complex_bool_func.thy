
theory Bij_betw_simplicial_complex_bool_func
  imports 
    Simplicial_complex
    Alexander
begin

section\<open>Bijection between simplicial complexes and monotone Boolean functions\<close>

context simplicial_complex
begin

lemma ceros_of_boolean_input_in_set:
  assumes s: "\<sigma> \<in> simplices"
  shows "ceros_of_boolean_input (vec n (\<lambda>i. i \<notin> \<sigma>)) = \<sigma>"
  unfolding ceros_of_boolean_input_def using s unfolding simplices_def by auto

lemma
  assumes sigma: "\<sigma> \<in> simplices"
  and nempty: "\<sigma> \<noteq> {}"
  shows "Max \<sigma> < n"
proof -
  have "Max \<sigma> \<in> \<sigma>" using linorder_class.Max_in [OF finite_simplex [OF sigma] nempty] .
  thus ?thesis using sigma unfolding simplices_def by auto
qed

definition bool_vec_from_simplice :: "nat set => (bool vec)"
  where "bool_vec_from_simplice \<sigma> = vec n (\<lambda>i. i \<notin> \<sigma>)"

lemma [simp]:
  assumes "\<sigma> \<in> simplices"
  shows "ceros_of_boolean_input (bool_vec_from_simplice \<sigma>) = \<sigma>"
  unfolding bool_vec_from_simplice_def
  unfolding ceros_of_boolean_input_def
  unfolding dim_vec
  using assms unfolding simplices_def by auto

lemma [simp]:
  assumes n: "dim_vec f = n"
  shows "bool_vec_from_simplice (ceros_of_boolean_input f) = f"
  unfolding bool_vec_from_simplice_def
  unfolding ceros_of_boolean_input_def
  using n by auto

lemma "bool_vec_from_simplice {0} = vec n (\<lambda>i. i \<notin> {0})"
  unfolding bool_vec_from_simplice_def by auto

lemma "bool_vec_from_simplice {1,2} = 
    vec n (\<lambda>i. i \<notin> {1,2})"
  unfolding bool_vec_from_simplice_def by auto

lemma simplicial_complex_implies_true: 
  assumes "\<sigma> \<in> simplicial_complex_induced_by_monotone_boolean_function n f"
  shows "f (bool_vec_from_simplice \<sigma>)"
  unfolding bool_vec_from_simplice_def
  using assms
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  unfolding ceros_of_boolean_input_def 
  apply auto
  by (smt (verit, best) dim_vec eq_vecI index_vec)

definition bool_vec_set_from_simplice_set :: "nat set set => (bool vec) set"
  where "bool_vec_set_from_simplice_set K =
     {\<sigma>. (dim_vec \<sigma> = n) \<and> (\<exists>k\<in>K. \<sigma> = bool_vec_from_simplice k)}"

definition boolean_function_from_simplicial_complex :: "nat set set => (bool vec => bool)"
  where "boolean_function_from_simplicial_complex K = 
          (\<lambda>x. x \<in> (bool_vec_set_from_simplice_set K))"

lemma "Collect (boolean_function_from_simplicial_complex K) = (bool_vec_set_from_simplice_set K)"
  unfolding boolean_function_from_simplicial_complex_def by simp

text\<open>The Boolean function induced by a simplicial complex is monotone.
  This result is proven in Scoville as part of the proof of Proposition 6.16.
  The opposite direction has been proven as 
  @{thm monotone_bool_fun_induces_simplicial_complex}.\<close>

lemma
  simplicial_complex_induces_monotone_bool_fun:
  assumes mon: "simplicial_complex (K::nat set set)"
  shows "boolean_functions.monotone_bool_fun n (boolean_function_from_simplicial_complex K)"
proof (unfold boolean_functions.monotone_bool_fun_def)
  show "mono_on (boolean_function_from_simplicial_complex K) (carrier_vec n)"
  proof (intro mono_onI)
  fix r and s::"bool vec"
  assume r_le_s: "r \<le> s"
  show "boolean_function_from_simplicial_complex K r 
        \<le> boolean_function_from_simplicial_complex K s"
  proof (cases "boolean_function_from_simplicial_complex K r")
    case False then show ?thesis by simp
  next
    case True
    have ce: "ceros_of_boolean_input s \<subseteq> ceros_of_boolean_input r"
      using monotone_ceros_of_boolean_input [OF r_le_s] .
    from True obtain k where r_def: "r = vec n (\<lambda>i. i \<notin> k)"
      and k: "k \<in> K"
      unfolding boolean_function_from_simplicial_complex_def
      unfolding bool_vec_set_from_simplice_set_def
      unfolding bool_vec_from_simplice_def by auto
    have r_in_K: "ceros_of_boolean_input r \<in> K" 
      using k mon
      unfolding r_def
      unfolding ceros_of_boolean_input_def
      unfolding dim_vec
      using simplicial_complex_def [of K] by fastforce
    have "boolean_function_from_simplicial_complex K s"
    proof (unfold boolean_function_from_simplicial_complex_def 
        bool_vec_set_from_simplice_set_def, rule, rule conjI)
      show "dim_vec s = n"
        by (metis less_eq_vec_def dim_vec r_def r_le_s)
      show "\<exists>k\<in>K. s = bool_vec_from_simplice k"
        proof (rule bexI [of _ "ceros_of_boolean_input s"], unfold bool_vec_from_simplice_def)
          show "ceros_of_boolean_input s \<in> K"
            using simplicial_complex_monotone [OF mon r_in_K ce] .
          show "s = vec n (\<lambda>i. i \<notin> ceros_of_boolean_input s)"
            using ce unfolding ceros_of_boolean_input_def
            using r_le_s
            unfolding less_eq_vec_def
            unfolding r_def
            unfolding dim_vec by auto
        qed
      qed
     thus ?thesis by simp
   qed
 qed
qed

lemma shows "(simplicial_complex_induced_by_monotone_boolean_function n) \<in> 
          boolean_functions.monotone_bool_fun_set n
          \<rightarrow> (simplicial_complex_set::nat set set set)"
proof
  fix x::"bool vec \<Rightarrow> bool"
  assume x: "x \<in> boolean_functions.monotone_bool_fun_set n"
  show "simplicial_complex_induced_by_monotone_boolean_function n x \<in> simplicial_complex_set"
    using monotone_bool_fun_induces_simplicial_complex [of x] x
    unfolding boolean_functions.monotone_bool_fun_set_def
    unfolding boolean_functions.monotone_bool_fun_def simplicial_complex_set_def
    by auto
qed

lemma shows "boolean_function_from_simplicial_complex 
          \<in> (simplicial_complex_set::nat set set set) 
          \<rightarrow> boolean_functions.monotone_bool_fun_set n"
proof
  fix x::"nat set set" assume x: "x \<in> simplicial_complex_set"
  show "boolean_function_from_simplicial_complex x \<in> boolean_functions.monotone_bool_fun_set n"
    using simplicial_complex_induces_monotone_bool_fun [of x]
    unfolding boolean_functions.monotone_bool_fun_set_def
    unfolding boolean_functions.monotone_bool_fun_def
    using x unfolding simplicial_complex_set_def
    unfolding mem_Collect_eq by fast
qed

text\<open>Given a Boolean function @{term f}, if we build its associated 
  simplicial complex and then the associated Boolean function,
  we obtain @{term f}.

  The result holds for every Boolean function @{term f}
  (the premise on @{term f} being monotone can be omitted,
  but then the set defined by the boolean function @{term f}
  will no longer satisfy the definition of simplicial complex).\<close>

lemma
  boolean_function_from_simplicial_complex_simplicial_complex_induced_by_monotone_boolean_function:
  fixes f :: "bool vec \<Rightarrow> bool"
  assumes dim: "v \<in> carrier_vec n"
  shows "boolean_function_from_simplicial_complex 
    (simplicial_complex_induced_by_monotone_boolean_function n f) v = f v"
proof (intro iffI)
  assume xb: "f v"
  show bf: "boolean_function_from_simplicial_complex 
      (simplicial_complex_induced_by_monotone_boolean_function n f) v"
  proof -
   have "f v \<and> v = bool_vec_from_simplice (ceros_of_boolean_input v)"
    unfolding ceros_of_boolean_input_def
    unfolding bool_vec_from_simplice_def
    using xb dim unfolding carrier_vec_def by auto
   then show ?thesis
    unfolding simplicial_complex_induced_by_monotone_boolean_function_def
    unfolding boolean_function_from_simplicial_complex_def 
    unfolding bool_vec_set_from_simplice_set_def
    unfolding mem_Collect_eq
    using dim unfolding carrier_vec_def by blast
   qed
next
  assume "boolean_function_from_simplicial_complex 
      (simplicial_complex_induced_by_monotone_boolean_function n f) v"
  then show "f v"
    unfolding simplicial_complex_induced_by_monotone_boolean_function_def
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def
    unfolding mem_Collect_eq
    using \<open>boolean_function_from_simplicial_complex 
      (simplicial_complex_induced_by_monotone_boolean_function n f) v\<close> 
      boolean_function_from_simplicial_complex_def 
      simplicial_complex.bool_vec_set_from_simplice_set_def 
      simplicial_complex_implies_true by fastforce
qed

text\<open>Given a simplicial complex @{term K}, if we build its associated 
  Boolean function, and then the associated simplicial complex,
  we obtain @{term K}.\<close>

lemma
  simplicial_complex_induced_by_monotone_boolean_function_boolean_function_from_simplicial_complex:
  fixes K :: "nat set set"
  assumes K: "simplicial_complex K"
  shows "simplicial_complex_induced_by_monotone_boolean_function n 
    (boolean_function_from_simplicial_complex K) = K"
proof (intro equalityI)
  show "simplicial_complex_induced_by_monotone_boolean_function n 
    (boolean_function_from_simplicial_complex K) \<subseteq> K"
  proof
    fix x :: "nat set"
    assume x: "x \<in> simplicial_complex_induced_by_monotone_boolean_function
              n (boolean_function_from_simplicial_complex K)"
    show "x \<in> K"
      using x
      unfolding boolean_function_from_simplicial_complex_def
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding bool_vec_from_simplice_def bool_vec_set_from_simplice_set_def
      using K
      unfolding simplicial_complex_def simplices_def
      by auto (metis assms bool_vec_from_simplice_def 
          ceros_of_boolean_input_in_set simplicial_complex_def)
  qed
next
  show "K \<subseteq> simplicial_complex_induced_by_monotone_boolean_function n 
            (boolean_function_from_simplicial_complex K)"
 proof
   fix x :: "nat set"
   assume "x \<in> K" 
   hence x: "x \<in> simplices" using K unfolding simplicial_complex_def by simp
   have bvs: "ceros_of_boolean_input (bool_vec_from_simplice x) = x"
     unfolding one_bool_def
     unfolding bool_vec_from_simplice_def
     using ceros_of_boolean_input_in_set [OF x] .
   show "x \<in> simplicial_complex_induced_by_monotone_boolean_function n 
          (boolean_function_from_simplicial_complex K)"
     unfolding boolean_function_from_simplicial_complex_def
     unfolding simplicial_complex_induced_by_monotone_boolean_function_def
     unfolding bool_vec_from_simplice_def bool_vec_set_from_simplice_set_def
     using x bool_vec_from_simplice_def bvs
     by (metis (mono_tags, lifting) \<open>x \<in> K\<close> dim_vec mem_Collect_eq)
 qed
qed

end

section\<open>Equivalence of the Alexander dual definition for Boolean functions 
  and simplicial complexes\<close>

context simplicial_complex
begin

lemma conjI3: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> A \<and> B \<and> C"
  by simp

lemma
  simplicial_complex_Alexander_dual_equals:
  shows "simplicial_complex_induced_by_monotone_boolean_function n (boolean_functions.Alexander_dual f)
    = Alexander_dual (simplicial_complex_induced_by_monotone_boolean_function n f)"
  unfolding simplicial_complex_induced_by_monotone_boolean_function_def
  unfolding Alexander_dual_def
  unfolding boolean_functions.Alexander_dual_def
  unfolding boolean_functions.not_def
  unfolding ceros_of_boolean_input_def
  unfolding simplex_complement_def
  unfolding nofaces_simplicial_complex_def
  unfolding simplices_def proof standard
  show "{y. \<exists>x. dim_vec x = n \<and>
            \<not> f (vec (dim_vec x) (\<lambda>n. \<not> x $ n)) \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}
    \<subseteq> {univ_n - x |x.
        x \<in> {v \<in> Pow {0..<n}.
              v \<notin> {y. \<exists>x. dim_vec x = n \<and> f x \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}}}"
  proof (rule subsetI)
    fix x :: "nat set"
    assume x: "x \<in> {y. \<exists>x. dim_vec x = n \<and> \<not> f (vec (dim_vec x) (\<lambda>n. \<not> x $ n)) \<and>
                     {xa. xa < dim_vec x \<and> x $ xa = False} = y} "
    from x obtain x':: "bool vec" where dx': "dim_vec x' = n" 
          and notfx': "\<not> f (vec (dim_vec x') (\<lambda>n. \<not> x' $ n))"
          and x_n_x': "{xa. xa < dim_vec x' \<and> x' $ xa = False} = x" by auto
    show "x \<in> {univ_n - x |x. x \<in> {v \<in> Pow {0..<n}.
        v \<notin> {y. \<exists>x. dim_vec x = n \<and> f x \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}}}"
    proof (rule CollectI,
            rule exI [of _ "(ceros_of_boolean_input (boolean_functions.not x'))"],
              rule conjI)
        show "x = univ_n - (ceros_of_boolean_input (boolean_functions.not x'))"
          using x_n_x' dx'
          unfolding boolean_functions.not_def
          unfolding ceros_of_boolean_input_def by auto
        show "(ceros_of_boolean_input (boolean_functions.not x')) \<in> {v \<in> Pow {0..<n}.
                v \<notin> {y. \<exists>x. dim_vec x = n \<and> f x \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}}"
          using x_n_x' dx'
          unfolding boolean_functions.not_def
          unfolding ceros_of_boolean_input_def apply simp apply (intro conjI)
           apply auto[1]
          by (smt (verit) dim_vec eq_vecI mem_Collect_eq notfx')
      qed
    qed
  next
    show "{univ_n - x |x.
            x \<in> {v \<in> Pow {0..<n}.
           v \<notin> {y. \<exists>x. dim_vec x = n \<and> f x \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}}}
        \<subseteq> {y. \<exists>x. dim_vec x = n \<and>
               \<not> f (vec (dim_vec x) (\<lambda>n. \<not> x $ n)) \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}"
    proof (rule subsetI)
      fix x :: "nat set"
      assume x: "x \<in> {univ_n - x |x.
              x \<in> {v \<in> Pow {0..<n}.
                    v \<notin> {y. \<exists>x. dim_vec x = n \<and>
                                 f x \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}}}"
      then obtain x' where x'_def: "x = univ_n - x'"
                      and x'_complement: "simplex_complement x' = x"
                      and x'_simplice: "x' \<in> Pow {0..<n}" 
                      and x'_compliment: "x' \<notin> {y. \<exists>x. dim_vec x = n \<and>
                                 f x \<and> {xa. xa < dim_vec x \<and> x $ xa = False} = y}" 
            unfolding simplex_complement_def
        by auto
      show "x \<in> {y. \<exists>x. dim_vec x = n \<and>
                      \<not> f (vec (dim_vec x) (\<lambda>n. \<not> x $ n)) \<and>
                      {xa. xa < dim_vec x \<and> x $ xa = False} = y}"
      proof (rule CollectI,
              rule exI [of _ "(bool_vec_from_simplice (simplex_complement x'))"],
                rule conjI3)
        show "dim_vec (bool_vec_from_simplice (simplex_complement x')) = n"
          by (metis dim_vec simplicial_complex.bool_vec_from_simplice_def)
        show "\<not> f (vec (dim_vec (bool_vec_from_simplice (simplex_complement x')))
           (\<lambda>n. \<not> bool_vec_from_simplice (simplex_complement x') $ n))"
          unfolding x'_complement using x
          unfolding bool_vec_from_simplice_def
          unfolding dim_vec by fastforce
        show "{xa. xa < dim_vec (bool_vec_from_simplice (simplex_complement x')) \<and>
                bool_vec_from_simplice (simplex_complement x') $ xa = False} = x"
          using x'_complement x'_simplice
          unfolding bool_vec_from_simplice_def
          unfolding ceros_of_boolean_input_def 
          unfolding simplex_complement_def
          using simplex_complement_simplex
          using ceros_of_boolean_input_in_set by auto
     qed
  qed
qed

lemma
  not_bool_vec_impl_not_simpl_compl:
  assumes v: "v \<in> carrier_vec n"
    and v_notin: "boolean_functions.not v \<notin> bool_vec_set_from_simplice_set s"
  shows "simplex_complement (ceros_of_boolean_input v) \<notin> s"
  using v v_notin
  unfolding bool_vec_set_from_simplice_set_def
  unfolding bool_vec_from_simplice_def
  unfolding ceros_of_boolean_input_def
  unfolding simplex_complement_def 
  using boolean_functions.dim_vec_not [OF carrier_vecD [OF v]] carrier_vecD [OF v]
  using boolean_functions.not_def [of v] 
  by auto (fastforce)

lemma
  boolean_function_Alexander_dual_equals:
  assumes s: "simplicial_complex s"
  and v: "v \<in> carrier_vec n"
  shows "boolean_functions.Alexander_dual (boolean_function_from_simplicial_complex s) v
    = boolean_function_from_simplicial_complex (Alexander_dual s) v"
proof (cases "s = {}")
case True
  show ?thesis
    unfolding True
    unfolding boolean_functions.Alexander_dual_def
    unfolding Alexander_dual_def
    unfolding boolean_function_from_simplicial_complex_def 
    unfolding boolean_functions.not_def
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def
    unfolding bool_vec_from_simplice_def
    unfolding ceros_of_boolean_input_def
    unfolding simplex_complement_def
    unfolding nofaces_simplicial_complex_def
    unfolding simplices_def
    unfolding carrier_vecD [OF v] 
  proof (standard, safe, simp_all add: carrier_vecD [OF v])
    show "\<exists>k. (\<exists>x. k = univ_n - x \<and> x \<subseteq> {0..<n}) \<and> v = vec n (\<lambda>i. i \<notin> k)"
    proof (rule exI [of _ "(ceros_of_boolean_input v)"], rule conjI,
        rule exI [of _ "simplex_complement (ceros_of_boolean_input v)"], rule conjI)
      show "ceros_of_boolean_input v = univ_n - simplex_complement (ceros_of_boolean_input v)"
        by (metis simplex_complement_def 
            simplicial_complex.simplex_complement_idempotent v vec_in_simplices)
      show "simplex_complement (ceros_of_boolean_input v) \<subseteq> {0..<n}"
        by (metis PowD simplex_complement_simplex simplices_def v vec_in_simplices)
      show "v = vec n (\<lambda>i. i \<notin> ceros_of_boolean_input v)"
        using v unfolding ceros_of_boolean_input_def by auto
    qed
  qed
  next
  case False
  note s_nempty = False
  show ?thesis
  proof
  assume A: "boolean_functions.Alexander_dual (boolean_function_from_simplicial_complex s) v"
  from A have v_nin_s: "boolean_functions.not v \<notin> bool_vec_set_from_simplice_set s"
    unfolding boolean_functions.Alexander_dual_def
    unfolding boolean_function_from_simplicial_complex_def .
  from v_nin_s have simp_compl_v_notin: "simplex_complement (ceros_of_boolean_input v) \<notin> s"
    using not_bool_vec_impl_not_simpl_compl [OF v, of s] by fast
  from A and v and s_nempty obtain k 
    where ks: "k \<in> s" and v_ne_k: "(\<lambda>n. \<not> v $ n) \<noteq> (\<lambda>i. i \<notin> k)"
     unfolding boolean_functions.Alexander_dual_def
     unfolding boolean_functions.not_def
     unfolding boolean_function_from_simplicial_complex_def
     unfolding bool_vec_set_from_simplice_set_def
     unfolding bool_vec_from_simplice_def
     unfolding ceros_of_boolean_input_def
     by fastforce
  show "boolean_function_from_simplicial_complex (Alexander_dual s) v"
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def
    unfolding bool_vec_from_simplice_def
    unfolding Alexander_dual_def
   proof (rule CollectI, rule conjI)
    show "dim_vec v = n" using v by simp
    show "\<exists>k\<in>{simplex_complement x |x. x \<in> nofaces_simplicial_complex s}. 
               v = vec n (\<lambda>i. i \<notin> k)"
    proof (rule bexI [of _ "(ceros_of_boolean_input v)"])
     show "v = vec n (\<lambda>i. i \<notin> (ceros_of_boolean_input v))"
     proof (intro eq_vecI)
      show "dim_vec v = dim_vec (vec n (\<lambda>i. i \<notin> (ceros_of_boolean_input v)))"
       using v by simp
       fix i
       assume "i < dim_vec (vec n (\<lambda>i. i \<notin> (ceros_of_boolean_input v)))"
       hence iln: "i < n" using v by simp
       have "(vec_index v) i = (\<lambda>i. i \<notin> (ceros_of_boolean_input v)) i"
        unfolding ceros_of_boolean_input_def
        using iln v by auto
       then show "v $ i = vec n (\<lambda>i. i \<notin> (ceros_of_boolean_input v)) $ i"
        by (metis iln index_vec)
       qed
       show "ceros_of_boolean_input v 
            \<in> {simplex_complement x |x. x \<in> nofaces_simplicial_complex s}"
       proof (rule CollectI, 
              rule exI [of _ "simplex_complement (ceros_of_boolean_input v)"], rule conjI)
       show "ceros_of_boolean_input v =
         simplex_complement (simplex_complement (ceros_of_boolean_input v))"
         using simplex_complement_idempotent [
             OF simplicial_complex.vec_in_simplices [OF v]] .
        show "simplex_complement (ceros_of_boolean_input v) \<in> nofaces_simplicial_complex s"
         unfolding simplex_complement_def
         unfolding ceros_of_boolean_input_def
         unfolding nofaces_simplicial_complex_def
         unfolding simplices_def 
         using ks v_ne_k simp_compl_v_notin 
         unfolding ceros_of_boolean_input_def 
         unfolding simp_compl_v_notin simplex_complement_def by auto
        qed
      qed
    qed
  next
  assume A: "boolean_function_from_simplicial_complex (Alexander_dual s) v"
  from A obtain k where k: "k \<in> {simplex_complement x |x. x \<in> nofaces_simplicial_complex s}"
               and v_eq_k: "v = bool_vec_from_simplice k"
    unfolding Alexander_dual_def
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def by blast
  from v_eq_k have vec_index_eq_k: "\<And>j. j < n \<Longrightarrow> (\<lambda>i. v $ i) j = (\<lambda>i. i \<notin> k) j"
    by (metis index_vec simplicial_complex.bool_vec_from_simplice_def v_eq_k)
  from k and v_eq_k obtain x where k_sc: "k = simplex_complement x"
    and x_noface: "x \<in> nofaces_simplicial_complex s"
    and v_bool_vec_sc: "v = bool_vec_from_simplice (simplex_complement x)"
    by blast
  show "boolean_functions.Alexander_dual (boolean_function_from_simplicial_complex s) v"
    unfolding boolean_function_from_simplicial_complex_def
    unfolding bool_vec_set_from_simplice_set_def
    unfolding bool_vec_from_simplice_def
    unfolding boolean_functions.Alexander_dual_def
    unfolding boolean_functions.not_def
  proof (standard, safe)
    fix l
    assume "n = dim_vec (vec (dim_vec v) (\<lambda>n. \<not> v $ n))"
         and lins: "l \<in> s"
         and  "vec (dim_vec v) (\<lambda>n. \<not> v $ n) =
          vec (dim_vec (vec (dim_vec v) (\<lambda>n. \<not> v $ n))) (\<lambda>i. i \<notin> l)"
    hence vec_eq: "vec n (\<lambda>n. \<not> v $ n) = vec n (\<lambda>i. i \<notin> l)" using v by simp
    hence vec_index_eq_l: "\<And>j. j < n \<Longrightarrow> (\<lambda>n. \<not> v $ n) j = (\<lambda>i. i \<notin> l) j"
      by (metis index_vec)
    show False
      using vec_index_eq_l
      using vec_index_eq_k using k using lins
      by (metis DiffE Pow_iff k_sc lessThan_iff s simpl_compl_not_in simpl_compl_simplice simplex_complement_def simplice_complement simplicial_complex.simplicial_complex_def subsetD subsetI x_noface)
  qed
 qed
qed

end

end