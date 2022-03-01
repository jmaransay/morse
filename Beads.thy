
theory Beads
  imports 
    Boolean_functions
    Simplicial_complex
    Bij_betw_simplicial_complex_bool_func
    Evasive
begin

definition first_half :: "bool vec \<Rightarrow> bool vec"
  where "first_half v = vec ((dim_vec v) div 2) (\<lambda> i. (v $ i))"

definition second_half :: "bool vec \<Rightarrow> bool vec"
  where "second_half v = vec ((dim_vec v) div 2) (\<lambda> i. (v $ (i + ((dim_vec v) div 2))))"

definition bead :: "bool vec => bool"
  where "bead v = (first_half v \<noteq> second_half v)"

lemma "bead (vec 8 (\<lambda>x. if x = 0 then True else False))"
(is "bead ?v")
proof -
  have "first_half ?v $ 0 = True"
    unfolding bead_def
    unfolding first_half_def by simp
  moreover have "second_half ?v $ 0 = False"
    unfolding bead_def
    unfolding second_half_def by simp
  ultimately show ?thesis unfolding bead_def by metis
qed

lemma "\<not> bead (vec 4 (\<lambda>x. True))"
  unfolding bead_def
  unfolding first_half_def
  unfolding second_half_def
  unfolding dim_vec
  by auto

lemma "\<not> bead (vec 8 (\<lambda>x. if x mod 2 = 0 then True else False))"
  unfolding bead_def
  unfolding first_half_def
  unfolding second_half_def
  unfolding dim_vec by (auto) fastforce

lemma
  \<open>0b0000000000000000000011 = 3\<close> (*binary*)
  \<open>0x0000F = 15\<close> (*hexa*)
  by simp_all

definition nat_to_bool_vec :: "nat \<Rightarrow> nat \<Rightarrow> bool vec"
  where "nat_to_bool_vec n k = vec n (\<lambda>i. bit k i)"

text\<open>The following function behaves similarly to the previous one, but
  it generates a list. In principle, we will use it just for testing.
  Do note that the elements in the list are placed in ``reverse order''
  with respect to the usual representation of binary strings 
  (is this Big Endian?), but in the same indexes as in @{term nat_to_bool_vec}}.\<close>

definition nat_to_bool_list :: "nat \<Rightarrow> nat \<Rightarrow> bool list"
  where "nat_to_bool_list n k = map (\<lambda>i. bit k i) [0..<n]"

value "nat_to_bool_vec 8 5 $ 0 = True"

value "nat_to_bool_vec 8 5 $ 1 = False"

value "nat_to_bool_vec 8 5 $ 2 = True"

value "nat_to_bool_vec 8 5 $ 3 = False"

value "nat_to_bool_list 8 5"

value "nat_to_bool_vec 8 1 $ 0 = False"

value "nat_to_bool_vec 8 4 $ 0 = False"

value "nat_to_bool_vec 8 2 $ 0 = False"

text\<open>The following function produces the output of a Boolean 
  function of dimension @{term "n::nat"}.\<close>

definition boolean_function_to_bool_vec 
  :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> bool vec"
  where "boolean_function_to_bool_vec n f = 
      vec n (\<lambda>i. f (nat_to_bool_vec n i))"

(*text\<open>The following function is similar to the previous one but it
  produces a list. For the moment just being used for testing purposes.\<close>

definition boolean_function_to_bool_list
  :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> bool list"
  where "boolean_function_to_bool_list n f = 
      map (\<lambda>i. f (nat_to_bool_vec n i)) [0..<n]"*)

text\<open>The following computation now produces the truth table for
  the threshold function of order @{term 1} in size @{term 8}, 
  \emph{i.e.}, a Boolean function in @{term 3} variables. 
  The Boolean function is true whenever one or more variables are true.\<close>

value "list_of_vec (boolean_function_to_bool_vec 8 (bool_fun_threshold 1))"

text\<open>The following computation now produces the truth table for
  the threshold function of order @{term 2} in size @{term 8}, 
  \emph{i.e.}, a Boolean function in @{term 3} variables. 
  The Boolean function is true whenever two or more variables are true.\<close>

value "list_of_vec (boolean_function_to_bool_vec 8 (bool_fun_threshold 2))"

text\<open>The following computation now produces the truth table for
  the threshold function of order @{term 3} in size @{term 8}, 
  \emph{i.e.}, a Boolean function in @{term 3} variables.
  The Boolean function is true iff the three variables are true.\<close>

value "list_of_vec (boolean_function_to_bool_vec 8 (bool_fun_threshold 3))"

text\<open>The following computation now produces the truth table for
  the threshold function of order @{term 2} in size @{term 16}, 
  \emph{i.e.}, a Boolean function in @{term 4} variables. 
  The Boolean function is true whenever two or more variables are true.\<close>

value "list_of_vec (boolean_function_to_bool_vec 16 (bool_fun_threshold 2))"

lemma "boolean_function_to_bool_vec 8 (\<lambda>x. True) = vec 8 (\<lambda>i. True)"
  unfolding boolean_function_to_bool_vec_def ..

text\<open>Following the notation in Knuth (BDDs), we compute the subfunctions of
  a Boolean function. Knuth uses subfunctions in index @{term "0::nat"},
  but we prefer to define them in general, for every possible index 
  @{term "i::nat"}.\<close>

definition subfunction_0 :: "(bool vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (bool vec \<Rightarrow> bool)"
  where "subfunction_0 f n = (\<lambda>x. f (vec (dim_vec x) (\<lambda>i. if i = n then False else x $ i)))"

definition subfunction_1 :: "(bool vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (bool vec \<Rightarrow> bool)"
  where "subfunction_1 f n = (\<lambda>x. f (vec (dim_vec x) (\<lambda>i.  if i = n then True else x $ i)))"

text\<open>The following definition represents the process
  of increasing a vector in one additional variable
  with a ``fixed'' value (either @{term True} or @{term False}.
  This operation will be later used to produce the subfunctions
  of a Boolean function.\<close>

definition vec_aug :: "bool vec \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool vec"
  where "vec_aug r k b = vec (dim_vec r + 1)
  (\<lambda>i. if i < k then r $ i else if i = k then b else r $ (i - 1))"

lemma vec_aug_in_carrier:
  assumes r: "r \<in> carrier_vec (m - 1)"  
    and m_g_0: "0 < m"
  shows "vec_aug r k b \<in> carrier_vec m"
    using r unfolding vec_aug_def carrier_vec_def
    using m_g_0 by force

definition vec_red :: "bool vec \<Rightarrow> nat \<Rightarrow> bool vec"
  where "vec_red r k = vec (dim_vec r - 1)
  (\<lambda>i. if i < k then r $ i else r $ (i + 1))"

lemma vec_red_in_carrier:
  assumes r: "r \<in> carrier_vec m"  
  shows "vec_red r k \<in> carrier_vec (m - 1)"
    using r unfolding vec_red_def carrier_vec_def by force

lemma "vec_red (vec_aug r k b) k = r"
  unfolding vec_red_def vec_aug_def dim_vec by auto

definition subfunction_0_dim :: "(bool vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (bool vec \<Rightarrow> bool)"
  where "subfunction_0_dim f k = (\<lambda>r. f (vec_aug r k False))"

definition subfunction_1_dim :: "(bool vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (bool vec \<Rightarrow> bool)"
  where "subfunction_1_dim f k = (\<lambda>r. f (vec_aug r k True))"

lemma
  assumes f: "f \<in> carrier_vec n \<rightarrow> UNIV"
  shows "(subfunction_0 f i) \<in> carrier_vec (n - 1) \<rightarrow> UNIV"
  using f unfolding carrier_vec_def subfunction_0_def
  by simp

lemma
  assumes f: "f \<in> carrier_vec n \<rightarrow> UNIV"
  shows "(subfunction_0_dim f i) \<in> carrier_vec (n - 1) \<rightarrow> UNIV"
  using f by simp

value "bool_fun_threshold 3 (vec_of_list [True, False, True, True])"

value "subfunction_0 (bool_fun_threshold 3) 0 (vec_of_list [True, False, True, True])"

value "subfunction_0_dim (bool_fun_threshold 3) 0 (vec_of_list [False, True, True])"

value "subfunction_1 (bool_fun_threshold 3) 0 (vec_of_list [True, False, True, True])"

value "subfunction_1_dim (bool_fun_threshold 3) 0 (vec_of_list [False, True, True])"

value "subfunction_0 (bool_fun_threshold 3) 1 (vec_of_list [True, False, True, True])"

value "subfunction_0_dim (bool_fun_threshold 3) 1 (vec_of_list [True, True, True])"

value "subfunction_1 (bool_fun_threshold 3) 1 (vec_of_list [True, False, True, True])"

value "subfunction_1_dim (bool_fun_threshold 3) 1 (vec_of_list [True, True, True])"

value "subfunction_0 (bool_fun_threshold 3) 2 (vec_of_list [True, False, True, True])"

value "subfunction_1 (bool_fun_threshold 3) 2 (vec_of_list [True, False, True, True])"

value "subfunction_0 (bool_fun_threshold 3) 3 (vec_of_list [True, False, True, True])"

value "subfunction_1 (bool_fun_threshold 3) 3 (vec_of_list [True, False, True, True])"

context boolean_functions
begin

text\<open>The following lemma states that @{term subfunction_0_dim} from a 
  monotone Boolean function in @{term m} variables produces another 
  monotone Boolean function but in @{term "m - 1"} variables. In fact,
  @{term subfunction_0_dim} is the operation ``LINK'' for simplicial complexes.\<close>

lemma
  subfunction_0_monotone:
  assumes m: "mono_on f (carrier_vec m)"
  and i_l_m: "i < m"
  shows "mono_on (subfunction_0_dim f i) (carrier_vec (m - 1))"
proof (unfold subfunction_0_dim_def mono_on_def, safe)
  fix r s :: "bool vec"
  assume r: "r \<in> carrier_vec (m - 1)" and s: "s \<in> carrier_vec (m - 1)" and r_le_s: "r \<le> s"
  have "vec_aug r i False \<in> carrier_vec m"
    and "vec_aug s i False \<in> carrier_vec m"
    using i_l_m r s vec_aug_in_carrier by blast+
  moreover have "vec_aug r i False \<le> vec_aug s i False"
  proof (unfold vec_aug_def less_eq_vec_def dim_vec, intro conjI)
    show dim_eq: "dim_vec r + 1 = dim_vec s + 1" using r s unfolding carrier_vec_def by simp
    show "\<forall>ia<dim_vec s + 1.
       vec (dim_vec r + 1)
        (\<lambda>ia. if ia < i then r $ ia else if ia = i then False else r $ (ia - 1)) $
       ia
       \<le> vec (dim_vec s + 1)
           (\<lambda>ia. if ia < i then s $ ia else if ia = i then False else s $ (ia - 1)) $
          ia"
    proof (intro allI, rule)
      fix ia
      assume ia: "ia < dim_vec s + 1"
      show " vec (dim_vec r + 1)
           (\<lambda>ia. if ia < i then r $ ia else if ia = i then False else r $ (ia - 1)) $
          ia
          \<le> vec (dim_vec s + 1)
              (\<lambda>ia. if ia < i then s $ ia else if ia = i then False else s $ (ia - 1)) $
             ia"
      proof (cases "ia = i")
        case True
        show ?thesis using ia dim_eq by (simp add: True)
      next
        case False
        note ia_ne_i = False 
        show ?thesis
        proof (cases "ia < i")
          case True
          show ?thesis
            using ia dim_eq r_le_s ia_ne_i True i_l_m unfolding less_eq_vec_def
            by auto (metis One_nat_def Suc_diff_Suc carrier_vecD diff_zero less_antisym not_less_eq plus_1_eq_Suc r trans_less_add1)
        next
          case False
          show ?thesis
            using ia dim_eq r_le_s ia_ne_i False i_l_m unfolding less_eq_vec_def
            by auto
        qed
      qed
    qed
  qed
  ultimately show "f (vec_aug r i False) \<le> f (vec_aug s i False)"
    using m unfolding mono_on_def by blast
qed

text\<open>The following lemma states that @{term subfunction_1_dim} from a 
  monotone Boolean function in @{term m} variables produces another 
  monotone Boolean function but in @{term "m - 1"} variables. In fact,
  this is the operation ``CONTRASTAR'' for simplicial complexes.\<close>

lemma
  subfunction_1_monotone:
  assumes m: "mono_on f (carrier_vec m)"
  and i_l_m: "i < m"
  shows "mono_on (subfunction_1_dim f i) (carrier_vec (m - 1))"
proof (unfold subfunction_1_dim_def mono_on_def, safe)
  fix r s :: "bool vec"
  assume r: "r \<in> carrier_vec (m - 1)" and s: "s \<in> carrier_vec (m - 1)" and r_le_s: "r \<le> s"
  have "vec_aug r i True \<in> carrier_vec m"
    and "vec_aug s i True \<in> carrier_vec m"
    using i_l_m r s vec_aug_in_carrier by blast+
  moreover have "vec_aug r i True \<le> vec_aug s i True"
  proof (unfold vec_aug_def less_eq_vec_def dim_vec, intro conjI)
    show dim_eq: "dim_vec r + 1 = dim_vec s + 1" using r s unfolding carrier_vec_def by simp
    show "\<forall>ia<dim_vec s + 1.
       vec (dim_vec r + 1)
        (\<lambda>ia. if ia < i then r $ ia else if ia = i then True else r $ (ia - 1)) $
       ia
       \<le> vec (dim_vec s + 1)
           (\<lambda>ia. if ia < i then s $ ia else if ia = i then True else s $ (ia - 1)) $
          ia"
    proof (intro allI, rule)
      fix ia
      assume ia: "ia < dim_vec s + 1"
      show " vec (dim_vec r + 1)
           (\<lambda>ia. if ia < i then r $ ia else if ia = i then True else r $ (ia - 1)) $
          ia
          \<le> vec (dim_vec s + 1)
              (\<lambda>ia. if ia < i then s $ ia else if ia = i then True else s $ (ia - 1)) $
             ia"
      proof (cases "ia = i")
        case True
        show ?thesis using ia dim_eq by (simp add: True)
      next
        case False
        note ia_ne_i = False 
        show ?thesis
        proof (cases "ia < i")
          case True
          show ?thesis
            using ia dim_eq r_le_s ia_ne_i True i_l_m unfolding less_eq_vec_def
            by auto (metis One_nat_def Suc_diff_Suc carrier_vecD diff_zero less_antisym not_less_eq plus_1_eq_Suc r trans_less_add1)
        next
          case False
          show ?thesis
            using ia dim_eq r_le_s ia_ne_i False i_l_m unfolding less_eq_vec_def
            by auto
        qed
      qed
    qed
  qed
  ultimately show "f (vec_aug r i True) \<le> f (vec_aug s i True)"
    using m unfolding mono_on_def by blast
qed

lemma
  subfunction_0_dim_subfunction_1_dim_mon:
  assumes m: "mono_on f (carrier_vec (dim_vec v + 1))"
    and s0: "(subfunction_0_dim f i) v"
  shows "(subfunction_1_dim f i) v"
proof -
  have mon: "vec (dim_vec v + 1) (\<lambda>ia. if ia < i then v $ ia else if ia = i then False else v $ (ia - 1))
      \<le> vec (dim_vec v + 1)
        (\<lambda>ia. if ia < i then v $ ia else if ia = i then True else v $ (ia - 1))"
    unfolding less_eq_vec_def by simp
  have "(subfunction_0_dim f i) v \<le> (subfunction_1_dim f i) v"
    unfolding subfunction_0_dim_def
    unfolding subfunction_1_dim_def
    unfolding vec_aug_def
    by (rule mono_onD [of f "carrier_vec (dim_vec v + 1)"], intro m, simp, simp, rule mon)
  then show ?thesis using s0 by simp
qed

lemma
  assumes m: "monotone_bool_fun f"
  shows "monotone_bool_fun (subfunction_0 f i)"
proof (unfold subfunction_0_def monotone_bool_fun_def mono_on_def, safe)
  fix r s :: "bool vec"
  assume r: "r \<in> carrier_vec n" and s: "s \<in> carrier_vec n" and r_le_s: "r \<le> s"
  hence fr: "f r \<le> f s" using m unfolding monotone_bool_fun_def mono_on_def by simp
  from r_le_s have "vec (dim_vec r) (\<lambda>ia. if ia = i then False else r $ ia) 
    \<le> vec (dim_vec s) (\<lambda>ia. if ia = i then False else s $ ia)"
    using r s unfolding carrier_vec_def less_eq_vec_def
    by simp
  thus "f (vec (dim_vec r) (\<lambda>ia. if ia = i then False else r $ ia))
           \<le> f (vec (dim_vec s) (\<lambda>ia. if ia = i then False else s $ ia))"
    by (metis (no_types, lifting) m boolean_functions.monotone_bool_fun_def carrier_vecD mono_on_def r s vec_carrier)
qed

lemma 
  assumes m: "monotone_bool_fun f"
  shows "monotone_bool_fun (subfunction_1 f i)"
proof (unfold subfunction_1_def monotone_bool_fun_def mono_on_def, safe)
  fix r s :: "bool vec"
  assume r: "r \<in> carrier_vec n" and s: "s \<in> carrier_vec n" and r_le_s: "r \<le> s"
  hence fr: "f r \<le> f s" using m unfolding monotone_bool_fun_def mono_on_def by simp
  from r_le_s have "vec (dim_vec r) (\<lambda>ia. if ia = i then True else r $ ia) 
    \<le> vec (dim_vec s) (\<lambda>ia. if ia = i then True else s $ ia)"
    using r s unfolding carrier_vec_def less_eq_vec_def
    by simp
  thus "f (vec (dim_vec r) (\<lambda>ia. if ia = i then True else r $ ia))
           \<le> f (vec (dim_vec s) (\<lambda>ia. if ia = i then True else s $ ia))"
    by (metis (no_types, lifting) m boolean_functions.monotone_bool_fun_def carrier_vecD mono_on_def r s vec_carrier)
qed

end

section\<open>Operations LINK and COST for simplicial complexes.\<close>

text\<open>In our definition of @{term simplicial_complex.simplicial_complex}
  we used as set of vertexes @{term "{0..<n::nat}"}. Since the @{term link}
  and @{term cost} operations can remove any vertex, we introduce a more 
  general notion of simplicial complex where the set of vertexes can be any 
  finite set of natural numbers.\<close>

definition simplices :: "'a set \<Rightarrow> 'a set set"
  where "simplices V = Pow V"

lemma "{} \<in> simplices V"
  unfolding simplices_def by simp

lemma
  fixes k :: nat and n :: nat
  assumes k: "k \<le> n"
  shows "{0..<k} \<in> simplices {0..<n}"
  using k unfolding simplices_def by simp

lemma finite_simplex:
  assumes "finite V" and "\<sigma> \<in> simplices V"
  shows "finite \<sigma>"
  using assms(1) assms(2) finite_subset unfolding simplices_def by auto

text\<open>A simplicial complex (in $n$ vertexes) is a collection of 
  sets of vertexes such that every subset of 
  a set of vertexes also belongs to the simplicial complex.\<close>

definition simplicial_complex :: "'a set \<Rightarrow> 'a set set => bool"
  where "simplicial_complex V K \<equiv>  (\<forall>\<sigma>\<in>K. (\<sigma> \<in> simplices V) \<and> (Pow \<sigma>) \<subseteq> K)"

lemma simplicial_complex_simplice:
  assumes s: "simplicial_complex V K"
  and sigma: "\<sigma> \<in> simplices V" and pow: "Pow \<sigma> \<subseteq> K"
shows "\<sigma> \<in> K"
  using s sigma pow unfolding simplicial_complex_def by auto

text\<open>The notion of @{term simplicial_complex_card} is defined
  as the number of vertexes of the simplicial complex. 
  It can be identified with the number of variables of the associated
  (monotone) Boolean function. Note that some of these vertexes 
  could not belong to any simplex.\<close>

definition simplicial_complex_card :: "'a set \<Rightarrow> 'a set set => nat"
  where "simplicial_complex_card V K = card V"

text\<open>The following result shows the coherence with our definition
  of simplicial complex in @{locale simplicial_complex}. 
  The simplicial complex in vertexes @{term "{0..<n}"}
  in locale @{term simplicial_complex} is an instance of
  @{term simplicial_complex}.\<close>

lemma
  assumes s: "simplicial_complex.simplicial_complex n K"
  shows "simplicial_complex {0..<n} K"
  using s
  unfolding simplicial_complex.simplicial_complex_def simplicial_complex_def
  unfolding simplicial_complex.simplices_def simplices_def .

lemma "simplicial_complex_card {0..<n} K = n"
  unfolding simplicial_complex_card_def by simp

text\<open>The following results are generalizations of
  the ones in the locale @{locale simplicial_complex}
  to a ``free'' set of vertexes.\<close>

lemma simplicial_complex_empty_set: "simplicial_complex V {}"
  unfolding simplicial_complex_def 
  unfolding simplices_def by simp

lemma simplicial_complex_contains_empty_set: "simplicial_complex V {{}}"
  unfolding simplicial_complex_def 
  unfolding simplices_def by simp

lemma simplicial_complex_either_empty_or_contains_empty:
  fixes V :: "'a set" and K::"'a set set"
  assumes k: "simplicial_complex V K"
  shows "K = {} \<or> {} \<in> K" using k unfolding simplicial_complex_def Pow_def by auto

lemma 
  finite_simplicial_complex:
  assumes "finite V" and "simplicial_complex V K"
  shows "finite K"
  by (metis assms(1) assms(2) finite_Pow_iff finite_subset simplices_def simplicial_complex_def subsetI)

definition link :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "link x V K = {s. s \<in> simplices (V - {x}) \<and> s \<union> {x} \<in> K}"

definition cost :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "cost x V K = {s. s \<in> simplices (V - {x}) \<and> s \<in> K}"

value "Pow (set [1,2,3,4::nat])"

value "link 4 (set [0::nat,1,2,3,4,5,6,7,8]) 
        (Pow (set [1,2,3,4,5]) \<union> Pow (set [4,7]) \<union> Pow (set [2,8]))"

value "cost 4 (set [0::nat,1,2,3,4,5,6,7,8]) 
        (Pow (set [1,2,3,4,5]) \<union> Pow (set [4,7]) \<union> Pow (set [2,8]))"

lemma link_empty [simp]: "link x V {} = {}"
  by (simp add: link_def)

lemma cost_empty [simp]: "cost x V {} = {}"
  by (simp add: cost_def)

text\<open>The result of operations @{term link} and @{term cost} 
  are simplicial complexes.\<close>

lemma
  simplicial_complex_link:
  assumes s: "simplicial_complex V K"
  shows "simplicial_complex (V - {x}) (link x V K)"
  unfolding link_def
  using s
  unfolding simplicial_complex_def simplices_def by fast

lemma
  simplicial_complex_cost:
  assumes s: "simplicial_complex V K"
  shows "simplicial_complex (V - {x}) (cost x V K)"
  unfolding cost_def
  using s
  unfolding simplicial_complex_def simplices_def by fast

lemma link_subset_cost: 
  assumes s: "simplicial_complex V K"
  shows "link x V K \<subseteq> cost x V K"
  using s
  unfolding simplicial_complex_def
  unfolding link_def cost_def simplices_def by auto  

text\<open>The number of vertexes  of operations @{term link} and @{term cost} 
  is one less than the number of vertexes in the original simplicial complex.\<close>

lemma
  assumes "simplicial_complex_card V K = n"
    and "x \<in> V"
  shows "simplicial_complex_card (V - {x}) (link x V K) = n - 1"
  using assms(1) assms(2) unfolding simplicial_complex_card_def by auto

lemma
  assumes "simplicial_complex_card V K = n"
    and "x \<in> V"
  shows "simplicial_complex_card (V - {x}) (cost x V K) = n - 1"
  using assms(1) assms(2) unfolding simplicial_complex_card_def by auto

section\<open>Equivalence between operations @{term link} and @{term cost} 
  with @{term subfunction_0_dim} and @{term subfunction_1_dim}.\<close>

locale simplicial_complex_mp_with_boolean_function = "boolean_functions" +
  fixes mp :: "nat \<Rightarrow> 'a"
    and V :: "'a set"
    and K :: "'a set set"
  assumes s: "simplicial_complex V K"
    and mp: "bij_betw mp {0..<n} V"
begin

definition ceros_of_boolean_input :: "bool vec \<Rightarrow> 'a set"
  where "ceros_of_boolean_input v = mp ` {x. x < dim_vec v \<and> vec_index v x = False}"

definition bool_vec_from_simplice :: "'a set => (bool vec)"
  where "bool_vec_from_simplice \<sigma> = vec n (\<lambda>i. mp i \<notin> \<sigma>)"

definition
  simplicial_complex_induced_by_monotone_boolean_function
    :: "(bool vec => bool) => 'a set set"
  where "simplicial_complex_induced_by_monotone_boolean_function f =
        {y\<in>simplices V. \<exists>x. dim_vec x = card V \<and> f x \<and> ceros_of_boolean_input x = y}"

end

text\<open>The simplicial complex given by the @{term link} function
  is a simplicial complex. Note that we also introduce the mapping @{term mp}
  between the indexes of the Boolean arrays and the vertexes 
  in the simplicial complex @{term V}.\<close>

lemma
  simplicial_complex_mp_link:
  assumes s: "simplicial_complex_mp_with_boolean_function n mp V K"
  and x: "x \<in> V"
  and mp: "mp j = x"
  and j: "j < n"
shows "simplicial_complex_mp_with_boolean_function 
      (n - 1) (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (link x V K)"
  unfolding simplicial_complex_mp_with_boolean_function_def
proof (intro conjI)
  show "simplicial_complex (V - {x}) (link x V K)"
    using s simplicial_complex_link [of V K] simplicial_complex_mp_with_boolean_function.s 
    by blast
  show "bij_betw (\<lambda>i. if i < j then mp i else mp (i + 1)) {0..<n - 1} (V - {x})"
  proof (unfold bij_betw_def, intro conjI)
    show "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<n - 1} = V - {x}"
    proof -
      have a: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<n - 1} = 
        (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<j} \<union> 
        (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {j..<n-1}"
        using j by auto
      have b: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<j} = mp ` {0..<j}" by simp
      have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {j..<n-1} = (\<lambda>i. mp (i + 1)) ` {j..<n -1}" by simp
      also have "... = (mp \<circ> (\<lambda>i. i + 1)) ` {j..<n -1}" by simp
      also have "... = mp ` {j+1..<n}"
      proof -
        have "(\<lambda>i. i + 1) ` {j..<n -1} =  {j+1..<n}" by auto
        thus ?thesis by (metis image_comp)
      qed
      finally have c: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {j..<n-1} = mp ` {j+1..<n}" 
        by simp
      from a b c mp have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<n-1} = 
          mp ` {0..<j} \<union> mp ` {j+1..<n}" by simp
      also have "... = mp ` ({0..<n} - {j})"
      proof -
        have "{0..<j} \<union> {j+1..<n} = {0..<n} - {j}" using j by auto
        thus ?thesis by auto
      qed
      also have "... = mp ` {0..<n} - mp ` {j}" 
        using j 
        using simplicial_complex_mp_with_boolean_function.mp [OF s]
        unfolding bij_betw_def inj_on_def by auto
      also have "... = V - {x}"
        using mp
        using simplicial_complex_mp_with_boolean_function.mp [OF s]
        unfolding bij_betw_def inj_on_def by auto
      finally show ?thesis .
    qed
  next
    show "inj_on (\<lambda>i. if i < j then mp i else mp (i + 1)) {0..<n - 1}"
    proof (unfold inj_on_def, rule+)
      fix x y
      assume x: "x \<in> {0..<n - 1}" and y: "y \<in> {0..<n-1}"
        and eq: "(if x < j then mp x else mp (x + 1)) = (if y < j then mp y else mp (y + 1))" 
      show "x = y"
      proof (cases "x < j")
        case True note xj = True
        show ?thesis 
        proof (cases "y < j")
          case True
          show ?thesis 
            using True xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def by simp
        next
          case False
          show ?thesis
            using False xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def by fastforce
        qed
      next
        case False note xj = False
        show ?thesis
          proof (cases "y < j")
          case True
          show ?thesis 
            using True xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def by fastforce
        next
          case False
          show ?thesis
            using False xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def
            by fastforce
        qed
      qed
    qed
  qed
qed

lemma
  simplicial_complex_mp_cost:
  assumes s: "simplicial_complex_mp_with_boolean_function n mp V K"
  and x: "x \<in> V"
  and mp: "mp j = x"
  and j: "j < n"
shows "simplicial_complex_mp_with_boolean_function
      (n - 1) (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (cost x V K)"
  unfolding simplicial_complex_mp_with_boolean_function_def
proof (intro conjI)
  show "simplicial_complex (V - {x}) (cost x V K)"
    using s simplicial_complex_cost [of V K] simplicial_complex_mp_with_boolean_function.s 
    by blast
  show "bij_betw (\<lambda>i. if i < j then mp i else mp (i + 1)) {0..<n - 1} (V - {x})"
  proof (unfold bij_betw_def, intro conjI)
    show "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<n - 1} = V - {x}"
    proof -
      have a: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<n - 1} = 
        (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<j} \<union> 
        (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {j..<n-1}"
        using j by auto
      have b: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<j} = mp ` {0..<j}" by simp
      have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {j..<n-1} = (\<lambda>i. mp (i + 1)) ` {j..<n -1}" by simp
      also have "... = (mp \<circ> (\<lambda>i. i + 1)) ` {j..<n -1}" by simp
      also have "... = mp ` {j+1..<n}"
      proof -
        have "(\<lambda>i. i + 1) ` {j..<n -1} =  {j+1..<n}" by auto
        thus ?thesis by (metis image_comp)
      qed
      finally have c: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {j..<n-1} = mp ` {j+1..<n}" 
        by simp
      from a b c mp have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {0..<n-1} = 
          mp ` {0..<j} \<union> mp ` {j+1..<n}" by simp
      also have "... = mp ` ({0..<n} - {j})"
      proof -
        have "{0..<j} \<union> {j+1..<n} = {0..<n} - {j}" using j by auto
        thus ?thesis by auto
      qed
      also have "... = mp ` {0..<n} - mp ` {j}" 
        using j 
        using simplicial_complex_mp_with_boolean_function.mp [OF s]
        unfolding bij_betw_def inj_on_def by auto
      also have "... = V - {x}"
        using mp
        using simplicial_complex_mp_with_boolean_function.mp [OF s]
        unfolding bij_betw_def inj_on_def by auto
      finally show ?thesis .
    qed
  next
    show "inj_on (\<lambda>i. if i < j then mp i else mp (i + 1)) {0..<n - 1}"
    proof (unfold inj_on_def, rule+)
      fix x y
      assume x: "x \<in> {0..<n - 1}" and y: "y \<in> {0..<n-1}"
        and eq: "(if x < j then mp x else mp (x + 1)) = (if y < j then mp y else mp (y + 1))" 
      show "x = y"
      proof (cases "x < j")
        case True note xj = True
        show ?thesis 
        proof (cases "y < j")
          case True
          show ?thesis 
            using True xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def by simp
        next
          case False
          show ?thesis
            using False xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def by fastforce
        qed
      next
        case False note xj = False
        show ?thesis
          proof (cases "y < j")
          case True
          show ?thesis 
            using True xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def by fastforce
        next
          case False
          show ?thesis
            using False xj eq
            using simplicial_complex_mp_with_boolean_function.mp [OF s]
            using x y
            unfolding bij_betw_def inj_on_def
            by fastforce
        qed
      qed
    qed
  qed
qed

lemma conjI3: assumes "A" and "B" and "C" shows "A \<and> B \<and> C"
  by (simp add: assms(1) assms(2) assms(3))

lemma image_Un3: "f ` (A \<union> B \<union> C) = f ` A \<union> f ` B \<union> f `C" by auto

lemma
  assumes s: "simplicial_complex_mp_with_boolean_function n mp V K"
    and x: "x \<in> V"
    and mp: "mp j = x"
    and j: "j < n"
    and finite: "finite V"
    and s_induced: "simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
      mp V f = K"
  shows "simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
    (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (subfunction_0_dim f j) = (link x V K)"
proof (rule)
  have s': "simplicial_complex_mp_with_boolean_function
      (n - 1) (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (link x V K)"
    using simplicial_complex_mp_link [OF s x mp j] .
  have card_V: "card V = n"
    by (metis bij_betw_same_card card_atLeastLessThan diff_zero s simplicial_complex_mp_with_boolean_function.mp)
  show "simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
     (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (subfunction_0_dim f j)
    \<subseteq> link x V K"
    unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF simplicial_complex_mp_link [OF s x mp j]]
    unfolding link_def
    unfolding subfunction_0_dim_def
    unfolding simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s']
  proof
    fix xa
    assume xa_s: "xa \<in> {y \<in> simplices (V - {x}). \<exists>xa. dim_vec xa = card (V - {x}) 
              \<and> f (vec_aug xa j False) 
              \<and> (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xa \<and> xa $ x = False} =
                     y}"
    hence xa: "xa \<in> simplices (V - {x})" by fast
    from xa_s obtain xb :: "bool vec"
      where dim: "dim_vec xb = card (V - {x})" 
      and f: "f (vec_aug xb j False)"
      and im: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xb \<and> xb $ x = False} =
                     xa" by auto
    show "xa \<in> {s \<in> simplices (V - {x}). s \<union> {x} \<in> K}"
    proof (rule, intro conjI)
      show "xa \<in> simplices (V - {x})" using xa .
      show "xa \<union> {x} \<in> K"
      proof (rule simplicial_complex_simplice [of V])
        show "simplicial_complex V K" 
          using s unfolding simplicial_complex_mp_with_boolean_function_def by fast
        show "xa \<union> {x} \<in> simplices V" using xa x unfolding simplices_def by auto
        have "xa \<union> {x} \<in> K"
        proof -
          have K: "K = {y \<in> simplices V. \<exists>x. dim_vec x = card V 
                  \<and> f x
                  \<and> simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp x = y}"
            unfolding s_induced [symmetric]
            unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF s]
            ..
          moreover have "xa \<union> {x} \<in>  {y \<in> simplices V. \<exists>x. dim_vec x = card V 
                  \<and> f x
                  \<and> simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp x = y}"
          proof (rule, intro conjI)
            show "xa \<union> {x} \<in> simplices V"
              using \<open>xa \<union> {x} \<in> simplices V\<close> by auto
            show "\<exists>xb. dim_vec xb = card V
                     \<and> f xb
                     \<and> simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp xb = xa \<union> {x}"
            proof (rule exI [of _ "vec_aug xb j False"], rule conjI3)
              show "dim_vec (vec_aug xb j False) = card V" 
                using dim x finite unfolding vec_aug_def dim_vec
                by auto (metis card_Suc_Diff1 dim)
              show "f (vec_aug xb j False)" using f .
              show "simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp (vec_aug xb j False) =
                    xa \<union> {x}"
              proof (unfold simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s])
                have card_V: "card V = n"
                  using s
                  unfolding simplicial_complex_mp_with_boolean_function_def
                  by (metis bij_betw_same_card card_atLeastLessThan diff_zero)
                have set_eq: "{x. x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False} =
                  {x. x < j \<and> vec_aug xb j False $ x = False}
                  \<union> {x. j < x \<and> x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False}
                  \<union> {x. x = j \<and> vec_aug xb j False $ x = False}"
                  using j using dim card_V x unfolding vec_aug_def dim_vec by auto
                have mp_j: "mp ` {x. x = j \<and> vec_aug xb j False $ x = False} = {x}"
                  using mp j card_V dim x unfolding vec_aug_def by auto
                have mp_less_j: "mp ` {x. x < j \<and> vec_aug xb j False $ x = False} =
                    (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < j \<and> xb $ x = False}"
                  unfolding vec_aug_def dim_vec apply auto
                  using card_V dim j x apply force using card_V dim j x by simp
                have mp_gt_j: "mp ` {x. j < x \<and> x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False}
                  = (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"
                proof -
                  have rhs: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} =
                      (mp \<circ> (\<lambda>x. x + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"
                    by simp
                  also have "... = mp ` ((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False})"
                    using fun.set_map [of "mp" "(\<lambda>x. x + 1)"] by auto
                  also have "mp ` ((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}) = 
                    mp ` {x. j < x \<and> x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False}" 
                  proof -
                    have set_eq: "((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}) =
                          {x. j < x \<and> x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False}"
                      unfolding vec_aug_def dim_vec
                      by auto (smt (z3) Suc_less_eq Suc_pred diff_is_0_eq imageI less_trans_Suc mem_Collect_eq nat_neq_iff zero_less_Suc zero_less_diff)
                    have inj: "inj_on mp {0..<n}"
                      using s 
                      unfolding simplicial_complex_mp_with_boolean_function_def bij_betw_def by fast
                    show ?thesis
                      using inj_on_image_eq_iff [OF inj,
                          of "((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False})"
                             "{x. j < x \<and> x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False}"]
                      set_eq by simp
                  qed
                  finally show ?thesis ..
                qed
                have set_union: "{x. x < j \<and> xb $ x = False} \<union> {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} = 
                  {x. x < dim_vec xb \<and> xb $ x = False}" using card_V dim j x by auto
                show "mp ` {x. x < dim_vec (vec_aug xb j False) \<and> vec_aug xb j False $ x = False} = xa \<union> {x}"
                  unfolding set_eq
                  unfolding image_Un3
                  unfolding mp_j
                  unfolding mp_less_j
                  unfolding mp_gt_j
                  unfolding im [symmetric]
                  unfolding image_Un [symmetric, of "(\<lambda>i. if i < j then mp i else mp (i + 1))"
                      "{x. x < j \<and> xb $ x = False}" "{x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"]
                  unfolding set_union ..
              qed
            qed
          qed
          thus ?thesis unfolding K [symmetric] .
        qed
        thus "Pow (xa \<union> {x}) \<subseteq> K" 
          using s unfolding simplicial_complex_mp_with_boolean_function_def simplicial_complex_def by simp
      qed
    qed
  qed
  show "link x V K
    \<subseteq> simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
        (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (subfunction_0_dim f j)"
    unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF simplicial_complex_mp_link [OF s x mp j]]
    unfolding link_def
    unfolding subfunction_0_dim_def
    unfolding simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s']
    unfolding vec_aug_def
  proof (rule)
    fix xa
    assume xa: "xa \<in> {s \<in> simplices (V - {x}). s \<union> {x} \<in> K}"
    hence xa_s: "xa \<in> simplices (V - {x})" and xa_x: "xa \<union> {x} \<in> K" by simp_all
    from xa_x
    obtain ya where dim_ya: "dim_vec ya = card V"
      and f_ya: "f ya"
      and mp_ya: "mp ` {xa. xa < dim_vec ya \<and> ya $ xa = False} = xa \<union> {x}"
      unfolding s_induced [symmetric]
      unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF s, of f]
      unfolding simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s]
      by auto
    have inj: "inj_on mp {0..<n}"
      using s
      unfolding simplicial_complex_mp_with_boolean_function_def bij_betw_def by fast
    have j_in: "j \<in> {xa. xa < dim_vec ya \<and> ya $ xa = False}"
      using inj_on_image_mem_iff [OF inj, of j "{xa. xa < dim_vec ya \<and> ya $ xa = False}"]
      using mp_ya j mp inj dim_ya card_V atLeast0LessThan by auto
    then have ya_j_False: "ya $ j = False" by auto      
    define xb :: "bool vec"
      where xb_def: "xb = vec_red ya j"
      (*define xb :: "bool vec"
      where xb_def: "xb =
        simplicial_complex_mp_with_boolean_function.bool_vec_from_simplice (n - 1) (\<lambda>i. if i < j then mp i else mp (i + 1)) xa"*)
      show "xa \<in> {y \<in> simplices (V - {x}).
                 \<exists>xa. dim_vec xa = card (V - {x}) \<and>
                      f (vec (dim_vec xa + 1)
                          (\<lambda>i. if i < j then xa $ i else if i = j then False else xa $ (i - 1))) \<and>
                      (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xa \<and> xa $ x = False} =
                      y}"
    proof (rule, intro conjI, rule xa_s, rule exI [of _ xb], rule conjI3)
      show "dim_vec xb = card (V - {x})" 
        unfolding xb_def
        unfolding vec_red_def
        unfolding dim_vec using dim_ya x by simp
      show "f (vec (dim_vec xb + 1) (\<lambda>i. if i < j then xb $ i else if i = j then False else xb $ (i - 1)))"
      proof -
        have "ya = vec (dim_vec xb + 1) (\<lambda>i. if i < j then xb $ i else if i = j then False else xb $ (i - 1))"
          apply (intro eq_vecI, unfold xb_def dim_vec vec_red_def, simp_all add: ya_j_False x dim_ya)
          using x
          apply auto
          apply (metis (no_types, lifting) One_nat_def card.remove card_Diff_singleton card_V index_vec j le_simps(2) less_antisym linorder_not_less local.finite)
           apply (metis (no_types, lifting) One_nat_def card.remove card_Diff_singleton card_V index_vec j le_simps(2) less_antisym linorder_not_less local.finite)
          by (metis One_nat_def card.remove card_Diff_singleton local.finite)
        thus ?thesis using f_ya by fast
      qed
      show "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xb \<and> xb $ x = False} = xa"
      proof -
        from mp_ya
        have mp_ya_j: "mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j}) = xa"
        proof -
          have "mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j})
            = mp ` {xa. xa < dim_vec ya \<and> ya $ xa = False} - mp ` {j}"
            apply (rule inj_on_image_set_diff [OF inj, of "{xa. xa < dim_vec ya \<and> ya $ xa = False}" "{j}"])
            unfolding dim_ya card_V using j by auto
          also have "... = mp ` {xa. xa < dim_vec ya \<and> ya $ xa = False} - {x}"
            using mp by simp
          also have "... = (xa \<union> {x}) - {x}" unfolding mp_ya ..
          also have "... = xa"
          proof -
            have "x \<notin> xa"
              using s
              unfolding simplicial_complex_mp_with_boolean_function_def
              using mp_ya inj unfolding inj_on_def using j mp j_in 
              unfolding dim_ya card_V
              by auto (metis One_nat_def Pow_iff add.commute add_diff_cancel_left' basic_trans_rules(31) cancel_comm_monoid_add_class.diff_cancel card.remove insert_Diff insert_absorb local.finite nat.simps(3) plus_1_eq_Suc simplices_def x xa_s)
            thus ?thesis by simp
          qed
          finally show ?thesis .
        qed
        have set_union: "{x. x < dim_vec xb \<and> xb $ x = False} = 
               {x. x < j \<and> xb $ x = False}
               \<union> {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}" 
        proof (cases "j \<le> dim_vec xb")  
          case True show ?thesis using True by auto
        next
          case False show ?thesis using False
            by (metis \<open>dim_vec xb = card (V - {x})\<close> card.remove card_V j less_Suc_eq_le local.finite x)
        qed
        have mp_image_l_j: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < j \<and> xb $ x = False} 
          = mp ` {x. x < j \<and> xb $ x = False}" by simp
        have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}
          = mp ` (\<lambda>i. i + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"
          by auto
        also have "... = mp ` {x. j < x \<and> x < dim_vec xb + 1 \<and> xb $ (x - 1) = False}"
        proof -
          have "(\<lambda>i. i + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} =
               {x. j < x \<and> x < dim_vec xb + 1 \<and> xb $ (x - 1) = False}"
            unfolding vec_red_def
            unfolding dim_vec apply auto
            using Nat.lessE by fastforce
          thus ?thesis by simp
        qed
        finally have mp_image_g_j: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} =
             mp ` {x. j < x \<and> x < dim_vec xb + 1 \<and> xb $ (x - 1) = False}"
          by simp
        have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xb \<and> xb $ x = False} =
                mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j})"
          unfolding set_union unfolding image_Un
          unfolding mp_image_l_j mp_image_g_j
          unfolding xb_def
          unfolding vec_red_def dim_vec
        proof -
          have "{x. x < j \<and> vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ x = False} \<union>
                {x. j < x \<and> x < dim_vec ya - 1 + 1 \<and>
                  vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ (x - 1) = False} 
              = {xa. xa < dim_vec ya \<and> ya $ xa = False} - {j}"
            using j card_V dim_ya by auto
          thus "mp ` {x. x < j \<and> vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ x = False} \<union>
                mp ` {x. j < x \<and> x < dim_vec ya - 1 + 1 \<and>
                  vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ (x - 1) = False} =
                mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j})" using image_Un by metis
        qed
        also have "... = xa" unfolding mp_ya_j ..
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma
  assumes s: "simplicial_complex_mp_with_boolean_function n mp V K"
    and x: "x \<in> V"
    and mp: "mp j = x"
    and j: "j < n"
    and finite: "finite V"
    and s_induced: "simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
      mp V f = K"
  shows "simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
    (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (subfunction_1_dim f j) = (cost x V K)"
proof (rule)
  have s': "simplicial_complex_mp_with_boolean_function
      (n - 1) (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (cost x V K)"
    using simplicial_complex_mp_cost [OF s x mp j] .
  have card_V: "card V = n"
    by (metis bij_betw_same_card card_atLeastLessThan diff_zero s simplicial_complex_mp_with_boolean_function.mp)
  show "simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
     (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (subfunction_1_dim f j)
    \<subseteq> cost x V K"
    unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF simplicial_complex_mp_link [OF s x mp j]]
    unfolding cost_def
    unfolding subfunction_1_dim_def
    unfolding simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s']
  proof
    fix xa
    assume xa_s: "xa \<in> {y \<in> simplices (V - {x}). \<exists>xa. dim_vec xa = card (V - {x}) 
              \<and> f (vec_aug xa j True) 
              \<and> (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xa \<and> xa $ x = False} =
                     y}"
    hence xa: "xa \<in> simplices (V - {x})" by fast
    from xa_s obtain xb :: "bool vec"
      where dim: "dim_vec xb = card (V - {x})" 
      and f: "f (vec_aug xb j True)"
      and im: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xb \<and> xb $ x = False} =
                     xa" by auto
    show "xa \<in> {s \<in> simplices (V - {x}). s \<in> K}"
    proof (rule, intro conjI)
      show "xa \<in> simplices (V - {x})" using xa .
      show "xa \<in> K"
      proof (rule simplicial_complex_simplice [of V])
        show "simplicial_complex V K" 
          using s unfolding simplicial_complex_mp_with_boolean_function_def by fast
        show "xa \<in> simplices V" using xa x unfolding simplices_def by auto
        have "xa \<in> K"
        proof -
          have K: "K = {y \<in> simplices V. \<exists>x. dim_vec x = card V 
                  \<and> f x
                  \<and> simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp x = y}"
            unfolding s_induced [symmetric]
            unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF s]
            ..
          moreover have "xa \<in>  {y \<in> simplices V. \<exists>x. dim_vec x = card V 
                  \<and> f x
                  \<and> simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp x = y}"
          proof (rule, intro conjI)
            show "xa \<in> simplices V"
              using \<open>xa \<in> simplices V\<close> by auto
            show "\<exists>xb. dim_vec xb = card V
                     \<and> f xb
                     \<and> simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp xb = xa"
            proof (rule exI [of _ "vec_aug xb j True"], rule conjI3)
              show "dim_vec (vec_aug xb j True) = card V" 
                using dim x finite unfolding vec_aug_def dim_vec
                by auto (metis card_Suc_Diff1 dim)
              show "f (vec_aug xb j True)" using f .
              show "simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input mp (vec_aug xb j True) =
                    xa"
              proof (unfold simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s])
                have card_V: "card V = n"
                  using s
                  unfolding simplicial_complex_mp_with_boolean_function_def
                  by (metis bij_betw_same_card card_atLeastLessThan diff_zero)
                have set_eq: "{x. x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False} =
                  {x. x < j \<and> vec_aug xb j True $ x = False}
                  \<union> {x. j < x \<and> x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False}
                  \<union> {x. x = j \<and> vec_aug xb j True $ x = False}"
                  using j using dim card_V x unfolding vec_aug_def dim_vec by auto
                have mp_j: "mp ` {x. x = j \<and> vec_aug xb j True $ x = False} = {}" 
                  using mp j card_V dim x unfolding vec_aug_def by auto
                have mp_less_j: "mp ` {x. x < j \<and> vec_aug xb j True $ x = False} =
                    (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < j \<and> xb $ x = False}"
                  unfolding vec_aug_def dim_vec apply auto
                  using card_V dim j x apply force using card_V dim j x by simp
                have mp_gt_j: "mp ` {x. j < x \<and> x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False}
                  = (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"
                proof -
                  have rhs: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} =
                      (mp \<circ> (\<lambda>x. x + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"
                    by simp
                  also have "... = mp ` ((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False})"
                    using fun.set_map [of "mp" "(\<lambda>x. x + 1)"] by auto
                  also have "mp ` ((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}) = 
                    mp ` {x. j < x \<and> x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False}" 
                  proof -
                    have set_eq: "((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}) =
                          {x. j < x \<and> x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False}"
                      unfolding vec_aug_def dim_vec
                      by auto (smt (z3) Suc_less_eq Suc_pred diff_is_0_eq imageI less_trans_Suc mem_Collect_eq nat_neq_iff zero_less_Suc zero_less_diff)
                    have inj: "inj_on mp {0..<n}"
                      using s 
                      unfolding simplicial_complex_mp_with_boolean_function_def bij_betw_def by fast
                    show ?thesis
                      using inj_on_image_eq_iff [OF inj,
                          of "((\<lambda>x. x + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False})"
                             "{x. j < x \<and> x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False}"]
                      set_eq by simp
                  qed
                  finally show ?thesis ..
                qed
                have set_union: "{x. x < j \<and> xb $ x = False} \<union> {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} = 
                  {x. x < dim_vec xb \<and> xb $ x = False}" using card_V dim j x by auto
                show "mp ` {x. x < dim_vec (vec_aug xb j True) \<and> vec_aug xb j True $ x = False} = xa"
                  unfolding set_eq
                  unfolding image_Un3
                  unfolding mp_j
                  unfolding mp_less_j
                  unfolding mp_gt_j
                  unfolding im [symmetric]
                  unfolding image_Un [symmetric, of "(\<lambda>i. if i < j then mp i else mp (i + 1))"
                      "{x. x < j \<and> xb $ x = False}" "{x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"]
                  unfolding set_union by simp
              qed
            qed
          qed
          thus ?thesis unfolding K [symmetric] .
        qed
        thus "Pow (xa) \<subseteq> K" 
          using s unfolding simplicial_complex_mp_with_boolean_function_def simplicial_complex_def by simp
      qed
    qed
  qed
  show "cost x V K
    \<subseteq> simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function
        (\<lambda>i. if i < j then mp i else mp (i + 1)) (V - {x}) (subfunction_1_dim f j)"
    unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF simplicial_complex_mp_link [OF s x mp j]]
    unfolding cost_def
    unfolding subfunction_1_dim_def
    unfolding simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s']
    unfolding vec_aug_def
  proof (rule)
    fix xa
    assume xa: "xa \<in> {s \<in> simplices (V - {x}). s \<in> K}"
    hence xa_s: "xa \<in> simplices (V - {x})" and xa_x: "xa \<in> K" by simp_all
    from xa_x
    obtain ya where dim_ya: "dim_vec ya = card V"
      and f_ya: "f ya"
      and mp_ya: "mp ` {xa. xa < dim_vec ya \<and> ya $ xa = False} = xa"
      unfolding s_induced [symmetric]
      unfolding simplicial_complex_mp_with_boolean_function.simplicial_complex_induced_by_monotone_boolean_function_def [OF s, of f]
      unfolding simplicial_complex_mp_with_boolean_function.ceros_of_boolean_input_def [OF s]
      by auto
    have inj: "inj_on mp {0..<n}"
      using s
      unfolding simplicial_complex_mp_with_boolean_function_def bij_betw_def by fast
    have j_in: "j \<notin> {xa. xa < dim_vec ya \<and> ya $ xa = False}"
      using inj_on_image_mem_iff [OF inj, of j "{xa. xa < dim_vec ya \<and> ya $ xa = False}"]
      using mp_ya j mp inj dim_ya card_V atLeast0LessThan using s
      unfolding simplicial_complex_mp_with_boolean_function_def 
      unfolding simplices_def using xa_s
      by auto (metis (no_types, lifting) Pow_iff bij_betw_def finite_imp_inj_to_nat_seg image_eqI inj_on_insert insert_image insert_subset lessThan_iff local.finite mem_Collect_eq mp_ya simplices_def)
    then have ya_j_True: "ya $ j = True"
      by (simp add: card_V dim_ya j)
    define xb :: "bool vec"
      where xb_def: "xb = vec_red ya j"
      (*define xb :: "bool vec"
      where xb_def: "xb =
        simplicial_complex_mp_with_boolean_function.bool_vec_from_simplice (n - 1) (\<lambda>i. if i < j then mp i else mp (i + 1)) xa"*)
      show "xa \<in> {y \<in> simplices (V - {x}).
                 \<exists>xa. dim_vec xa = card (V - {x}) \<and>
                      f (vec (dim_vec xa + 1)
                          (\<lambda>i. if i < j then xa $ i else if i = j then True else xa $ (i - 1))) \<and>
                      (\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xa \<and> xa $ x = False} =
                      y}"
    proof (rule, intro conjI, rule xa_s, rule exI [of _ xb], rule conjI3)
      show "dim_vec xb = card (V - {x})" 
        unfolding xb_def
        unfolding vec_red_def
        unfolding dim_vec using dim_ya x by simp
      show "f (vec (dim_vec xb + 1) (\<lambda>i. if i < j then xb $ i else if i = j then True else xb $ (i - 1)))"
      proof -
        have "ya = vec (dim_vec xb + 1) (\<lambda>i. if i < j then xb $ i else if i = j then True else xb $ (i - 1))"
          apply (intro eq_vecI, unfold xb_def dim_vec vec_red_def, simp_all add: x dim_ya)
          using x
          apply auto
          using ya_j_True apply blast
             apply (metis (no_types, lifting) One_nat_def card.remove card_Diff_singleton card_V index_vec j le_simps(2) less_antisym linorder_not_less local.finite)
          apply (metis (no_types, lifting) One_nat_def card.remove card_Diff_singleton card_V index_vec j le_simps(2) less_antisym linorder_not_less local.finite)
          using ya_j_True apply blast
          by (metis One_nat_def card.remove card_Diff_singleton local.finite)          
        thus ?thesis using f_ya by fast
      qed
      show "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xb \<and> xb $ x = False} = xa"
      proof -
        from mp_ya
        have mp_ya_j: "mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j}) = xa"
        proof -
          have "mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j})
            = mp ` {xa. xa < dim_vec ya \<and> ya $ xa = False} - mp ` {j}"
            apply (rule inj_on_image_set_diff [OF inj, of "{xa. xa < dim_vec ya \<and> ya $ xa = False}" "{j}"])
            unfolding dim_ya card_V using j by auto
          also have "... = mp ` {xa. xa < dim_vec ya \<and> ya $ xa = False} - {x}"
            using mp by simp
          also have "... = xa - {x}" unfolding mp_ya ..
          also have "... = xa"
          proof -
            have "x \<notin> xa"
              using s
              unfolding simplicial_complex_mp_with_boolean_function_def
              using mp_ya inj unfolding inj_on_def using j mp j_in 
              unfolding dim_ya card_V
              by (metis (mono_tags, lifting) Diff_empty Diff_iff Diff_insert0 calculation j_in mp_ya singletonI)
            thus ?thesis by simp
          qed
          finally show ?thesis .
        qed
        have set_union: "{x. x < dim_vec xb \<and> xb $ x = False} = 
               {x. x < j \<and> xb $ x = False}
               \<union> {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}" 
        proof (cases "j \<le> dim_vec xb")  
          case True show ?thesis using True by auto
        next
          case False show ?thesis using False
            by (metis \<open>dim_vec xb = card (V - {x})\<close> card.remove card_V j less_Suc_eq_le local.finite x)
        qed
        have mp_image_l_j: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < j \<and> xb $ x = False} 
          = mp ` {x. x < j \<and> xb $ x = False}" by simp
        have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}
          = mp ` (\<lambda>i. i + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False}"
          by auto
        also have "... = mp ` {x. j < x \<and> x < dim_vec xb + 1 \<and> xb $ (x - 1) = False}"
        proof -
          have "(\<lambda>i. i + 1) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} =
               {x. j < x \<and> x < dim_vec xb + 1 \<and> xb $ (x - 1) = False}"
            unfolding vec_red_def
            unfolding dim_vec apply auto
            using Nat.lessE by fastforce
          thus ?thesis by simp
        qed
        finally have mp_image_g_j: "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. j \<le> x \<and> x < dim_vec xb \<and> xb $ x = False} =
             mp ` {x. j < x \<and> x < dim_vec xb + 1 \<and> xb $ (x - 1) = False}"
          by simp
        have "(\<lambda>i. if i < j then mp i else mp (i + 1)) ` {x. x < dim_vec xb \<and> xb $ x = False} =
                mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j})"
          unfolding set_union unfolding image_Un
          unfolding mp_image_l_j mp_image_g_j
          unfolding xb_def
          unfolding vec_red_def dim_vec
        proof -
          have "{x. x < j \<and> vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ x = False} \<union>
                {x. j < x \<and> x < dim_vec ya - 1 + 1 \<and>
                  vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ (x - 1) = False} 
              = {xa. xa < dim_vec ya \<and> ya $ xa = False} - {j}"
            using j card_V dim_ya by auto
          thus "mp ` {x. x < j \<and> vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ x = False} \<union>
                mp ` {x. j < x \<and> x < dim_vec ya - 1 + 1 \<and>
                  vec (dim_vec ya - 1) (\<lambda>i. if i < j then ya $ i else ya $ (i + 1)) $ (x - 1) = False} =
                mp ` ({xa. xa < dim_vec ya \<and> ya $ xa = False} - {j})" using image_Un by metis
        qed
        also have "... = xa" unfolding mp_ya_j ..
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma
  link_commute:
  assumes i: "i \<in> V"
  and j: "j \<in> V"
  shows "link j (V - {i}) (link i V K) = link i (V - {j}) (link j V K)"
  unfolding link_def unfolding simplices_def using i j 
  by auto (simp_all add: insert_commute)

lemma
  cost_commute:
  assumes i: "i \<in> V"
  and j: "j \<in> V"
  shows "cost j (V - {i}) (cost i V K) = cost i (V - {j}) (cost j V K)"
  unfolding cost_def unfolding simplices_def using i j by auto 

lemma
  cost_link_commute:
  assumes i: "i \<in> V"
  and j: "j \<in> V"
  and i_ne_j: "i \<noteq> j"
  shows "cost j (V - {i}) (link i V K) = link i (V - {j}) (cost j V K)"
  unfolding link_def cost_def unfolding simplices_def using i j i_ne_j
  by auto

lemma
  link_cost_commute:
  assumes i: "i \<in> V"
  and j: "j \<in> V"
  and i_ne_j: "i \<noteq> j"
  shows "link j (V - {i}) (cost i V K) = cost i (V - {j}) (link j V K)"
  unfolding link_def cost_def unfolding simplices_def using i j i_ne_j
  by auto

section\<open>Internal and External Join and cones\<close>

definition join_vertices :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "join_vertices V V' = (V \<union> V')"

definition join_simplices :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "join_simplices K K' = (K \<union> K' \<union> {x. \<exists>y\<in>K. \<exists>y'\<in>K'. x = y \<union> y'})"

lemma simplicial_complex_singleton:
  fixes x :: 'a
  shows "simplicial_complex {x} {{},{x}}"
  unfolding simplicial_complex_def simplices_def by auto

lemma
  simplicial_complex_join:
  assumes s: "simplicial_complex V K"
  and s': "simplicial_complex V' K'"
shows "simplicial_complex (join_vertices V V') (join_simplices K K')"
  using s s'
  unfolding join_vertices_def join_simplices_def simplicial_complex_def 
  unfolding simplices_def 
  apply (auto)
    apply blast
   apply (meson PowI subsetD)
  by (meson PowI subsetD subset_UnE)

definition external_join_vertices :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a + 'a) set"
  where "external_join_vertices V V' = (V <+> V')"

definition external_join_simplices :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> ('a + 'a) set set"
  where "external_join_simplices K K' = {x. \<exists>y\<in>K. \<exists>y'\<in>K'. x = y <+> y'}"

lemma
  simplicial_complex_external_join:
  assumes s: "simplicial_complex V K"
  and s': "simplicial_complex V' K'"
shows "simplicial_complex (external_join_vertices V V') (external_join_simplices K K')"
  unfolding external_join_vertices_def external_join_simplices_def simplicial_complex_def 
  unfolding simplices_def Pow_def proof (safe)
  fix y y' xa
  assume y: "y \<in> K" and y': "y' \<in> K" and xa: "xa \<in> y"
  show "xa \<in> V" using s y xa unfolding simplicial_complex_def simplices_def by auto
next
  fix y y' ya
  assume y: "y \<in> K" and y': "y' \<in> K'" and ya: "ya \<in> y'"
  show "ya \<in> V'" using s' y' ya unfolding simplicial_complex_def simplices_def by auto
next
  fix \<sigma> y y' x
  assume y: "y \<in> K" and y': "y' \<in> K'" and x: "x \<subseteq> y <+> y'"
  show "\<exists>y\<in>K. \<exists>y'\<in>K'. x = y <+> y'"
  proof (cases "x = {}")
    case True show ?thesis
      using True s s' simplicial_complex_either_empty_or_contains_empty y y' by auto
  next
    case False
    from False obtain x' :: "'a + 'a" where x': "x' \<in> x" by auto
    then obtain xy and xy' where x_split: "x = xy <+> xy'" using x by blast
    with x have "xy \<subseteq> y" and "xy' \<subseteq> y'" by auto
    with y and y' and s and s' have "xy \<in> K" and "xy' \<in> K'"
      unfolding simplicial_complex_def simplices_def by auto
    then show ?thesis using x_split by auto
  qed
qed

(*definition cone_vertices :: "nat \<Rightarrow> nat set \<Rightarrow> nat set"
  where "cone_vertices n V = join_vertices {n} V"*)

definition cone_vertices :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "cone_vertices n V = join_vertices {n} V"

definition cone_simplices :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "cone_simplices n K = join_simplices {{},{n}} K"

text\<open>In principle for the cone it should be enough to use @{term "{n}"} as
  simplex, but including also @{term "{}"} we have that the @{thm cone_vertices_def}
  together with @{thm cone_simplices_def} are already a simplicial complex.\<close>

corollary simplicial_complex_cone:
  assumes s: "simplicial_complex V K"
  shows "simplicial_complex (cone_vertices x V) (cone_simplices x K)"
  using simplicial_complex_join [OF simplicial_complex_singleton [of x] s]
  unfolding cone_vertices_def cone_simplices_def by simp

lemma cone_empty: "cone_simplices x {} = {{},{x}}" 
  unfolding cone_simplices_def join_simplices_def by simp

text\<open>The need to add @{term "insert {} K"} as a premise
  is mentioned in theoretical works, such as for instance Carl Miller
  in @{url "https://arxiv.org/pdf/1306.0110.pdf"} (see the definition
  of emph\<open>cone\<close> in p. 74).\<close>

lemma
  cost_cone_identity:
  assumes x: "x \<notin> V"
    and s: "simplicial_complex V K"
  shows "cost x V (cone_simplices x K) = insert {} K"
proof (cases "K = {}")
  case True
  show ?thesis 
    unfolding True 
    unfolding cone_empty cost_def simplices_def by auto
next
  case False
  show ?thesis unfolding cone_simplices_def
    unfolding cost_def simplices_def join_simplices_def 
    using x using False using s
    unfolding simplicial_complex_def simplices_def by auto
qed

corollary
  cost_cone_identity_nempty:
  assumes x: "x \<notin> V"
    and s: "simplicial_complex V K"
    and K: "K \<noteq> {}"
  shows "cost x V (cone_simplices x K) = K"
  using cost_cone_identity [OF x s] using K
  by (metis insert_absorb s simplicial_complex_either_empty_or_contains_empty)

lemma
  cost_cone_link_cone:
  assumes x: "x \<notin> V"
    and s: "simplicial_complex V K"
    and K: "K \<noteq> {}"
  shows "cost x V (cone_simplices x K) = link x V (cone_simplices x K)"
  unfolding cost_def link_def simplices_def cone_simplices_def join_simplices_def
  using x s K
  unfolding simplicial_complex_def simplices_def
  apply auto
  apply (metis in_mono insert_ident)
  by (metis insert_eq_iff subsetD)

text\<open>A different characterization of a cone, in this case as a predicate.
  This characterization is useful for vertexes which appear in the simplicial
  complex simplices. A simplicial complex is a cone if one of its vertexes
  is connected to every other vertex.\<close>

definition cone :: "'a \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "cone v K = (K = cone_simplices v K)"

value "cone 0 {{},{0},{1::nat},{2}} = False"

value "cone 0 {{},{0},{1::nat},{2},{0,1}} = False"

value "cone 0 {{},{0},{1::nat},{2},{1,0},{1,2}} = False"

value "cone 1 {{},{0},{1::nat},{2},{1,0},{1,2}} = True"

value "cone 0 {{},{0},{1::nat},{2},{0,1},{0,2}} = True"

value "cone 0 {{},{0},{1::nat},{2},{0,1},{0,2},{1,2},{0,1,2}} = True"

lemma coneI [intro!]:
  assumes c: "cone v K"
  shows "K = cone_simplices v K"
  using c using cone_def by (rule back_subst)

(*definition cone :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "cone v V K = simplicial_complex (V - {v}) (cost v V K)"*)

definition vertex_in_simplicial_complex :: "'a \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "vertex_in_simplicial_complex v K = (\<exists>s\<in>K. v \<in> s)"

lemma
  vertex_not_in_link:
  assumes s: "simplicial_complex V K"
    and x: "x \<in> V"
  shows "\<not> vertex_in_simplicial_complex x (link x V K)"
  using s x
  unfolding vertex_in_simplicial_complex_def
  unfolding link_def
  unfolding simplicial_complex_def
  unfolding simplices_def by auto

lemma
  vertex_not_in_cost:
  assumes s: "simplicial_complex V K"
    and x: "x \<in> V"
  shows "\<not> vertex_in_simplicial_complex x (cost x V K)"
  using s x
  unfolding vertex_in_simplicial_complex_def
  unfolding cost_def
  unfolding simplicial_complex_def
  unfolding simplices_def by auto

lemma
  cone_cost:
  assumes s: "simplicial_complex V K"
    and k: "K \<noteq> {}"
    and v: "v \<in> V"
    (*and vk: "vertex_in_simplicial_complex v K"*)
  shows "cone v K = (K = cone_simplices v (cost v V K))"
proof (rule)
  show "(K = cone_simplices v (cost v V K)) \<Longrightarrow> cone v K"
    using s k v
    unfolding cone_def cone_simplices_def cone_vertices_def
    unfolding join_vertices_def join_simplices_def cost_def 
    unfolding simplicial_complex_def simplices_def
    by auto (smt (verit, del_insts) Un_iff insert_absorb2 insert_iff mem_Collect_eq)
next
  show "cone v K \<Longrightarrow> (K = cone_simplices v (cost v V K))"
  proof
    assume cone: "cone v K"
    show "cone_simplices v (cost v V K) \<subseteq> K"
      using cone s k v
      unfolding cone_def cone_simplices_def cone_vertices_def
      unfolding join_vertices_def join_simplices_def cost_def
      unfolding vertex_in_simplicial_complex_def simplicial_complex_def simplices_def by auto
    show "K \<subseteq> cone_simplices v (cost v V K)"
    proof
      fix x
      assume x: "x \<in> K"
      from cone obtain k k' where x_kk': "x = k \<union> k'" 
         and k: "k \<in> {{},{v}}" and k': "k' \<in> K"
        unfolding cone_def
        unfolding cone_simplices_def
        unfolding join_simplices_def using x by blast
      show "x \<in> cone_simplices v (cost v V K)"
      proof (cases "v \<in> k'")
        case False
        have "k' \<in> Pow (V - {v})" 
          using False using x_kk' k k'
          using s x unfolding simplicial_complex_def simplices_def by auto
        thus ?thesis
          using x_kk'
          using k x k'
          unfolding cost_def cone_simplices_def simplices_def join_simplices_def by auto
      next
        case True
        hence k_id: "k \<union> k' = k'" using x_kk' using k by auto
        have "x \<in> {x. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>{s \<in> Pow (V - {v}). s \<in> K}. x = y \<union> y'}"
        proof (rule, rule bexI [of _ "{v}"], rule bexI [of _ "k' - {v}"])
          show "x = {v} \<union> (k' - {v})" unfolding x_kk' k_id using True by auto
          show "k' - {v} \<in> {s \<in> Pow (V - {v}). s \<in> K}" 
            using k' using s unfolding simplicial_complex_def simplices_def by auto
          show "{v} \<in> {{}, {v}}" by fast
        qed
        thus ?thesis
          unfolding cost_def cone_simplices_def simplices_def join_simplices_def by simp
      qed
    qed
  qed
qed

lemma
  cone_cost_equiv:
  assumes s: "simplicial_complex V K"
    and k: "K \<noteq> {}"
    and v: "v \<in> V"
  shows "(K = cone_simplices v K) = (K = cone_simplices v (cost v V K))"
  using cone_cost [OF s k v] unfolding cone_def .

value "cone 1 {{},{1::nat},{2},{1,2}}"

value "cone_simplices 1 (cost 1 {1,2} {{},{1::nat},{2},{1,2}})"

value "cone_simplices 1 (cost 1 {1,2} {{},{1::nat},{2},{1,2}}) = {{},{1::nat},{2},{1,2}}"

value "cost 1 {1::nat,2} (cone_simplices 1 {{},{1},{2},{1,2}}) = {{},{1},{2},{1,2}}"

value "cone_vertices 2 {1::nat}"

value "cone_simplices 3 {{},{1::nat},{2},{1,2}}"

value "cost 1 {1::nat,2,3} {{},{1},{1,2,3}}"

section\<open>Some results in dimension 0.\<close>

lemma
  assumes s: "simplicial_complex.simplicial_complex 0 K"
  shows "K = {} \<or> K = {{}}"
  using s 
  unfolding simplicial_complex.simplicial_complex_def simplicial_complex.simplices_def 
  by auto

lemma
  shows "simplicial_complex.boolean_function_from_simplicial_complex 0 {} = (\<lambda>x. False)"
  unfolding simplicial_complex.boolean_function_from_simplicial_complex_def
  unfolding simplicial_complex.bool_vec_set_from_simplice_set_def
  unfolding simplicial_complex.bool_vec_from_simplice_def by simp

lemma
  shows "simplicial_complex.boolean_function_from_simplicial_complex 0 {{}} =
    (\<lambda>x::bool vec. x = vec 0 (\<lambda>i. True))"
  unfolding simplicial_complex.boolean_function_from_simplicial_complex_def
  unfolding simplicial_complex.bool_vec_set_from_simplice_set_def
  unfolding simplicial_complex.bool_vec_from_simplice_def by fastforce


section\<open>Evasiveness for simplicial complexes\<close>

function non_evasive :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where
   "non_evasive {} K = False"
 | "finite V \<Longrightarrow> non_evasive V K = (\<exists>x\<in>V. V = {x} \<or> (non_evasive (V - {x}) (link x V K) \<and> non_evasive (V - {x}) (cost x V K)))"
 | "\<not> finite V \<Longrightarrow> non_evasive V K = False"
  unfolding link_def cost_def simplices_def by auto+
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  fix V :: "'a set" and K :: "'a set set" and x :: "'a"
  assume f: "finite V" and x: "x \<in> V"
  show "((V - {x}, link x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using f x by auto (metis card_gt_0_iff diff_Suc_less empty_iff)
  show "((V - {x}, cost x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using f x by auto (metis card_gt_0_iff diff_Suc_less empty_iff)
qed simp

lemma
  non_evasive_singleton_true: "non_evasive {x} {{}}" by simp

lemma
  non_evasive_singleton_false: "non_evasive {x} {}" by simp

lemma
  non_evasive_empty_simplicial:
  assumes f: "finite V"
  and v_ne: "V \<noteq> {}"
shows "non_evasive V {}"
using f v_ne proof (induct "card V" arbitrary: V)
  case 0
  then have False by simp thus ?case by simp
next
  case (Suc n)
  show ?case proof (cases "card V = 1")
    case True
    then show ?thesis
      by (metis One_nat_def card_1_singleton_iff non_evasive_singleton_false)
  next
    case False
    with Suc (2) obtain x where x: "x \<in> V" by fastforce
    have "non_evasive (V - {x}) (link x V {}) \<and> non_evasive (V - {x}) (cost x V {})"
    proof (rule conjI)
      show "non_evasive (V - {x}) (link x V {})"
        unfolding link_empty
      proof (rule Suc (1))
       show "n = card (V - {x})" by (metis Suc.hyps(2) card_Diff_singleton diff_Suc_1 x)
       show "finite (V - {x})" using Suc.prems(1) by blast
       show "V - {x} \<noteq> {}"
         by (metis False One_nat_def Suc.prems(1) card.remove card_eq_0_iff x)
     qed
     show "non_evasive (V - {x}) (cost x V {})"
        unfolding cost_empty
      proof (rule Suc (1))
       show "n = card (V - {x})" by (metis Suc.hyps(2) card_Diff_singleton diff_Suc_1 x)
       show "finite (V - {x})" using Suc.prems(1) by blast
       show "V - {x} \<noteq> {}"
         by (metis False One_nat_def Suc.prems(1) card.remove card_eq_0_iff x)
     qed
   qed
   then show ?thesis using non_evasive.simps (2) [OF Suc (3), of "{}"] using x by blast
 qed
qed

definition evasive :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "evasive V K = (\<not> non_evasive V K)"

lemma
  cost_cone_cone_cost:
  assumes x: "x \<noteq> v"
  and x': "x \<in> V"
shows "cost x (V \<union> {v}) (cone_simplices v K) = cone_simplices v (cost x (V \<union> {v}) K)"
  using x x'
  unfolding simplicial_complex_def cost_def cone_simplices_def simplices_def join_simplices_def
  by auto

lemma [simp]:
  assumes v: "vertex_in_simplicial_complex x K"
  shows "K \<noteq> {}"
  using v
  by (meson empty_iff vertex_in_simplicial_complex_def)

lemma [simp]:
  assumes v: "vertex_in_simplicial_complex x K"
  shows "K \<noteq> {{}}"
  using v
  by (metis empty_iff singletonD vertex_in_simplicial_complex_def)

lemma
  vertex_in_simplicial_complex_singleton [simp]:
  assumes v: "vertex_in_simplicial_complex x K"
    and s: "simplicial_complex V K"
  shows "{x} \<in> K"
  using v s unfolding vertex_in_simplicial_complex_def simplicial_complex_def by auto

lemma
  link_cone_cone_link:
  assumes x: "x \<in> V"
    and xk: "vertex_in_simplicial_complex x K"
    and xv: "x \<noteq> v"
    and s: "simplicial_complex V K"
  shows "link x (V \<union> {v}) (cone_simplices v K) = cone_simplices v (link x (V \<union> {v}) K)"
proof (rule)
  show "link x (V \<union> {v}) (cone_simplices v K) \<subseteq> cone_simplices v (link x (V \<union> {v}) K)"
  proof
    fix xa :: "'a set"
    assume xa: "xa \<in> link x (V \<union> {v}) (cone_simplices v K)"
    hence xa_pow: "xa \<in> Pow (V \<union> {v} - {x})"
          and xa_car: "xa \<union> {x} \<in> {{}, {v}} \<union> K \<union> {x. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>K. x = y \<union> y'}"
      unfolding link_def cone_simplices_def simplices_def join_simplices_def by fast+
    show "xa \<in> cone_simplices v (link x (V \<union> {v}) K)"
      using xa xa_pow x s xk xv
      unfolding link_def
      unfolding cone_simplices_def
      unfolding join_simplices_def
      unfolding vertex_in_simplicial_complex_def
      unfolding simplicial_complex_def link_def cone_simplices_def simplices_def join_simplices_def
      proof (cases "xa \<union> {x} \<in> {{}, {v}}")
        case True then show "xa \<in> {{}, {v}} \<union> {s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K} \<union>
          {xa. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>{s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}. xa = y \<union> y'}" by auto
      next
        case False
        note xa_not = False
        show "xa \<in> {{}, {v}} \<union> {s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K} \<union>
          {xa. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>{s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}. xa = y \<union> y'}"
        proof (cases "xa \<union> {x} \<in> K")
          case True then show ?thesis using xa_not xa_pow by simp
        next
          case False
          note xa_x_not_in_K = False
          then have xa_in: "xa \<union> {x} \<in> {x. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>K. x = y \<union> y'}"
            using xa_not xa_car by auto
          then obtain y y'
            where y: "y\<in>{{}, {v}}" and y': "y'\<in> K" and xa_x: "xa \<union> {x} = y \<union> y'" by auto
          show ?thesis
          proof (cases "y = {}")
            case True
            with xa_in and y and xa_x have "xa \<union> {x} = y'" by auto
            hence "xa \<union> {x} \<in> K" using y' by fast
            hence False using xa_x_not_in_K by fast
            thus ?thesis by fast
          next
            case False hence yv: "y = {v}" using y by fast
            hence "xa \<union> {x} = y' \<union> {v}" using xa_x by fast
            hence xa: "xa = (y' - {x}) \<union> {v}"
              using xa_pow xv by blast
            have "xa \<in> {xa. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>{s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}. xa = y \<union> y'}"
            proof (rule, rule bexI [of _ y], rule bexI [of _ "y' - {x}"])
              show "y \<in> {{}, {v}}" using yv by fast
              show "xa = y \<union> (y' - {x})" using xa yv by fast
              show "y' - {x} \<in> {s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}"
              proof (rule, rule conjI)
                show "y' - {x} \<in> Pow (V \<union> {v} - {x})" using xa_pow xa by simp
                show "y' - {x} \<union> {x} \<in> K" using y'
                  by (metis UnE UnI2 Un_insert_right insert_Diff singleton_iff sup_bot_right xa_x xv yv)
              qed
            qed
            thus ?thesis by fast
          qed
        qed
      qed
    qed
 show "cone_simplices v (link x (V \<union> {v}) K) \<subseteq> link x (V \<union> {v}) (cone_simplices v K)"
  proof
    fix xa :: "'a set"
    assume xa: "xa \<in> cone_simplices v (link x (V \<union> {v}) K)"
    hence xa_in: "xa \<in> {{}, {v}} \<union> {s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K} \<union>
        {xa. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>{s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}. xa = y \<union> y'}"
      unfolding cone_simplices_def join_simplices_def link_def simplices_def by fast
    from xk have empty_in_K: "{} \<in> K"
      unfolding vertex_in_simplicial_complex_def
      using s simplicial_complex_either_empty_or_contains_empty by auto
    show "xa \<in> link x (V \<union> {v}) (cone_simplices v K)"
    proof (cases "xa \<in> {{}, {v}}")
      case True
      show ?thesis
        unfolding cone_simplices_def join_simplices_def link_def simplices_def
      proof (rule, rule conjI)
        show "xa \<in> Pow (V \<union> {v} - {x})" using xa_in xv by auto
        show "xa \<union> {x} \<in> {{}, {v}} \<union> K \<union> {x. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>K. x = y \<union> y'}"
          using True using vertex_in_simplicial_complex_singleton [OF xk s] by auto
      qed
      next
        case False
        note xa_not_v = False
        show ?thesis
        proof (cases "xa \<in> {s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}")
          case True
          then show ?thesis
          unfolding cone_simplices_def join_simplices_def link_def simplices_def by simp
        next
          case False with xa_in xa_not_v
          have xa_union: "xa \<in> {xa. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>{s \<in> Pow (V \<union> {v} - {x}). s \<union> {x} \<in> K}. xa = y \<union> y'}" 
            by fast
          have "xa \<in> {s \<in> Pow (V \<union> {v} - {x}).
            s \<union> {x} \<in> {x. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>K. x = y \<union> y'}}"
          proof (rule, rule conjI)
           show "xa \<in> Pow (V \<union> {v} - {x})" 
             using xa_union xv by blast
           show "xa \<union> {x} \<in> {x. \<exists>y\<in>{{}, {v}}. \<exists>y'\<in>K. x = y \<union> y'}"
             using xa_union xv by auto
         qed
         thus ?thesis
           unfolding cone_simplices_def join_simplices_def link_def simplices_def by auto
      qed
    qed
  qed
qed

corollary
  link_cone_cone_link_external_vertex:
  assumes x: "x \<in> V"
    and xk: "vertex_in_simplicial_complex x K"
    and v: "v \<notin> V"
    and s: "simplicial_complex V K"
  shows "link x (V \<union> {v}) (cone_simplices v K) = cone_simplices v (link x (V \<union> {v}) K)"
  using link_cone_cone_link [OF x xk _ s, of v] using x v by auto

corollary
  link_cone_cone_link_internal_vertex:
  assumes x: "x \<in> V"
    and xk: "vertex_in_simplicial_complex x K"
    and v: "v \<in> V"
    and xv: "x \<noteq> v"
    and s: "simplicial_complex V K"
  shows "link x V (cone_simplices v K) = cone_simplices v (link x V K)"
  using link_cone_cone_link [OF x xk xv s] using insert_absorb [OF v] by simp

lemma
  cost_invariant:
  assumes s: "simplicial_complex V K"
  shows "(cost x (V \<union> {v}) K) = (cost x V K)"
  using s
  unfolding simplicial_complex_def simplices_def cost_def by auto

lemma
  link_invariant:
  assumes s: "simplicial_complex V K"
  shows "(link x (V \<union> {v}) K) = (link x V K)"
  using s
  unfolding simplicial_complex_def simplices_def link_def by auto

lemma
  non_evasive_cone:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
  shows "non_evasive (V \<union> {v}) (cone_simplices v K)"
using f s proof (induct "card V" arbitrary: K V)
  case 0
  have "V = {}" using 0 by simp
  then show ?case unfolding 0 using non_evasive.simps (2) [of "{} \<union> {v}"] by fast
next
  case (Suc n)
    assume ind: "\<And>V K. n = card V \<Longrightarrow>
      finite V \<Longrightarrow>
      simplicial_complex V K \<Longrightarrow> non_evasive (V \<union> {v}) (cone_simplices v K)"
    and c: "Suc n = card V"
    and f: "finite V"
    and s: "simplicial_complex V K"
  have fVv: "finite (V \<union> {v})" using f by fast
  show "non_evasive (V \<union> {v}) (cone_simplices v K)"
  proof (unfold non_evasive.simps (2) [OF fVv, of "(cone_simplices v K)"])
    show "\<exists>x\<in>V \<union> {v}.
       V \<union> {v} = {x} \<or>
       non_evasive (V \<union> {v} - {x}) (link x (V \<union> {v}) (cone_simplices v K)) \<and>
       non_evasive (V \<union> {v} - {x}) (cost x (V \<union> {v}) (cone_simplices v K))"
     proof (cases "V = {v}")
      case True show ?thesis unfolding True by fast
    next
      case False
      with c obtain x where x: "x \<in> V" and x_n_v: "x \<noteq> v"
        by (metis card.empty is_singletonI' is_singleton_the_elem nat.simps(3) singletonI)
      show ?thesis
      proof (rule bexI [of _ x])
        show "x \<in> V \<union> {v}" using x by fast
        have "non_evasive (V \<union> {v} - {x}) (link x (V \<union> {v}) (cone_simplices v K)) \<and>
          non_evasive (V \<union> {v} - {x}) (cost x (V \<union> {v}) (cone_simplices v K))"
        proof (rule conjI)
          have cccc: "cost x (V \<union> {v}) (cone_simplices v K) = cone_simplices v (cost x (V \<union> {v}) K)"
            using cost_cone_cone_cost [OF x_n_v x, of K] .
          have vvx: "V \<union> {v} - {x} = V - {x} \<union> {v}" using x_n_v by auto
          show "non_evasive (V \<union> {v} - {x}) (cost x (V \<union> {v}) (cone_simplices v K))"
            unfolding cccc vvx
          proof (rule ind)
           show "n = card (V - {x})" by (metis c card_Diff_singleton diff_Suc_1 x)
           show "finite (V - {x})" using f by blast
           show "simplicial_complex (V - {x}) (cost x (V \<union> {v}) K)" 
             unfolding cost_invariant [OF s, of x v]
             by (simp add: s simplicial_complex_cost)
         qed
         show "non_evasive (V \<union> {v} - {x}) (link x (V \<union> {v}) (cone_simplices v K))"
         proof (cases "vertex_in_simplicial_complex x K")
           case True
           have lclc: "link x (V \<union> {v}) (cone_simplices v K) = cone_simplices v (link x (V \<union> {v}) K)"
              using link_cone_cone_link [OF x True x_n_v s] .
           show ?thesis unfolding lclc vvx
           proof (rule ind)
            show "n = card (V - {x})" by (metis c card_Diff_singleton diff_Suc_1 x)
            show "finite (V - {x})" using f by blast
            show "simplicial_complex (V - {x}) (link x (V \<union> {v}) K)" 
              unfolding link_invariant [OF s, of x v]
             by (simp add: s simplicial_complex_link)
           qed
         next
         case False
         then have link_empty: "(link x (V \<union> {v}) (cone_simplices v K)) = {}"
           unfolding vertex_in_simplicial_complex_def
           unfolding link_def simplices_def cone_simplices_def join_simplices_def
           using x_n_v
           by auto
         show ?thesis
           unfolding link_empty
           using non_evasive_empty_simplicial [of "V \<union> {v} - {x}"]
           using fVv vvx by blast
       qed
     qed
     thus " V \<union> {v} = {x} \<or>
          non_evasive (V \<union> {v} - {x}) (link x (V \<union> {v}) (cone_simplices v K)) \<and>
          non_evasive (V \<union> {v} - {x}) (cost x (V \<union> {v}) (cone_simplices v K))" by fast
   qed
  qed
 qed
qed

corollary non_evasive_cone_external_vertex:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and v: "v \<notin> V"
  shows "non_evasive (V \<union> {v}) (cone_simplices v K)"
  using non_evasive_cone [OF s f, of v] .

corollary non_evasive_cone_internal_vertex: 
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and v: "v \<in> V"
  shows "non_evasive V (cone_simplices v K)"
  using non_evasive_cone [OF s f, of v] using insert_absorb [OF v] by simp

lemma
  non_evasive_vertex_irrelevant:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and w: "w \<in> V"
    and v: "\<not> vertex_in_simplicial_complex w K"
  shows "non_evasive V K"
  using f w v proof (induct "card V" arbitrary: V K)
  case 0
  show ?case using 0 (1,2,3) by simp
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True show ?thesis 
      using True using Suc (2)
      by (metis Suc.prems(1) Suc.prems(2) card_1_singleton_iff empty_iff insertE non_evasive.simps(2))
  next
    case False then obtain x where x: "x \<in> V" and x_n_w: "x \<noteq> w"
      using Suc (2)
      by (metis Suc.prems(1) Suc_le_mono card_le_Suc0_iff_eq le_antisym zero_le)
    have "non_evasive (V - {x}) (link x V K) \<and> non_evasive (V - {x}) (cost x V K)"
    proof (rule conjI)
      show "non_evasive (V - {x}) (link x V K)"
      proof (rule Suc (1))
       show "n = card (V - {x})"
        by (metis Suc.hyps(2) card_Diff_singleton diff_Suc_1 x)
       show "finite (V - {x})" using Suc.prems(1) by blast
       show "w \<in> V - {x}" using x_n_w using Suc.prems(2) by blast
       show "\<not> vertex_in_simplicial_complex w (link x V K)"
        using Suc (5)
        unfolding link_def vertex_in_simplicial_complex_def simplices_def by auto
       qed
      show "non_evasive (V - {x}) (cost x V K)"
      proof (rule Suc (1))
       show "n = card (V - {x})"
         by (metis Suc.hyps(2) card_Diff_singleton diff_Suc_1 x)
         show "finite (V - {x})" using Suc.prems(1) by blast
         show "w \<in> V - {x}" using x_n_w using Suc.prems(2) by blast
         show "\<not> vertex_in_simplicial_complex w (cost x V K)" 
           using Suc (5)
           unfolding cost_def vertex_in_simplicial_complex_def simplices_def by auto
      qed
    qed
    thus ?thesis using non_evasive.simps (2) [OF Suc (3), of K] using x by blast
  qed
qed

corollary non_evasive_link:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and x: "x \<in> V"
  shows "non_evasive V (link x V K)"
proof (rule non_evasive_vertex_irrelevant [OF _ f x])
  show "simplicial_complex V (link x V K)" 
    using simplicial_complex_link [OF s, of x]
    unfolding link_def simplicial_complex_def simplices_def by auto
  show "\<not> vertex_in_simplicial_complex x (link x V K)"
    using vertex_not_in_link [OF s x] .
qed

corollary non_evasive_cost:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and x: "x \<in> V"
  shows "non_evasive V (cost x V K)"
proof (rule non_evasive_vertex_irrelevant [OF _ f x])
  show "simplicial_complex V (cost x V K)" 
    using simplicial_complex_cost [OF s, of x]
    unfolding cost_def simplicial_complex_def simplices_def by auto
  show "\<not> vertex_in_simplicial_complex x (cost x V K)"
    using vertex_not_in_cost [OF s x] .
qed

section\<open>Dismantelable simplicial complexes\<close>

function dismantelable :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where
   "dismantelable {} K = False"
 | "finite V \<Longrightarrow> dismantelable V K = (\<exists>x\<in>V. V = {x} 
      \<or> (\<exists>k\<in>V. k \<noteq> x \<and> (cone k (link x V K)) \<and> dismantelable (V - {x}) (cost x V K)))"
 | "\<not> finite V \<Longrightarrow> dismantelable V K = False"
  unfolding link_def cost_def simplices_def by auto+
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  fix V :: "'a set" and K :: "'a set set" and x :: "'a"
  assume f: "finite V" and x: "x \<in> V"
  show "((V - {x}, cost x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using f x by auto (metis card_gt_0_iff diff_Suc_less empty_iff)
qed simp

lemma
  dismantelable_implies_non_evasive:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and d: "dismantelable V K"
  shows "non_evasive V K"
  using s f d proof (induct "card V" arbitrary: V K)
  case 0
  hence es: "V = {}" by simp
  show ?case 
    using "0.prems"(3)
    unfolding es
    unfolding dismantelable.simps(1) by blast
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True show ?thesis 
      using True using Suc (2)
      using non_evasive.simps(2) [OF Suc (4), of K]
      by (metis card_1_singleton_iff singletonI)
  next
    case False then obtain x k where x: "x \<in> V" and k: "k \<in> V" and kx: "k \<noteq> x"
      and cx: "cone k (link x V K)" and dx: "dismantelable (V - {x}) (cost x V K)"
      using Suc (2)
      using Suc (5)
      unfolding dismantelable.simps (2) [OF Suc (4), of K] by auto
    have "non_evasive (V - {x}) (link x V K) \<and> non_evasive (V - {x}) (cost x V K)"
    proof (rule conjI)
      show "non_evasive (V - {x}) (cost x V K)"
      proof (rule Suc (1))
       show "n = card (V - {x})"
        by (metis Suc.hyps(2) card_Diff_singleton diff_Suc_1 x)
       show "finite (V - {x})" using Suc.prems (2) by blast
       show "simplicial_complex (V - {x}) (cost x V K)"
         using simplicial_complex_cost [OF Suc.prems (1), of x] .
       show "dismantelable (V - {x}) (cost x V K)"
         using dx .
     qed
     have l_c: "(link x V K) = (cone_simplices k (link x V K))"
       using cx using coneI [OF cx] by simp
     have "non_evasive (V - {x}) (cone_simplices k (link x V K))"
     proof (rule non_evasive_cone_internal_vertex)
       show "simplicial_complex (V - {x}) (link x V K)"
         using simplicial_complex_link [OF Suc (3), of x] .
       show "finite (V - {x})" using Suc (4) by simp
       show "k \<in> V - {x}" using k kx by simp
     qed
     thus "non_evasive (V - {x}) (link x V K)" by (subst l_c, safe)
   qed
   thus ?thesis unfolding non_evasive.simps (2) [OF Suc (4), of K] using x by blast
 qed
qed

section\<open>$m$-Vertex reducible simplicial complexes.\<close>

function m_vertex_reducible :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where
   "m_vertex_reducible 0 V K = dismantelable V K"
 | "finite V \<Longrightarrow> m_vertex_reducible (Suc m) V K = (\<exists>x\<in>V. V = {x} 
      \<or> ((m_vertex_reducible m (V - {x}) (link x V K)) \<and> m_vertex_reducible (Suc m) (V - {x}) (cost x V K)))"
 | "\<not> finite V \<Longrightarrow> m_vertex_reducible m V K = False"
  unfolding link_def cost_def simplices_def apply auto
   using not0_implies_Suc by blast
termination proof (relation "Wellfounded.measure (\<lambda>(m,V,K). card V)")
  fix m :: nat and V :: "'a set" and K :: "'a set set" and x :: "'a"
  assume f: "finite V" and x: "x \<in> V"
  show "((m, V - {x}, link x V K), Suc m, V, K) \<in> measure (\<lambda>(m, V, K). card V)"
    using f x by auto (metis card_gt_0_iff diff_Suc_less empty_iff)
  show "((Suc m, V - {x}, cost x V K), Suc m, V, K) \<in> measure (\<lambda>(m, V, K). card V)"
    using f x by auto (metis card_gt_0_iff diff_Suc_less empty_iff)
qed simp

lemma
  m_vertex_reducible_implies_non_evasive:
  assumes s: "simplicial_complex V K"
    and f: "finite V"
    and d: "m_vertex_reducible m V K"
  shows "non_evasive V K"
  using s f d proof (induct "m" arbitrary: V K)
  case 0
  show ?case using 0 (3) unfolding m_vertex_reducible.simps (1) 
    using dismantelable_implies_non_evasive [OF 0 (1,2)] by fast
next
  case (Suc m)
  note ind = Suc (1)
  note s = Suc (2)
  note f = Suc (3)  
  note m = Suc (4)
  show ?case using s m f
  proof (induct "card V" arbitrary: V K)
    case 0 have False using 0 unfolding m_vertex_reducible.simps (2) [OF 0 (4)] by simp
    thus ?case by simp
  next
    case (Suc n)
    show ?case
    proof (cases "n = 0")
      case True
      then obtain x where V: "V = {x}" using Suc (2)
        by (metis card_1_singleton_iff) 
      show ?thesis unfolding V by simp
    next
      case False
      then obtain x where x: "x \<in> V"
        and m_link: "m_vertex_reducible m (V - {x}) (link x V K)" 
        and m_cost: "m_vertex_reducible (Suc m) (V - {x}) (cost x V K)"
      using Suc (4) Suc (2)
      using m_vertex_reducible.simps (2) [OF Suc (5), of m K] by auto
      have "non_evasive (V - {x}) (link x V K) \<and> non_evasive (V - {x}) (cost x V K)"
      proof (rule conjI)
        show "non_evasive (V - {x}) (link x V K)"
        proof (rule ind)
          show "simplicial_complex (V - {x}) (link x V K)" 
            using simplicial_complex_link [OF Suc (3), of x] .
          show "finite (V - {x})" using Suc (5) by simp
          show "m_vertex_reducible m (V - {x}) (link x V K)" using m_link .
        qed
        show "non_evasive (V - {x}) (cost x V K)" thm Suc
        proof (rule Suc (1))
          show "n = card (V - {x})"
            by (metis Suc (2) card_Diff_singleton diff_Suc_1 x)
          show "simplicial_complex (V - {x}) (cost x V K)"
            using simplicial_complex_cost [OF Suc (3), of x] .
          show "m_vertex_reducible (Suc m) (V - {x}) (cost x V K)"
            using m_cost .
          show "finite (V - {x})" using Suc (5) by simp
        qed
      qed
      thus ?thesis unfolding non_evasive.simps (2) [OF Suc (5), of K] using x by blast
    qed
  qed
qed

section\<open>Relationship between the notion of \emph{non evasive} 
  for ROBDD and simplicial complexes.\<close>

text\<open>We first state some general results about the height of 
   @{typ "'a ifex"} expressions.\<close>

text\<open>The function @{term restrict_top} takes a @{typ "'a ifex"}
  expression, a variable and a boolean. If the variable is at the
  top of the @{term IF} expression then it uses the boolean 
  value to produce the corresponding subexpression. Otherwise, 
  it keeps the original @{term IF} expression.\<close>

lemma height_restrict_le: "height (restrict_top k var val) \<le> height k"
  by (induction k, auto)

lemma height_restrict_less:
  "ifex_top_var k = Some var \<Longrightarrow> height (restrict_top k var val) < height k"
  by (induction k, auto)

lemma height_restrict_some_less:
  "lowest_tops [i, t, e] = Some xa \<Longrightarrow>
  (height (restrict_top i xa val) + height (restrict_top t xa val) + height (restrict_top e xa val)) 
    < (height i + height t + height e)"
  using height_restrict_le[of i xa val] height_restrict_le[of t xa val] height_restrict_le[of e xa val]
  by (auto dest!: lowest_tops_cases height_restrict_less[of _ _ val])

lemma height_IF:
  "height (IF v t e) \<le> max (height t) (height e) + 1"
  unfolding IFC_def by simp

text\<open>The @{term IFC} function takes as parameters a variable and two
   @{typ "'a ifex"} expressions. If the expressions are the same,
    then it returns either of them. Otherwise, it builds the
   @{term "IF"} expression with the variable and the
    two subtrees.\<close>

lemma height_IFC:
  "height (IFC v t e) \<le> max (height t) (height e) + 1"
  unfolding IFC_def by simp

lemma 
  max_card_le_card_union:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> max (card A) (card B) \<le> card (A \<union> B)"
  by (auto simp add: card_mono)+

text\<open>If we assume that we have an @{typ "'a ifex"} which is 
  @{term ifex_minimal} and @{term ifex_ordered}, then its height 
  is less than or equal to its number of variables.\<close>

lemma
  height_ro_le_var_set:
  assumes r: "ro_ifex i"
  shows "height i \<le> card (ifex_var_set i)"
  using r proof (induct i)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 i1 i2)
  from IF.prems have roi1: "ro_ifex i1" and roi2: "ro_ifex i2" by simp+
  have fi1: "finite (ifex_var_set i1)" and fi2: "finite (ifex_var_set i2)" by simp+
  have ifx1i1i2: "ifex_var_set (IF x1 i1 i2) = {x1} \<union> ifex_var_set i1 \<union> ifex_var_set i2"
    using IF.prems by simp
  have "height (IF x1 i1 i2) \<le> 1 + max (height i1) (height i2)" by simp
  also have "... \<le> 1 + max (card (ifex_var_set i1)) (card (ifex_var_set i2))"
    using IF (1) [OF roi1] IF (2) [OF roi2] by auto
  also have "... \<le> card (ifex_var_set (IF x1 i1 i2))" 
    using roifex_var_not_in_subtree [OF IF.prems, of x1 i1 i2] 
    unfolding ifx1i1i2
    using max_card_le_card_union by auto
  finally show ?case .
qed

corollary
  height_ro_le_var:
  assumes r: "ro_ifex i"
  shows "height i \<le> length (ifex_vars i)"
  using height_ro_le_var_set [OF r]
  using card_length dual_order.trans by blast

corollary
  height_mkifex_le_var_set:
  fixes f vars
  defines "l \<equiv> mk_ifex f vars"
  shows "height l \<le> card (ifex_var_set l)"
    using height_ro_le_var_set [OF mk_ifex_ro] unfolding l_def .

definition boolfunc_to_vec :: "nat \<Rightarrow> (nat boolfunc) \<Rightarrow> (bool vec => bool)"
  where "boolfunc_to_vec n f = (\<lambda>v. f (vec_index v))"

lemma
  assumes mk: "mk_ifex f [0..<n] = (IF x1 i1 i2)"
  shows "link x1 {..<n} (simplicial_complex_induced_by_monotone_boolean_function 
    n (boolfunc_to_vec n f)) = 
  (simplicial_complex_induced_by_monotone_boolean_function 
    n (boolfunc_to_vec n (bf_restrict x1 False f)))"
  using mk proof (induction n arbitrary: x1 i1 i2)
  case 0
  then show ?case unfolding mk_ifex.simps
    by (metis ifex.distinct(3) ifex.distinct(5) mk_ifex.simps(1) upt_0)
next
  case (Suc n)
  then show ?case sorry
qed

lemma
  shows "height (mk_ifex f l) \<le> length l"
proof (induct "length l" arbitrary: l f) 
  case 0
  show ?case using 0 by simp
next
  case (Suc n)
  from Suc (2) obtain l' x' where l_suc: "l = x' # l'" and ll': "length l' = n"    
    by (meson Suc_length_conv)
  have ht: "height (mk_ifex (bf_restrict x' True f) l') \<le> n"
    and hf: "height (mk_ifex (bf_restrict x' False f) l') \<le> n"
    using Suc (1) [of l'] ll' by simp_all
  show ?case 
    unfolding l_suc
    unfolding mk_ifex.simps using ht hf apply auto try
  apply simp
  try

lemma
  assumes ne: "\<not> Evasive.evasive (Suc n) f"
  and f: "boolean_functions.monotone_bool_fun (Suc n) f"
 shows "non_evasive ({..<Suc n} - {0}) (link 0 {..<Suc n} (simplicial_complex_induced_by_monotone_boolean_function n f))"
using ne f proof (induct "card {..<n}" arbitrary: n)
  case 0
  from 0 (1) have n: "n = 0" by simp
  have False using 0 (2) unfolding n unfolding Evasive.evasive_def apply auto try show ?case unfolding n apply auto try
  


lemma "\<not> non_evasive {1, 2} {{2::nat}}"
  using non_evasive.simps(2) [of "{1,2}" "{{2}}"]
  unfolding link_def cost_def simplices_def
  sorry

lemma subfunction_0_commute:
  fixes f :: "bool vec \<Rightarrow> bool" and v :: "bool vec"
  assumes v: "v \<in> carrier_vec n" and f: "f v"
  and mn2: "mono_on f (carrier_vec (n + 2))"
  and i: "i < n" and j: "j < n"
  shows "(subfunction_0_dim (subfunction_0_dim f i) j) v=
    (subfunction_0_dim (subfunction_0_dim f j) i) v"
  unfolding subfunction_0_dim_def
  apply (rule cong [of f], simp)
  unfolding vec_aug_def
  unfolding dim_vec
  apply (intro eq_vecI)
   prefer 2
  apply simp
  using v i j mn2 f
  unfolding carrier_vec_def dim_vec mono_on_def less_eq_vec_def
  apply auto try




definition subtable_0 :: "(bool vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool vec"
  where "subtable_0 f n = boolean_function_to_bool_vec (n div 2) (subfunction_0 f)"

value "list_of_vec (subtable_0 (bool_fun_threshold 3) 16)"

value "list_of_vec (first_half (boolean_function_to_bool_vec 16 (bool_fun_threshold 3)))"

definition subtable_1 :: "(bool vec \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool vec"
  where "subtable_1 f n = boolean_function_to_bool_vec (n div 2) (subfunction_1 f)"

value "list_of_vec (subtable_1 (bool_fun_threshold 3) 16)"

value "list_of_vec (second_half (boolean_function_to_bool_vec 16 (bool_fun_threshold 3)))"

lemma
  shows "first_half (boolean_function_to_bool_vec n f) = subtable_0 f n"
  unfolding first_half_def
  unfolding boolean_function_to_bool_vec_def
  unfolding dim_vec
  unfolding subtable_0_def
  unfolding boolean_function_to_bool_vec_def
  unfolding subfunction_0_def
  unfolding nat_to_bool_vec_def
proof (intro eq_vecI, unfold dim_vec) try
  show "n div 2 = n div 2" by fast
  fix i
  assume "i < n div 2"
  have "(vec n (\<lambda>i. f (vec n (bit i))) $ i = 
   f (vec (n div 2)
                    (\<lambda>ia. if ia = n div 2 - 1 then False
                           else vec (n div 2) (bit i) $ ia)))"
    sorry
  then
  show "vec (n div 2) (($) (vec n (\<lambda>i. f (vec n (bit i))))) $ i =
         vec (n div 2)
          (\<lambda>i. f (vec (n div 2)
                    (\<lambda>ia. if ia = n div 2 - 1 then False
                           else vec (n div 2) (bit i) $ ia))) $
         i " using eq_vecI


lemma "bead (boolean_function_to_bool_vec n f) \<equiv> (subtable_0 f n \<noteq> subtable_1 f n)"
  unfolding bead_def
  unfolding first_half_def
  unfolding second_half_def
  unfolding boolean_function_to_bool_vec_def
  unfolding dim_vec
  


definition beads_of_a_boolean_function :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> (bool vec) set"
  where "beads_of_a_boolean_function n f = (boolean_function_to_bool_vec n f)


text\<open>How to generate all the beads (size 1 to size n) of a boolean function???\<close>

definition beads_of_a_boolean_function :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> (bool vec) set"
  where "beads_of_a_boolean_function n f = (boolean_function_to_bool_vec n f)


context boolean_functions
begin


end




end