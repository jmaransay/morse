
theory Beads
  imports 
    Boolean_functions
    Simplicial_complex
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
    and i_l_m: "i < m"
  shows "vec_aug r k b \<in> carrier_vec m"
    using r unfolding vec_aug_def carrier_vec_def
    using i_l_m by force

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

definition simplices :: "nat set \<Rightarrow> nat set set"
  where "simplices V = Pow V"

lemma "{} \<in> simplices V"
  unfolding simplices_def by simp

lemma
  assumes k: "k \<le> n"
  shows "{0..<k} \<in> simplices {0..<n}"
  using k unfolding simplices_def by simp

lemma finite_simplex:
  assumes "finite V" and "\<sigma> \<in> simplices V"
  shows "finite \<sigma>"
  using assms(1) assms(2) finite_subset simplices_def by auto

text\<open>A simplicial complex (in $n$ vertexes) is a collection of 
  sets of vertexes such that every subset of 
  a set of vertexes also belongs to the simplicial complex.\<close>

definition simplicial_complex :: "nat set \<Rightarrow> nat set set => bool"
  where "simplicial_complex V K \<equiv>  (\<forall>\<sigma>\<in>K. (\<sigma> \<in> simplices V) \<and> (Pow \<sigma>) \<subseteq> K)"

text\<open>The notion of @{term simplicial_complex_card} is defined
  as the number of vertexes of the simplicial complex. 
  It can be identified with the number of variables of the associated
  (monotone) Boolean function. Note that some of these vertexes 
  could not belong to any simplex.\<close>

definition simplicial_complex_card :: "nat set \<Rightarrow> nat set set => nat"
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
  fixes V :: "nat set" and K::"nat set set"
  assumes k: "simplicial_complex V K"
  shows "K = {} \<or> {} \<in> K" using k unfolding simplicial_complex_def Pow_def by auto

lemma 
  finite_simplicial_complex:
  assumes "finite V" and "simplicial_complex V K"
  shows "finite K"
  by (metis assms(1) assms(2) finite_Pow_iff finite_subset simplices_def simplicial_complex_def subsetI)

definition link :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x V K = {s. s \<in> simplices (V - {x}) \<and> s \<union> {x} \<in> K}"

definition cost :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x V K = {s. s \<in> simplices (V - {x}) \<and> s \<in> K}"

value "Pow (set [1,2,3,4::nat])"

value "link 4 (set [0::nat,1,2,3,4,5,6,7,8]) 
        (Pow (set [1,2,3,4,5]) \<union> Pow (set [4,7]) \<union> Pow (set [2,8]))"

value "cost 4 (set [0::nat,1,2,3,4,5,6,7,8]) 
        (Pow (set [1,2,3,4,5]) \<union> Pow (set [4,7]) \<union> Pow (set [2,8]))"

text\<open>The result of operations @{term link} and @{term cost} 
  are simplicial complexes.\<close>

lemma
  assumes s: "simplicial_complex V K"
  shows "simplicial_complex (V - {x}) (link x V K)"
  unfolding link_def
  using s
  unfolding simplicial_complex_def simplices_def by fast

lemma
  assumes s: "simplicial_complex V K"
  shows "simplicial_complex (V - {x}) (cost x V K)"
  unfolding cost_def
  using s
  unfolding simplicial_complex_def simplices_def by fast

text\<open>The number of vertexes  of operations @{term link} and @{term cost} 
  is one less than the number of vertexes in the original simplicial complex.\<close>

lemma
  assumes "simplicial_complex_card V K = n"
    and "x \<in> V"
  shows "simplicial_complex_card (V - {x}) (link x V K) = n - 1"
  using assms(1) assms(2) simplicial_complex_card_def by auto

lemma
  assumes "simplicial_complex_card V K = n"
    and "x \<in> V"
  shows "simplicial_complex_card (V - {x}) (cost x V K) = n - 1"
  using assms(1) assms(2) simplicial_complex_card_def by auto

section\<open>Equivalence between operations @{term link} and @{term cost} 
  with @{term subfunction_0_dim} and @{term subfunction_1_dim}.\<close>

definition
  simplicial_complex_induced_by_monotone_boolean_function
    :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set => (bool vec => bool) => nat set set"
  where "simplicial_complex_induced_by_monotone_boolean_function mp V f =
        {y\<in>simplices V. \<exists>x. dim_vec x = card V \<and> f x \<and> mp ` (ceros_of_boolean_input x) = y}"

text\<open>The following operation is ``equivalent'' to @{term vec_aug}
  for arrays.\<close>

definition set_aug :: "nat set \<Rightarrow> nat \<Rightarrow> nat set"
  where "set_aug A i = (A \<inter> {0..<i}) \<union> {i} \<union> (\<lambda>x. Suc x) ` (A - {0..<i})"

value "set_aug (set [1,3,4,5]) 2"

lemma
  ceros_of_boolean_input_set_aug:
  fixes mp :: "nat \<Rightarrow> nat"
  assumes c: "mp ` (ceros_of_boolean_input v) = A" and i: "i \<le> dim_vec v"
  shows "mp ` (ceros_of_boolean_input (vec_aug v i False)) = mp ` (set_aug A i)"
  using c i
  unfolding ceros_of_boolean_input_def vec_aug_def set_aug_def
  by force (*slow proof*)

lemma
  ceros_of_boolean_input_set_aug:
  assumes c: "ceros_of_boolean_input v = A" and i: "i \<le> dim_vec v"
  shows "ceros_of_boolean_input (vec_aug v i False) = set_aug A i"
  using c i
  unfolding ceros_of_boolean_input_def vec_aug_def set_aug_def
  by force (*slow proof*)

lemma
  assumes k: "simplicial_complex_induced_by_monotone_boolean_function {0..<n} f = K"
  and x: "x < n"
  shows "simplicial_complex_induced_by_monotone_boolean_function ({0..<n} - {x}) (subfunction_0_dim f x) = link x  {0..<n} K"
proof (rule)
  show "simplicial_complex_induced_by_monotone_boolean_function ({0..<n} - {x})
     (subfunction_0_dim f x)
    \<subseteq> link x {0..<n} K"
  proof
    fix y :: "nat set"
    assume y: "y \<in> simplicial_complex_induced_by_monotone_boolean_function ({0..<n} - {x})
                (subfunction_0_dim f x)"
    from y obtain xa :: "bool vec" where d: "dim_vec xa = card ({0..<n} - {x})" 
             and s: "subfunction_0_dim f x xa" and c: "ceros_of_boolean_input xa = y"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def by fast
    from y have y_v_x: "y \<in> simplices ({0..<n} - {x})"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def by simp 
    define y' where "y' = vec_aug xa x False"
    have "set_aug y x \<in> simplices {0..<(n+1)}"
      using y_v_x x unfolding simplices_def set_aug_def by auto
    have cy': "ceros_of_boolean_input y' = set_aug y x"
      unfolding y'_def
      apply (rule ceros_of_boolean_input_set_aug [OF c, of x])
      using x d by simp
    have fy': "f y'" using s unfolding y'_def subfunction_0_dim_def .
    hence "ceros_of_boolean_input y' \<in> K" 
      using k
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      



lemma
  assumes k: "simplicial_complex_induced_by_monotone_boolean_function V f = K"
  and finite: "finite V"
  and x: "x \<in> V"
  shows "simplicial_complex_induced_by_monotone_boolean_function (V - {x}) (subfunction_0_dim f x) = link x V K"
proof (rule)
  show "simplicial_complex_induced_by_monotone_boolean_function (V - {x})
     (subfunction_0_dim f x)
    \<subseteq> link x V K"
  proof
    fix y :: "nat set"
    assume y: "y \<in> simplicial_complex_induced_by_monotone_boolean_function (V - {x})
                (subfunction_0_dim f x)"
    from y obtain xa :: "bool vec" where d: "dim_vec xa = card (V - {x})" 
             and s: "subfunction_0_dim f x xa" and c: "ceros_of_boolean_input xa = y"
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def by fast
    from y have y_v_x: "y \<in> simplices (V - {x})" 
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def by simp 
    define y' where "y' = vec_aug xa x False"
    have "set_aug y x \<in> simplices V"  
      using y_v_x x unfolding simplices_def set_aug_def try
    have cy': "ceros_of_boolean_input y' = set_aug y x" 
      using ceros_of_boolean_input_set_aug [OF c, of x] sorry
    have fy': "f y'" using s unfolding y'_def subfunction_0_dim_def .
    hence "ceros_of_boolean_input y' \<in> K" 
      using k 
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      
      unfolding ceros_of_boolean_input_def y'_def vec_aug_def try
    have dy': "dim_vec y' = card V"
      using d x finite unfolding y'_def vec_aug_def dim_vec
      by (metis add.commute card.remove plus_1_eq_Suc)
   show "y \<in> link x V K"
      unfolding link_def unfolding simplices_def
      using y unfolding simplicial_complex_induced_by_monotone_boolean_function_def

      using k x
      unfolding simplicial_complex_induced_by_monotone_boolean_function_def
      unfolding subfunction_0_dim_def
      unfolding link_def unfolding vec_aug_def unfolding simplices_def apply auto try apply auto try


term "link x V K"

term "subfunction_0_dim f x"


lemma
  assumes "link x V K = subfunction_0_dim f x"




lemma finite_simplices:
  assumes "simplicial_complex K"
  and "v \<in> K"
shows "finite v"
  using assms finite_simplex simplicial_complex.simplicial_complex_def by blast





lemma
  assumes s: "simplicial_complex.simplicial_complex m S"
  shows "simplicial_complex.simplicial_complex (m - 1) S"



context simplicial_complex
begin


definition link :: "nat \<Rightarrow> nat \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x m \<Delta> = {s. s \<in> Pow ({0..<m} - {x}) \<and> s \<union> {x} \<in> \<Delta>}"



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