
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

definition link :: "nat \<Rightarrow> nat \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x m \<Delta> = {s. s \<in> Pow ({0..<m} - {x}) \<and> s \<union> {x} \<in> \<Delta>}"

definition cost :: "nat \<Rightarrow> nat \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x m \<Delta> = {s. s \<in> Pow ({0..<m} - {x}) \<and> s \<in> \<Delta>}"

text\<open>The following does not hold, we should define a notion of
  ``dimension'' of a simplicial complex, which represents the
  number of variables over which it is defined (not the variables themselves).
  \<close>

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