
theory Evasive
  imports
    Bij_betw_simplicial_complex_bool_func
    MkIfex
begin

section\<open>Relation between boolean functions over vectors and boolfunc as in ROBDD\<close>

definition vec_to_boolfunc :: "nat \<Rightarrow> (bool vec => bool) => (nat boolfunc)"
  where "vec_to_boolfunc n f = (\<lambda>i. f (vec n i))"

lemma
  ris: "reads_inside_set (\<lambda>i. bool_fun_threshold_2_3 (vec 4 i)) (set [0,1,2,3])"
  unfolding reads_inside_set_def
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding set_list_four [symmetric] by simp 

lemma
  shows "val_ifex (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0,1,2,3])
    = vec_to_boolfunc 4 bool_fun_threshold_2_3"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  unfolding vec_to_boolfunc_def
  using ris .

text\<open>Given any Boolean function over an enumerable and linearly ordered type,
  its ifex representation is ifex_ordered and ifex_minimal.\<close>

lemma mk_ifex_boolean_function: 
  fixes f :: "bool vec => bool"
  shows "ro_ifex (mk_ifex (vec_to_boolfunc n f) [0..n])"
  using mk_ifex_ro by fast

text\<open>Any Boolean function of a finite dimension can be 
  seen as an expression over the underlying set of variables.\<close>

lemma
  reads_inside_set_boolean_function:
  fixes f :: "bool vec => bool"
  shows "reads_inside_set (vec_to_boolfunc n f) {..<n}"
  unfolding vec_to_boolfunc_def
  unfolding reads_inside_set_def
  by (smt (verit, best) dim_vec eq_vecI index_vec lessThan_iff)

text\<open>Any Boolean function of a finite dimension 
  is equal to its ifex representation 
  by means of mk_ifex.\<close>

lemma
  mk_ifex_equivalence:
  fixes f :: "bool vec => bool"
  shows "val_ifex (mk_ifex (vec_to_boolfunc n f) [0..n])
    = vec_to_boolfunc n f"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  using reads_inside_set_boolean_function [of n f]
  unfolding reads_inside_set_def by auto

definition bcount_true :: "nat => (nat=> bool) => nat"
  where "bcount_true n f =  (\<Sum>i = 0..<n. if f i then 1 else (0::nat))"

(*definition bcount_true :: "('a => bool) => nat"
  where "bcount_true f = card {i. f i}"*)

definition boolfunc_threshold_2_3 :: "(nat => bool) => bool"
  where "boolfunc_threshold_2_3 = (\<lambda>v. if 2 \<le> bcount_true 4 v then True else False)"

definition proj_2 :: "(finite_mod_4 => bool) => bool"
  where "proj_2 = (\<lambda>v. v a\<^sub>2)"

definition proj_2_n3 :: "(finite_mod_4 => bool) => bool"
  where "proj_2_n3 = (\<lambda>v. v a\<^sub>2 \<and> \<not> v a\<^sub>3)"

fun height :: "'a ifex => nat"
  where "height Trueif = 0"
  | "height Falseif = 0"
  | "height (IF v va vb) = 1 + max (height va) (height vb)"  

value "mk_ifex (boolfunc_threshold_2_3) [0,1,2,3]"

value "height (mk_ifex (boolfunc_threshold_2_3) [0,1,2,3])"

value "(mk_ifex (proj_2) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])"

value "(mk_ifex (proj_2) [a\<^sub>0])"

value "(mk_ifex (proj_2) [a\<^sub>3, a\<^sub>2, a\<^sub>1, a\<^sub>0])"

value "(mk_ifex (proj_2) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]) = (mk_ifex (proj_2) [a\<^sub>3, a\<^sub>2, a\<^sub>1, a\<^sub>0])"

value "height (mk_ifex (proj_2) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])"

value "(mk_ifex (proj_2_n3) [a\<^sub>3, a\<^sub>2, a\<^sub>1, a\<^sub>0])"

value "(mk_ifex (proj_2_n3) enum_class.enum)"

value "(mk_ifex (proj_2_n3) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]) = (mk_ifex (proj_2_n3) [a\<^sub>3, a\<^sub>2, a\<^sub>1, a\<^sub>0])"

value "height (mk_ifex (proj_2_n3) enum_class.enum)"

value "mk_ifex (bf_False) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]"

value "height (mk_ifex (bf_False) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])"

value "mk_ifex (bf_True) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]"

value "height (mk_ifex (bf_True) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])"

text\<open>Now we introduce the definition of evasive boolean function. 
  It is based on the height of the ifex expression of the function\<close>

definition evasive :: "nat => ((nat => bool) => bool) => bool"
  where "evasive n f \<equiv> (height (mk_ifex f [0..n])) = n"

lemma "height (mk_ifex (boolfunc_threshold_2_3) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]) = 4"
  sorry

lemma "evasive boolfunc_threshold_2_3"
  sorry

lemma "\<not> evasive proj_2"
  sorry 

end