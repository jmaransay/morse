
theory Evasive
  imports
    Bij_betw_simplicial_complex_bool_func
    MkIfex
begin

section\<open>Relation between boolean functions over vectors and boolfunc as in ROBDD\<close>

definition vec_to_boolfunc :: "(bool^'n => bool) => 'n boolfunc"
  where "vec_to_boolfunc f = (\<lambda>i. f (vec_lambda i))"

lemma
  ris: "reads_inside_set (\<lambda>i. bool_fun_threshold_2_3 (vec_lambda i)) (set [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])"
  unfolding reads_inside_set_def
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  by (metis (no_types, hide_lams) UNIV_I UNIV_finite_mod_4 finite_mod_4_enum mem_Collect_eq subsetI subset_antisym vec_lambda_beta)

lemma
  shows "val_ifex (mk_ifex (vec_to_boolfunc bool_fun_threshold_2_3) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])
    = vec_to_boolfunc bool_fun_threshold_2_3"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  unfolding vec_to_boolfunc_def
  using ris .

text\<open>Given any Boolean function over an enumerable and linearly ordered type,
  its ifex representation is ifex_ordered and ifex_minimal.\<close>

lemma mk_ifex_boolean_function: 
  fixes f :: "bool^'n::{enum,linorder} => bool"
  shows "ro_ifex (mk_ifex (vec_to_boolfunc f) enum_class.enum)"
  using mk_ifex_ro by fast

text\<open>Any Boolean function over a finite type can be 
  seen as an expression over the underlying set of variables.\<close>

lemma
  reads_inside_set_boolean_function:
  fixes f :: "bool^'n => bool"
  shows "reads_inside_set (vec_to_boolfunc f) (UNIV::'n set)"
  by (smt (verit, del_insts) iso_tuple_UNIV_I reads_inside_set_def vec_eq_iff vec_lambda_beta vec_to_boolfunc_def)

text\<open>Any Boolean function over an enumerable and linearly ordered type
  (and in particular, over class_mod_type) is equal to its ifex representation 
  by means of mk_ifex.\<close>

lemma
  mk_ifex_equivalence:
  fixes f :: "bool^'n::{enum,linorder} => bool"
  shows "val_ifex (mk_ifex (vec_to_boolfunc f) (enum_class.enum::'n list))
    = vec_to_boolfunc f"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  using reads_inside_set_boolean_function [of f]
  unfolding enum_class.UNIV_enum [symmetric] .

definition bcount_true :: "('a => bool) => nat"
  where "bcount_true f = card {i. f i}"

definition boolfunc_threshold_2_3 :: "(finite_mod_4 => bool) => bool"
  where "boolfunc_threshold_2_3 = (\<lambda>v. if 2 \<le> bcount_true v then True else False)"

definition proj_2 :: "(finite_mod_4 => bool) => bool"
  where "proj_2 = (\<lambda>v. v a\<^sub>2)"

definition proj_2_n3 :: "(finite_mod_4 => bool) => bool"
  where "proj_2_n3 = (\<lambda>v. v a\<^sub>2 \<and> \<not> v a\<^sub>3)"

fun height :: "'a ifex => nat"
  where "height Trueif = 0"
  | "height Falseif = 0"
  | "height (IF v va vb) = 1 + max (height va) (height vb)"  

value "mk_ifex (boolfunc_threshold_2_3) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]"

value "height (mk_ifex (boolfunc_threshold_2_3) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3])"

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

definition evasive :: "(('a::{linorder,enum} => bool) => bool) => bool"
  where "evasive f \<equiv> (height (mk_ifex f enum_class.enum)) = CARD ('a)"

lemma "height (mk_ifex (boolfunc_threshold_2_3) [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]) = 4"
  sorry

lemma "evasive boolfunc_threshold_2_3"
  sorry

lemma "\<not> evasive proj_2"
  sorry 

end