
theory BDD
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

definition val_vec_ifex :: "'a ifex \<Rightarrow> (bool^'a) \<Rightarrow> bool"
  where "val_vec_ifex ifex v = val_ifex ifex (\<lambda>i. vec_nth v i)"

lemma "val_vec_ifex Trueif (\<chi> i. True)"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex Falseif (\<chi> i. False) = False"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>3 Trueif Falseif) (\<chi> i. if i = a\<^sub>3 then True else False)"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>1 Trueif Falseif) (\<chi> i. if i = a\<^sub>1 then True else False)"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>0 Falseif (IF a\<^sub>1 Trueif Falseif)) (\<chi> i. if i = a\<^sub>1 then True else False)"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>0 Falseif (IF a\<^sub>1 Trueif (IF a\<^sub>2 Falseif (IF a\<^sub>3 Falseif Falseif)))) 
                    (\<chi> i. if i = a\<^sub>1 then True else False)"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>3 Trueif (IF a\<^sub>2 Falseif Falseif)) (\<chi> i. if i = a\<^sub>3 then True else False)"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>2 Trueif Falseif) (\<chi> i. if i = a\<^sub>3 then True else False) = False"
  by (simp add: val_vec_ifex_def)

lemma "val_vec_ifex (IF a\<^sub>2 Trueif Falseif) (\<chi> i. if i = a\<^sub>3 then True else False) = False"
  by (simp add: val_vec_ifex_def)

definition vec_to_pairs_list :: "bool^'n::enum \<Rightarrow> ('n \<times> bool) list"
  where "vec_to_pairs_list v = map (\<lambda>i. (i, v $ i)) enum_class.enum"

fun pairs_list_to_bdd :: "('n \<times> bool) list => 'n ifex"
  where  "pairs_list_to_bdd [] = Falseif"
  | "pairs_list_to_bdd (a # l) = (if (snd a) then IF (fst a) Trueif (pairs_list_to_bdd l) 
                                              else IF (fst a) Falseif (pairs_list_to_bdd l))"

definition boolfunc_to_bdd :: "bool^'n::enum \<Rightarrow> 'n ifex"
  where "boolfunc_to_bdd v = pairs_list_to_bdd (vec_to_pairs_list v)"

lemma "(IF a\<^sub>0 Falseif (IF a\<^sub>1 Trueif (IF a\<^sub>2 Falseif (IF a\<^sub>3 Falseif Falseif)))) =
       boolfunc_to_bdd (\<chi> i. if i = a\<^sub>1 then True else False)"
  unfolding boolfunc_to_bdd_def
  unfolding vec_to_pairs_list_def
  unfolding enum_finite_mod_4_def
  by simp

lemma "(IF a\<^sub>0 Falseif (IF a\<^sub>1 Trueif (IF a\<^sub>2 Falseif (IF a\<^sub>3 Falseif Falseif)))) \<noteq>
        (IF a\<^sub>1 Trueif Falseif)"
  by simp

lemma "vec_to_boolfunc (\<lambda>x. True) = bf_True"
  unfolding vec_to_boolfunc_def ..

lemma "vec_to_boolfunc (bool_fun_top) = bf_True"
  unfolding vec_to_boolfunc_def bool_fun_top_def ..

lemma "vec_to_boolfunc (\<lambda>x. False) = bf_False"
  unfolding vec_to_boolfunc_def ..

lemma "vec_to_boolfunc (bool_fun_bot) = bf_False"
  unfolding vec_to_boolfunc_def bool_fun_bot_def ..

end