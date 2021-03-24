
theory BDD
  imports 
    Bij_betw_simplicial_complex_bool_func
    "ROBDD.BDD_Examples"
begin

section\<open>Relation between boolean functions over vectors and boolfunc as in ROBDD\<close>

definition vec_to_boolfunc :: "(bool^'n => bool) => 'n boolfunc"
  where "vec_to_boolfunc f = (\<lambda>i. f (vec_lambda i))"

term map

definition vec_to_list :: "bool^'n::{finite, enum} => ('n \<times> bool) list"
  where "vec_to_list v = map (\<lambda>i::'n. (i, v $ i)) (enum_class.enum::'n list)"

text\<open>TODO: - Prove that class_mod_type is a subclass of enum;
           - Define the transformation from a boolean funcion to a bdt\<close>


term sat_list_to_bdt

term vec_to_list

lemma "vec_to_boolfunc (\<lambda>x. True) = bf_True"
  unfolding vec_to_boolfunc_def ..

lemma "vec_to_boolfunc (bool_fun_top) = bf_True"
  unfolding vec_to_boolfunc_def bool_fun_top_def ..

lemma "vec_to_boolfunc (\<lambda>x. False) = bf_False"
  unfolding vec_to_boolfunc_def ..

lemma "vec_to_boolfunc (bool_fun_bot) = bf_False"
  unfolding vec_to_boolfunc_def bool_fun_bot_def ..

lemma "vec_to_boolfunc (bool_fun_threshold_2_3) = bf_False"
  unfolding vec_to_boolfunc_def
  unfolding bool_fun_threshold_2_3_def
  

term sat_list_to_bdt

term eqci
term emptyci 
term litci

term orci
term andci


lemma "<emp> do {
  s \<leftarrow> emptyci;
  (a,s) \<leftarrow> litci 0 s;
  (b,s) \<leftarrow> litci 1 s;
  (c,s) \<leftarrow> litci 2 s;
  (t1i,s) \<leftarrow> orci a b s;
  (t1,s) \<leftarrow> andci t1i c s;
  (t2i1,s) \<leftarrow> andci a c s;
  (t2i2,s) \<leftarrow> andci b c s;
  (t2,s) \<leftarrow> orci t2i1 t2i2 s;
  eqci t1 t2
} <\<up>>\<^sub>t"
by sep_auto


end