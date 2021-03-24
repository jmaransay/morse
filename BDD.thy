
theory BDD
  imports 
    Bij_betw_simplicial_complex_bool_func
    "ROBDD.BDD_Examples"
begin

section\<open>Relation between boolean functions over vectors and boolfunc as in ROBDD\<close>

definition vec_to_boolfunc :: "(bool^'n => bool) => 'n boolfunc"
  where "vec_to_boolfunc f = (\<lambda>i. f (vec_lambda i))"

lemma "vec_to_boolfunc (\<lambda>x. True) = bf_True"
  unfolding vec_to_boolfunc_def ..

lemma "vec_to_boolfunc (\<lambda>x. False) = bf_False"
  unfolding vec_to_boolfunc_def ..

term sat_list_to_bdt

term eqci


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