
theory BDD
  imports 
    Bij_betw_simplicial_complex_bool_func
    "ROBDD.BDD_Examples"
begin

section\<open>Relation between boolean functions over vectors and boolfunc as in ROBDD\<close>

definition vec_to_boolfunc :: "(bool^'n => bool) => 'n boolfunc"
  where "vec_to_boolfunc f = (\<lambda>i. f (vec_lambda i))"

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

fun val_ifex :: "'a ifex \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "val_ifex Trueif s = True" |
  "val_ifex Falseif s = False" |
  "val_ifex (IF n t1 t2) s = (if s n then val_ifex t1 s else val_ifex t2 s)"

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