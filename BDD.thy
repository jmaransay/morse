theory BDD
  imports
    Bij_betw_simplicial_complex_bool_func
    ROBDD.Level_Collapse
    ListLexorder
begin

section\<open>Relation between boolean functions over vectors and boolfunc as in ROBDD\<close>

definition vec_to_boolfunc :: "(bool^'n => bool) => 'n boolfunc"
  where "vec_to_boolfunc f = (\<lambda>i. f (vec_lambda i))"

text \<open>Each vertex in a simplicial complex correspons to one True line in the truth table of the inducing boolean function.\<close>
definition bf_from_sc :: "('a :: finite) set set => (bool, 'a) vec \<Rightarrow> bool" where "bf_from_sc K \<equiv> \<lambda>p. {i. p $ i = False} \<in> K"

lemma bf_from_sc: "simplicial_complex K \<Longrightarrow> simplicial_complex_induced_by_monotone_boolean_function (bf_from_sc K) = K"
proof -
  have  "( \<exists>x. {i. x $ i = False} \<in> K \<and> {xa. x $ xa = False} = y) = (y \<in> K)" for y
  by simp (metis Collect_neg_eq UNIV_I double_compl uminus_set_def vec_lambda_inverse)
  thus ?thesis
  unfolding bf_from_sc_def simplicial_complex_induced_by_monotone_boolean_function_def
  unfolding ceros_of_boolean_input_def
  by simp
qed

definition boolfunc_from_sc :: "('a :: finite) set set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where "boolfunc_from_sc K \<equiv> \<lambda>p. {i. \<not> p i} \<in> K"

definition "sc_threshold_2_3 \<equiv> {{},{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0,a\<^sub>1},{a\<^sub>0,a\<^sub>2},{a\<^sub>0,a\<^sub>3},{a\<^sub>1,a\<^sub>2},{a\<^sub>1,a\<^sub>3},{a\<^sub>2,a\<^sub>3}}"
lemma "bf_from_sc sc_threshold_2_3 = bool_fun_threshold_2_3"
  unfolding sc_threshold_2_3_def oops (* nyeah, not gonna repeat that one *)

lemma hlp1: "{i. \<not> (f(a\<^sub>0 := a0, a\<^sub>1 := a1, a\<^sub>2 := a2, a\<^sub>3 := a3)) i} =
  (if a0 then {} else {a\<^sub>0})
\<union> (if a1 then {} else {a\<^sub>1})
\<union> (if a2 then {} else {a\<^sub>2})
\<union> (if a3 then {} else {a\<^sub>3})
"
  by(simp; insert finite_mod_4.exhaust; blast)

lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=False, a\<^sub>2:=False, a\<^sub>3:=False)) = False" unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=False, a\<^sub>2:=False, a\<^sub>3:=True )) = False" unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=False, a\<^sub>2:=True , a\<^sub>3:=False)) = False" unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=False, a\<^sub>2:=True , a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=True , a\<^sub>2:=False, a\<^sub>3:=False)) = False" unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=True , a\<^sub>2:=False, a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=True , a\<^sub>2:=True , a\<^sub>3:=False)) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=False, a\<^sub>1:=True , a\<^sub>2:=True , a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=False, a\<^sub>2:=False, a\<^sub>3:=False)) = False" unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=False, a\<^sub>2:=False, a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=False, a\<^sub>2:=True , a\<^sub>3:=False)) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=False, a\<^sub>2:=True , a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=True , a\<^sub>2:=False, a\<^sub>3:=False)) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=True , a\<^sub>2:=False, a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=True , a\<^sub>2:=True , a\<^sub>3:=False)) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto
lemma "boolfunc_from_sc sc_threshold_2_3 (a(a\<^sub>0:=True , a\<^sub>1:=True , a\<^sub>2:=True , a\<^sub>3:=True )) = True " unfolding hlp1 boolfunc_from_sc_def sc_threshold_2_3_def by auto

lemma "boolfunc_from_sc UNIV = bf_True"
  unfolding boolfunc_from_sc_def by simp

text\<open>This may seem like an extra step, but effectively, it means: require that all the atoms outside the vertex are true, but don't care about what's in the vertex.\<close>
lemma boolfunc_from_sc_lazy: "simplicial_complex K \<Longrightarrow> boolfunc_from_sc K = (\<lambda>p. Pow {i. \<not> p i} \<subseteq> K)"
  unfolding simplicial_complex_def boolfunc_from_sc_def
  by auto (* wow *)

primrec boolfunc_from_vertex_list :: "'a list \<Rightarrow> ('a :: finite) list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"boolfunc_from_vertex_list n [] = bf_True" |
"boolfunc_from_vertex_list n (f#fs) =  bf_and (boolfunc_from_vertex_list n fs) (if f \<in> set n then bf_True else bf_lit f)"

lemma boolfunc_from_vertex_list_Cons: "boolfunc_from_vertex_list (a # as) lUNIV = (\<lambda>v. (boolfunc_from_vertex_list as lUNIV) (v(a:=True)))"
  by(induction lUNIV; simp add: bf_ite_def bf_lit_def)

lemma boolfunc_from_vertex_list_Empty: "boolfunc_from_vertex_list [] lUNIV = Ball (set lUNIV)"
  by(induction lUNIV) (auto simp add: bf_ite_def bf_lit_def)

lemma "set lUNIV = UNIV \<Longrightarrow> boolfunc_from_vertex_list a lUNIV = (\<lambda>p. {i. \<not> p i} \<subseteq> set a)"
  apply(induction "card (set lUNIV - set a)" arbitrary: a lUNIV)
  oops
  (* There is probably some neat way of proving this through an opposite-direction induction, but I'm not able to find an induction rule for it *)
(* so I just prove it through straightforward induction and some helper lemmas *)
lemma boolfunc_from_vertex_list: "set lUNIV = UNIV \<Longrightarrow> boolfunc_from_vertex_list a lUNIV = (\<lambda>p. {i. \<not> p i} \<subseteq> set a)"
  by(induction a; fastforce simp add: boolfunc_from_vertex_list_Empty boolfunc_from_vertex_list_Cons)

primrec boolfunc_from_sc_list :: "'a list \<Rightarrow> ('a :: finite) list list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"boolfunc_from_sc_list lUNIV [] = bf_False" |
"boolfunc_from_sc_list lUNIV (l#L) = bf_or (boolfunc_from_sc_list lUNIV L) (boolfunc_from_vertex_list l lUNIV)"

lemma boolfunc_from_sc_un: "boolfunc_from_sc (a\<union>b) = bf_or (boolfunc_from_sc a) (boolfunc_from_sc b)"
  unfolding boolfunc_from_sc_def unfolding bf_or_def bf_ite_def by force

lemma bf_ite_const[simp]: "bf_ite bf_True a b = a" "bf_ite bf_False a b = b"
  by(simp_all add: bf_ite_def)

lemma simlicial_complex_Pow[simp,intro!]: "simplicial_complex (Pow s)"
  by(auto simp add: simplicial_complex_def)

lemma Pow_subset_Pow: "Pow a \<subseteq> Pow b = (a \<subseteq> b)"
  by blast

lemma boolfunc_from_sc_list_concat: "boolfunc_from_sc_list lUNIV (a @ b) = bf_or (boolfunc_from_sc_list lUNIV a) (boolfunc_from_sc_list lUNIV b)"
  by(induction a; auto simp add: bf_ite_def)

lemma boolfunc_from_sc_list_existing_useless: "a \<in> set as \<Longrightarrow> boolfunc_from_sc_list l (a # as) = boolfunc_from_sc_list l as"
proof(induction as)
  case (Cons a1s as) then show ?case by(cases "a1s = a"; simp add: bf_ite_def) metis
qed simp

primrec remove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"remove a [] = []" |
"remove a (a1 # as) = (if a = a1 then [] else [a1]) @ remove a as"

lemma set_remove[simp]: "set (remove a as) = set as - {a}"
  by(induction as; auto)
lemma remove_concat[simp]: "remove a (a1 @ a2) = remove a a1 @ remove a a2"
  by(induction a1; simp)

lemma boolfunc_from_sc_list_dedup1: "boolfunc_from_sc_list l (a # as) = boolfunc_from_sc_list l (a # remove a as)"
proof(induction as)
  case (Cons a1s as) then show ?case by(cases "a1s = a"; simp add: bf_ite_def) metis
qed simp

lemma boolfunc_from_sc_list_reorder: "set a = set b \<Longrightarrow> boolfunc_from_sc_list l a = boolfunc_from_sc_list l b"
proof(induction a arbitrary: b)
next
  case (Cons a1 a2)
  then obtain b1 b2 where  b: "b = b1 @ a1 # b2" by (metis list.set_intros(1) split_list)
  have cons_concat: "\<And>a as. a # as = [a] @ as" by simp
  have bb: "boolfunc_from_sc_list l b = bf_or (boolfunc_from_vertex_list a1 l) (bf_or (boolfunc_from_sc_list l b1) (boolfunc_from_sc_list l b2))"
    apply(subst b)
    apply(subst boolfunc_from_sc_list_concat)
    apply(subst cons_concat)
    apply(subst boolfunc_from_sc_list_concat)
    apply(auto simp add: bf_ite_def)
    done
  have bbb: "boolfunc_from_sc_list l b = boolfunc_from_sc_list l (a1 # (remove a1 (b1 @ b2)))"
    unfolding bb boolfunc_from_sc_list_dedup1[symmetric]
    by (auto simp add: boolfunc_from_sc_list_concat bf_ite_def)
  show ?case proof(cases "a1 \<in> set a2")
    case True
    then show ?thesis using Cons by (metis insert_absorb list.set(2))
  next
    case False
    then have a2: "set a2 = set (remove a1 (b1 @ b2))"
      using Cons.prems b by fastforce
    show ?thesis using  Cons.IH[OF a2] bbb by simp
  qed
qed simp

lemma boolfunc_from_sc_list: "set lUNIV = (UNIV :: ('a :: finite) set) \<Longrightarrow> simplicial_complex (set ` set L) \<Longrightarrow> boolfunc_from_sc_list lUNIV L = boolfunc_from_sc (set ` set L)"
proof -
  assume lUNIV: "set lUNIV = UNIV"
  assume sc: "simplicial_complex (set ` set L)"
  define sorted where "sorted \<equiv> sorted_wrt (\<lambda>a b :: 'a list. card (set b) \<le> card (set a))"
  (* wlog, assume L is sorted. the price for that was paid in boolfunc_from_sc_list_reorder *)
  have i: "sorted L \<Longrightarrow> simplicial_complex (set ` set L) \<Longrightarrow> boolfunc_from_sc_list lUNIV L = boolfunc_from_sc (set ` set L)" for L
  proof(induction L)
    case Nil
    show ?case by(simp add: boolfunc_from_sc_def)
  next
    case (Cons a L)
    from Cons.prems(2) have p: "Pow (set a) \<subseteq> (set ` set (a # L))" unfolding simplicial_complex_def by simp
    hence pun: "insert (set a) (set ` set L) = Pow (set a) \<union> (set ` set  L)" by auto
    have bfSing: "boolfunc_from_sc_list lUNIV [a] = boolfunc_from_sc (Pow (set a))"
      by(simp add: boolfunc_from_sc_lazy Pow_subset_Pow boolfunc_from_vertex_list[OF lUNIV])
    have bflCons: "boolfunc_from_sc_list lUNIV (a # L) = bf_or (boolfunc_from_sc_list lUNIV [a]) (boolfunc_from_sc_list lUNIV L)"
      by(simp add: bf_ite_def) blast
    from Cons.prems have "simplicial_complex (set ` set L)"
      unfolding simplicial_complex_def sorted_def  by simp (metis List.finite_set PowD card_seteq insert_image subset_insert)
    from Cons.IH[OF _ this] Cons.prems(1) have "boolfunc_from_sc_list lUNIV L = boolfunc_from_sc (set ` set L)" unfolding sorted_def by simp
    thus ?case
      apply(subst bflCons)
      apply(simp del: boolfunc_from_sc_list.simps)
      apply(subst pun)
      apply(subst boolfunc_from_sc_un)
      apply(subst bfSing)
      apply(simp)
      done
  qed
  define sort where "sort \<equiv> rev (sort_key (\<lambda>l. card (set l)) L)"
  have sc: "simplicial_complex (set ` set sort)" unfolding sort_def using sc by simp
  have sorted: "sorted sort"
    by(simp add: sorted_def sort_def sorted_wrt_rev) (metis sorted_map sorted_sort_key)
  have set: "set sort = set L" unfolding sort_def by simp
  from boolfunc_from_sc_list_reorder[OF set] i[OF sorted sc] set show ?thesis by presburger
qed

lemma boolfunc_from_sc_alt: "boolfunc_from_sc K = vec_to_boolfunc (bf_from_sc K)"
  unfolding boolfunc_from_sc_def vec_to_boolfunc_def bf_from_sc_def
  by simp

text\<open>Another stone in the way: BDD assumes that the atoms are nats. So you'll need a function to map between @{typ "'a :: finite"} and @{typ "nat"}\<close>

primrec bdd_from_vertex_list :: "nat list \<Rightarrow> nat list \<Rightarrow> bddi \<Rightarrow> (nat \<times> bddi) Heap" where
"bdd_from_vertex_list n [] s = tci s" |
"bdd_from_vertex_list n (f#fs) s = do {
  (f, s) \<leftarrow> if f \<in> set n then tci s else litci f s;
  (fs, s) \<leftarrow> bdd_from_vertex_list n fs s;
  andci fs f s
}"
(* You'd guess that andci is commutative, and thus the argument order doesn't matter.
   You'd be wrong. The automation very much doesn't know about that. *)

primrec bdd_from_sc_list :: "nat list \<Rightarrow> nat list list \<Rightarrow> bddi \<Rightarrow> (nat \<times> bddi) Heap" where
"bdd_from_sc_list lUNIV [] s = fci s" |
"bdd_from_sc_list lUNIV (l#L) s = do {
  (l, s) \<leftarrow> bdd_from_vertex_list l lUNIV s;
  (L, s) \<leftarrow> bdd_from_sc_list lUNIV L s;
  orci L l s
}"

primrec nat_from_finite4 :: "finite_mod_4 \<Rightarrow> nat" where
"nat_from_finite4 a\<^sub>0 = 0" |
"nat_from_finite4 a\<^sub>1 = 1" |
"nat_from_finite4 a\<^sub>2 = 2" |
"nat_from_finite4 a\<^sub>3 = 3"

lemma inj_nat_from_finite4: "inj nat_from_finite4"
  apply(rule injI)
  subgoal for x y
    apply(cases x; cases y)
                   apply simp_all
    done
  done

definition "nat_list_from_vertex (f :: ('a :: finite) \<Rightarrow> nat) v \<equiv> sorted_list_of_set (f ` v)"
definition "nat_list_from_sc (f :: ('a :: finite) \<Rightarrow> nat) K \<equiv> sorted_list_of_list_set (nat_list_from_vertex f ` K)"
lemma nat_list_from_sc: "set ` set (nat_list_from_sc f (L :: ('a :: finite) set set)) = {{f i|i . i \<in> l} | l. l \<in>  L}"
  by (auto simp add: nat_list_from_sc_def nat_list_from_vertex_def image_image)

definition "ex_2_3 \<equiv> do {
  s \<leftarrow> emptyci;
  (ex, s) \<leftarrow> bdd_from_sc_list [0, 1, 2, 3] (nat_list_from_sc nat_from_finite4 sc_threshold_2_3) s;
  graphifyci ''2_3'' ex s
}"
(* hommm. seeing is believing. how to execute? *)

definition nat_boolfunc :: "('a \<Rightarrow> nat) \<Rightarrow> 'a boolfunc \<Rightarrow> nat boolfunc" where
"nat_boolfunc m f \<equiv> (\<lambda>v. f (\<lambda>a. v (m a)))"
lemma "nat_boolfunc id f = f" by(simp add: nat_boolfunc_def)
lemma nat_boolfunc_ite: "nat_boolfunc m (bf_ite i t e) = bf_ite (nat_boolfunc m i) (nat_boolfunc m t) (nat_boolfunc m e)"
  by(simp add: nat_boolfunc_def)
lemma nat_boolfunc_consts[simp]: "nat_boolfunc m bf_True = bf_True" "nat_boolfunc m bf_False = bf_False"
  unfolding nat_boolfunc_def by argo+
lemma nat_boolfunc_misc:
  "nat_boolfunc m (bf_and a b) = bf_and (nat_boolfunc m a) (nat_boolfunc m b)"
  "nat_boolfunc m (bf_or a b) = bf_or (nat_boolfunc m a) (nat_boolfunc m b)"
  by(simp_all only: nat_boolfunc_ite bf_or_def bf_and_def nat_boolfunc_consts) (* guess my simp setup is bad... *)
lemma nat_boolfunc_lit: "nat_boolfunc m (bf_lit i) = bf_lit (m i)" unfolding nat_boolfunc_def bf_lit_def ..

lemma bf_ite_direct[simp]: "bf_ite i bf_True bf_False = i" by simp


lemma andciI: "node_relator (tb, tc) rp \<Longrightarrow> node_relator (eb, ec) rp \<Longrightarrow> rq \<subseteq> rp \<Longrightarrow>
      <bdd_relator rp s> andci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_and tb eb,r) rq) s'>"
  by sep_auto

lemma bdd_from_vertex_list[sep_heap_rules]:
  assumes "inj m"
  shows "<bdd_relator rp s>
    bdd_from_vertex_list (map m n) (map m l) s
  <\<lambda>(r,s'). bdd_relator (insert (nat_boolfunc m (boolfunc_from_vertex_list n l), r) rp) s'>"
proof(induction l arbitrary: rp s)
  case Nil then show ?case by(sep_auto simp add: nat_boolfunc_def)
next
  case (Cons a l)
  show ?case proof(cases "m a \<in> set (map m n)")
    case True
    with assms have ti: "a \<in> set n" by (metis image_set inj_image_mem_iff)
    show ?thesis
      apply(simp only: bdd_from_vertex_list.simps list.map boolfunc_from_vertex_list.simps ti True if_True)
      apply(sep_auto simp only:)
       apply(rule Cons.IH)
      apply(clarsimp simp del: bf_ite_def)
      apply(sep_auto)
      done
  next
    case False
    hence ti: "a \<notin> set n" by auto
    show ?thesis
      apply(simp only: bdd_from_vertex_list.simps list.map boolfunc_from_vertex_list.simps ti False if_False)
      apply(sep_auto simp only:)
       apply(rule Cons.IH)
      apply(sep_auto simp del: bf_ite_def bf_and_def simp add: nat_boolfunc_lit nat_boolfunc_misc)
    done
  qed
qed

lemma boolfunc_bdd_from_sc_list:
  assumes "inj m"
  shows "<bdd_relator rp s>
    bdd_from_sc_list (map m lUNIV) (map (map m) K) s
  <\<lambda>(r,s'). bdd_relator (insert (nat_boolfunc m (boolfunc_from_sc_list lUNIV K), r) rp) s'>"
proof(induction K arbitrary: rp s)
  case Nil
  then show ?case by sep_auto
next
  case (Cons a K)
  show ?case by(sep_auto heap add: Cons.IH intro: assms simp del: bf_ite_def bf_or_def simp add: nat_boolfunc_misc)
qed


lemma map_map_idI: "(\<And>x. x \<in> \<Union>(set ` set l) \<Longrightarrow> f x = x) \<Longrightarrow> map (map f) l = l"
  by(induct l; simp; meson map_idI)

definition "bdd_from_sc m K \<equiv> bdd_from_sc_list (nat_list_from_vertex m UNIV) (nat_list_from_sc m K)"

theorem bdd_from_sc:
  assumes "inj m"
  assumes "simplicial_complex (K :: ('a :: finite) set set)"
  shows "<bdd_relator rp s>
    bdd_from_sc m K s
  <\<lambda>(r,s'). bdd_relator (insert (nat_boolfunc m (vec_to_boolfunc (bf_from_sc K)), r) rp) s'>"
proof -
  obtain lUNIV :: "('a :: finite) list" where lUNIV: "set lUNIV = UNIV" by (meson finite finite_list)
  define lUNIV where "lUNIV = map (the_inv m) (nat_list_from_vertex m UNIV)"
  have lUNIV_set: "set lUNIV = UNIV"
    unfolding lUNIV_def nat_list_from_vertex_def
    by(simp add: assms(1))
  have lUNIV_map: "map m lUNIV = (nat_list_from_vertex m UNIV)"
    unfolding lUNIV_def nat_list_from_vertex_def
    apply (simp add: comp_def)
    apply (rule map_idI)
    apply (subst f_the_inv_into_f[OF assms(1)]; fastforce)
    done
  define Klist where "Klist \<equiv> map (map (the_inv m)) (nat_list_from_sc m K)"
  thm f_the_inv_into_f[where A = UNIV, OF assms(1)] the_inv_f_f[OF assms(1)]
  have Klist_set: "set ` set Klist = K"
    unfolding Klist_def nat_list_from_sc_def nat_list_from_vertex_def
    by(simp add: image_comp the_inv_f_f[OF assms(1)])
  have Klist_map: "map (map m) Klist = nat_list_from_sc m K"
    unfolding Klist_def nat_list_from_sc_def nat_list_from_vertex_def
    apply (simp add: comp_def)
    apply (rule map_map_idI)
    apply (subst f_the_inv_into_f[OF assms(1)]; fastforce)
    done
  have sc_Klist: "simplicial_complex (set ` set Klist)"
    using Klist_set assms(2) by fastforce
  show ?thesis
    by (insert boolfunc_bdd_from_sc_list[OF assms(1), of rp s lUNIV Klist])
        (simp only: Klist_set Klist_map lUNIV_map boolfunc_from_sc_alt boolfunc_from_sc_list[OF lUNIV_set sc_Klist] bdd_from_sc_def)
qed

export_code bdd_from_sc (* I guess this means its actually executable? *)

end
