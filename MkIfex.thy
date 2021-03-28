
text\<open>
  Author: Julius Michaelis
\<close>

theory MkIfex
  imports "ROBDD.BDT"
begin

fun mk_ifex :: "'a boolfunc \<Rightarrow> 'a list \<Rightarrow> 'a ifex" where
"mk_ifex f [] = (if f undefined then Trueif else Falseif)" |
"mk_ifex f (v#vs) = IF v (mk_ifex (bf_restrict v True f) vs) (mk_ifex (bf_restrict v False f) vs)"

definition "reads_inside_set f x \<equiv> (\<forall>assmt1 assmt2. (\<forall>p. p \<in> x \<longrightarrow> assmt1 p = assmt2 p) \<longrightarrow> f assmt1 = f assmt2)"
definition "reads_finite f \<equiv> \<exists>x. finite x \<and> reads_inside_set f x"

lemma reads_inside_set_subset: "reads_inside_set f a \<Longrightarrow> a \<subseteq> b \<Longrightarrow> reads_inside_set f b"
  unfolding reads_inside_set_def by blast

lemma reads_inside_set_bf_vars: "reads_inside_set f x \<Longrightarrow> bf_vars f \<subseteq> x"
  unfolding bf_vars_def reads_inside_set_def bf_restrict_def
  apply(rule subsetI)
  apply(unfold mem_Collect_eq)
  apply(erule exE)
  apply(metis fun_upd_apply) (* meh *)
done

lemma const_funcs_finite: "reads_finite bf_True" "reads_finite bf_False" unfolding reads_finite_def reads_inside_set_def by blast+
lemma lit_finite: "reads_finite (bf_lit x)" unfolding bf_lit_def reads_finite_def reads_inside_set_def by blast
lemma combine_funcs_finite:
  assumes "reads_finite f1" "reads_finite f2" "reads_finite f3"
  shows "reads_finite ((bf_ite f1 f2 f3) :: 'a boolfunc)"
proof -
  from assms(1)[unfolded reads_finite_def] guess r1 .. note r1 = this
  from assms(2)[unfolded reads_finite_def] guess r2 .. note r2 = this
  from assms(3)[unfolded reads_finite_def] guess r3 .. note r3 = this
  define r where "r \<equiv> r1 \<union> r2 \<union> r3"
  have rf: "finite r" using r1 r2 r3 r_def by simp
  have re: "reads_inside_set f1 r" "reads_inside_set f2 r" "reads_inside_set f3 r"
    using r1 r2 r3 r_def rf by(simp_all add: reads_inside_set_def)
  thus ?thesis unfolding bf_ite_def reads_inside_set_def reads_finite_def by (metis rf)
qed

lemma restrict_reads_finite: "reads_finite (f :: 'a boolfunc) \<Longrightarrow> reads_finite (bf_restrict i v f)"
(* opposite direction does not hold *)
proof -
  assume "reads_finite f" 
  from this[unfolded reads_finite_def] guess a .. note a = this
  hence "reads_inside_set (bf_restrict i v f) a" unfolding reads_inside_set_def bf_restrict_def by simp
  thus "reads_finite (bf_restrict i v f)"  unfolding reads_finite_def using a by fast
qed

lemma reads_inside_set_restrict: "reads_inside_set f s \<Longrightarrow> reads_inside_set (bf_restrict i v f) (Set.remove i s)"
  unfolding reads_inside_set_def bf_restrict_def by force (* wow *)

lemma collect_upd_true: "Collect (x(y:= True)) = insert y (Collect x)" by auto
lemma collect_upd_false: "Collect (x(y:= False)) = Set.remove y (Collect x)" by auto metis
  
lemma "bf_vars (\<lambda>assmt. finite {x. assmt x}) = {}"
  unfolding bf_vars_def Collect_empty_eq bf_restrict_def not_ex not_not collect_upd_true collect_upd_false remove_def
  by simp

lemma vars_restrict: "finite (bf_vars f) \<Longrightarrow> bf_vars (bf_restrict v x f) \<subseteq> Set.remove v (bf_vars f)"
  apply(rule subsetI)
  apply(subst Set.member_remove)
  apply(rule)
  subgoal unfolding bf_vars_def bf_restrict_def mem_Collect_eq by (metis (no_types, lifting) fun_upd_twist fun_upd_upd)
  subgoal unfolding bf_vars_def bf_restrict_def by force
  done

lemma reads_none: "reads_inside_set f {} \<Longrightarrow> f = bf_True \<or> f = bf_False"
  unfolding reads_inside_set_def by fast (* wow *)

lemma 
  val_ifex_mk_ifex_equal:
  "reads_inside_set f (set vs) \<Longrightarrow> val_ifex (mk_ifex f vs) assmt = f assmt"
proof(induction vs arbitrary: f assmt)
  case Nil
  then show ?case using reads_none by auto
next
  case (Cons v vs)
  have "reads_inside_set (bf_restrict v x f) (set vs)" for x
    using reads_inside_set_restrict[OF Cons.prems] reads_inside_set_subset by fastforce
  from Cons.IH[OF this] show ?case 
    unfolding mk_ifex.simps val_ifex.simps bf_restrict_def
    by (simp add: fun_upd_idem)
qed

end