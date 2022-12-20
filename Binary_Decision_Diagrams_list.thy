
theory Binary_Decision_Diagrams_list
  imports
    Main
    "Boolean_Expression_Checkers.Boolean_Expression_Checkers"
    "Boolean_Expression_Checkers.Boolean_Expression_Checkers_AList_Mapping"
begin

text\<open>Beware that following @{term val_ifex} definition the left branch 
corresponds to @{term True} and the left branch to @{term False}\<close>

fun depth :: "'a ifex \<Rightarrow> nat"
  where
    "depth Trueif = 0" | "depth Falseif = 0" |
    "depth (IF b t f) = 1 + max (depth t) (depth f)"

fun Alexander_dual :: "'a ifex \<Rightarrow> 'a ifex"
  where "Alexander_dual Trueif = Falseif" |
    "Alexander_dual Falseif = Trueif" |
    "Alexander_dual (IF b t f) = (IF b (Alexander_dual f) (Alexander_dual t))"

lift_definition neg_env :: "'a env_bool \<Rightarrow> 'a env_bool"
  is "\<lambda>m k. case m k of None \<Rightarrow> None | Some v \<Rightarrow> Some (\<not> v)" .

lemma "val_ifex (Alexander_dual t) env = (\<not> val_ifex (t) (\<lambda>x. \<not> env x))"
  by (induct t) auto

lemma "depth (Alexander_dual t) = depth t"
  by (induct t) auto

lemma "Alexander_dual (Alexander_dual t) = t"
  by (induct t) auto

value "Alexander_dual (IF (1::int) Trueif Falseif)"

value "Alexander_dual (IF (1::int) (IF 2 (Trueif) (Falseif))
                         (IF 3 (Trueif) (Falseif)))"

value "Alexander_dual (IF (1::int) (IF 2 ((IF 3 (Falseif) (Trueif))) (Falseif))
                         (IF 3 (Trueif) (Falseif)))"

text\<open>Beware that the depth of a reduced BDT is not always smaller than the 
  one of the original BDT (it may depend on the chosen environment).\<close>

value "depth (IF finite_4.a\<^sub>1 (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) (IF finite_4.a\<^sub>4 Falseif Trueif)) Trueif)"

value "depth (IF finite_4.a\<^sub>1 
                (IF finite_4.a\<^sub>1 
                  (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) 
                                  (IF finite_4.a\<^sub>4 Falseif Trueif)) 
                  Trueif)
                Trueif)"

value "depth (reduce_alist  [(finite_4.a\<^sub>1, True)]
    (IF finite_4.a\<^sub>1 (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) (IF finite_4.a\<^sub>4 Falseif Trueif)) 
                      Trueif))"

value "depth (reduce_alist [(finite_4.a\<^sub>1, True)] (IF finite_4.a\<^sub>1
                (IF finite_4.a\<^sub>1 
                  (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) 
                                  (IF finite_4.a\<^sub>4 Falseif Trueif)) 
                  Trueif)
                Trueif))"

value "depth (reduce_alist  [] (IF finite_4.a\<^sub>1
                (IF finite_4.a\<^sub>1
                  (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) 
                                  (IF finite_4.a\<^sub>4 Falseif Trueif)) 
                  Trueif)
                Trueif))"


value "depth (reduce_alist  [(finite_4.a\<^sub>1, False)] 
    (IF finite_4.a\<^sub>1 (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) (IF finite_4.a\<^sub>4 Falseif Trueif)) 
                      Trueif))"

lemma depth_mkIF: "depth (mkIF x t1 t2) \<le> Suc (max (depth t1) (depth t2))"
  unfolding mkIF_def by auto

fun vars :: "'a ifex \<Rightarrow> 'a set"
  where "vars (IF x t f) = insert x (vars t \<union> vars f)" |
        "vars _ = {}"

lemma vars_IFT_subset: "vars t \<subseteq> vars (IF x t f)" by auto
lemma vars_IFF_subset: "vars f \<subseteq> vars (IF x t f)" by auto

lemma vars_mkIF: "vars (mkIF x t f) \<subseteq> vars (IF x t f)" 
  by (metis dual_order.eq_iff mkIF_def vars_IFT_subset)

lemma
  shows "vars (reduce env b) \<subseteq> vars b"
proof (induction b arbitrary: env)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b1 b2)
  show ?case
  proof (cases "Mapping.lookup env x1 = None")
    case True
    have vt: "vars (reduce (Mapping.update x1 True env) b1) \<subseteq> vars b1"
        and vf: "vars (reduce (Mapping.update x1 False env) b2) \<subseteq> vars b2"
      using IF.IH by simp_all
    with vars_mkIF show ?thesis unfolding reduce.simps using True by fastforce
  next
    case False
    have vt: "vars (reduce env b1) \<subseteq> vars b1"
        and vf: "vars (reduce env b2) \<subseteq> vars b2" using IF.IH by simp_all
    thus ?thesis unfolding reduce.simps using False
      by auto (metis (mono_tags, lifting) subset_eq)
  qed
qed

fun ifex_no_twice where 
  "ifex_no_twice (IF v t e) = (
  v \<notin> (vars t \<union> vars e) \<and> ifex_no_twice t \<and> ifex_no_twice e)" |
 "ifex_no_twice _ = True"

lemma
  env_not_in_vars:
  assumes m: "Mapping.lookup env x = Some b"
  shows "x \<notin> vars (reduce env bdd)"
  using m proof (induction bdd arbitrary: env b)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 bdd1 bdd2 _ b)
  show ?case
  proof (cases "x = x1")
    case True
    have rw: "reduce env (IF x1 bdd1 bdd2) = reduce env (if b then bdd1 else bdd2)"
      using IF.prems True unfolding reduce.simps by auto
    show ?thesis unfolding rw using IF.IH [OF IF.prems] by (cases b, auto)
  next
    case False
    have "x \<notin> vars (reduce (Mapping.update x1 True env) bdd1)"
      and "x \<notin> vars (reduce (Mapping.update x1 False env) bdd2)"
      using False IF.IH(1,2) IF.prems by auto
    moreover have "x \<notin> vars (reduce env bdd1)"
      and "x \<notin> vars (reduce env bdd2)"
      using False IF.IH(1,2) IF.prems by auto
    ultimately show ?thesis unfolding reduce.simps
      apply (cases "Mapping.lookup env x1 = None") 
      using False unfolding mkIF_def by (simp_all) force
  qed
qed

lemma "x \<notin> vars (reduce (Mapping.update x b env) bdd)"
  using env_not_in_vars by force

lemma "ifex_no_twice (reduce env b)"
proof (induction b arbitrary: env)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b1 b2)
  show ?case
  proof (cases "Mapping.lookup env x1 = None")
    case True
    have vt: "ifex_no_twice (reduce (Mapping.update x1 True env) b1)"
        and vf: "ifex_no_twice (reduce (Mapping.update x1 False env) b2)"
      using IF.IH by simp_all
    show ?thesis unfolding reduce.simps using True
      by auto (simp add: env_not_in_vars mkIF_def vf vt)
  next
    case False
    have vt: "ifex_no_twice (reduce env b1)"
        and vf: "ifex_no_twice (reduce env b2)"
      using IF.IH by simp_all
    show ?thesis unfolding reduce.simps using False
      using vf vt by force
  qed
qed

lemma
  depth_reduce_le:
  assumes ib: "ifex_no_twice b" 
    and k: "vars b \<inter> Mapping.keys env = {}"
  shows "depth (reduce env b) \<le> depth b"
using ib k proof (induction b arbitrary: env)
  case Trueif show ?case by simp
next
  case Falseif show ?case by simp
next
  case (IF x t f)
  from IF.prems 
  have int: "ifex_no_twice t" and inf: "ifex_no_twice f"
    and xt: "x \<notin> vars t" and xf: "x \<notin> vars f"
    and vt: "vars t \<inter> Mapping.keys (Mapping.update x True env) = {}"
    and vf: "vars f \<inter> Mapping.keys (Mapping.update x False env) = {}"
    by auto
  have drdt: "depth (reduce (Mapping.update x True env) t) \<le> depth t"
    and drdf: "depth (reduce (Mapping.update x False env) f) \<le> depth f"
     by (rule IF.IH, intro int, intro vt)
          (rule IF.IH, intro inf, intro vf)
  have mlxnone: "Mapping.lookup env x = None"
     using IF.prems (2)
     by (metis disjoint_iff_not_equal domIff insertCI keys_dom_lookup vars.simps(1))
  have "depth (reduce env (IF x t f)) =
          depth (mkIF x (reduce (Mapping.update x True env) t)
      (reduce (Mapping.update x False env) f))"
        (is "_ = depth (mkIF x ?xt ?xf)")
      using mlxnone reduce.simps (1) [of env x t f] by simp
  also have "... \<le> Suc (max (depth ?xt) (depth ?xf))"
      using depth_mkIF by metis
  also have "... \<le> Suc (max (depth t) (depth f))"
      using drdt drdf by auto
  also have "... = depth (IF x t f)" by simp
  finally show ?case .
qed

text\<open>Do notice that we treat similarly the case where 
  we compute the path of a constant that the case where we 
  compute the path with respect to an environment that does not
  include some of the variables in the @{typ "'a ifex"} expression.
  We will hav eto include premises in our lemmas to discard the 
  latter case.\<close>

fun path :: "'a env_bool \<Rightarrow> 'a ifex \<Rightarrow> 'a list"
  where "path _ Trueif = []" |
  "path _ Falseif = []" |
  "path eval (IF x t f) = (case Mapping.lookup eval x of 
      None \<Rightarrow> [] |
      Some True \<Rightarrow> x # (path eval t) |
      Some False \<Rightarrow> x # (path eval f))"

value "path Mapping.empty (IF x Trueif Falseif)"

lemma "path (Mapping.update x False env) (IF x (IF y Trueif Falseif) Falseif) 
  = [x]"
  by simp

lemma "path (Mapping.of_alist [(x, True), (y, True)]) 
                  (IF x (IF y Trueif Falseif) Falseif) 
  = [x, y]"
  by auto (simp add: lookup_of_alist)

value "length (path (Mapping.of_alist [(finite_4.a\<^sub>1, True)]) 
            (IF finite_4.a\<^sub>1 Falseif Falseif))"

value "length (path (Mapping.of_alist [(finite_4.a\<^sub>3, False)])
            (IF finite_4.a\<^sub>3 (IF finite_4.a\<^sub>1 Falseif Falseif) (Falseif)))"

(*lemma
  path_exists:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  shows "path eval bdd \<noteq> None"
  using v proof (induction bdd)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b11 b12)
  from IF.prems
  have vb11: "vars b11 \<subseteq> Mapping.keys eval" and vb12: "vars b12 \<subseteq> Mapping.keys eval"
    and x1: "x1 \<in> Mapping.keys eval"
    by simp_all
  obtain l11 l12 x11 
    where "path eval b11 = Some l11" and "path eval b12 = Some l12"
      and "Mapping.lookup eval x1 = Some x11"
    using IF.IH (1) [OF vb11] IF.IH (2) [OF vb12] x1
    by auto (meson in_keysD)
  then show ?case unfolding path.simps
    by (simp add: case_bool_if)
qed

lemma
  path_reduce_exists:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  shows "path eval (reduce env bdd) \<noteq> None"
  using v path_exists [OF v] proof (induction bdd arbitrary: env)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b1 b2)
  show ?case
  proof (cases "Mapping.lookup env x1 = None")
    case False 
    then obtain x11 where mx1: "Mapping.lookup env x1 = Some (x11)" by auto
    from IF.prems (1)
    have vb1: "vars b1 \<subseteq> Mapping.keys eval" and vb2: "vars b2 \<subseteq> Mapping.keys eval"
      by simp_all
    obtain l11 l12
      where perb1: "path eval (reduce env b1) = Some l11" 
        and perb2: "path eval (reduce env b2) = Some l12"
      using IF.IH (1) [OF vb1 path_exists [OF vb1]] 
        IF.IH (2) [OF vb2 path_exists [OF vb2]] (*x1*)
      by auto (meson in_keysD)
    thus ?thesis unfolding reduce.simps using mx1 by auto
  next
    case True
    from IF.prems (1)
    have vb1: "vars b1 \<subseteq> Mapping.keys eval" and vb2: "vars b2 \<subseteq> Mapping.keys eval"
      and x1: "x1 \<in> Mapping.keys eval"
      by simp_all
    obtain l11 l12 x11
      where perb1: "path eval (reduce (Mapping.update x1 True env) b1) = Some l11" 
        and perb2: "path eval (reduce (Mapping.update x1 True env) b2) = Some l12"
        and mx1: "Mapping.lookup eval x1 = Some x11"
      using IF.IH (1) [OF vb1 path_exists [OF vb1]] 
        IF.IH (2) [OF vb2 path_exists [OF vb2]] x1
      by auto (meson in_keysD)
    thus ?thesis
      using True perb1 perb2 unfolding reduce.simps mkIF_def 
      apply auto
      apply (cases x11)
      by (simp add: IF.IH(2) option.case_eq_if path_exists vb2)+
  qed
qed

corollary
  path_some:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  obtains l
  where "path eval bdd = Some l"
  using path_exists [OF v] by auto

corollary
  path_reduce_some:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  obtains l
  where "path eval (reduce env bdd) = Some l"
  using path_reduce_exists [OF v] by auto

corollary
  olength_some:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  obtains i
  where "olength (path eval bdd) = Some i"
  using path_some [OF v] unfolding olength_def
  by (metis option.simps(5))

corollary
  olength_reduce_some:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  obtains i
  where "olength (path eval (reduce env bdd)) = Some i"
  using path_reduce_some [OF v] unfolding olength_def
  by (metis option.simps(5))
*)
(*lemma assumes pm: "path eval
       (mkIF x1 (reduce env1 b1) (reduce env2 b2)) = Some l"
      and p: "path eval (IF x1 b1 b2) = Some m"
    shows "set l \<subseteq> set m" and "length l \<le> length m"
proof (cases "(reduce (Mapping.update x1 True env1) b1) =
         (reduce (Mapping.update x1 False env1) b2)")
  case True
  hence "mkIF x1 (reduce (Mapping.update x1 True env1) b1)
         (reduce (Mapping.update x1 False env2) b2) = 
         reduce (Mapping.update x1 True env1) b1"
    unfolding mkIF_def by simp*)

text\<open>Beware that if we omit the first premise of the following result
  then it does not hold:
  Nitpick found a counterexample for card 'a = 6:
  Free variables:
    @{term "b = IF a\<^sub>1 (IF a\<^sub>2 (IF a\<^sub>3 Falseif Trueif) Falseif) Trueif"},
    @{term "env = [a\<^sub>1 \<mapsto> True, a\<^sub>6 \<mapsto> False]"},
    @{term "eval =
      [a\<^sub>1 \<mapsto> False, a\<^sub>2 \<mapsto> True, a\<^sub>3 \<mapsto> False, a\<^sub>4 \<mapsto> False, a\<^sub>5 \<mapsto> False, a\<^sub>6 
        \<mapsto> False]"},
    @{term "i = 2"},
    @{term "j = 1"}.
\<close>

theorem
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
    and c: "\<forall>x\<in>Mapping.keys eval.
          (Mapping.lookup env x = Mapping.lookup eval x \<or> Mapping.lookup env x = None)"
  shows "length (path eval (reduce env bdd)) \<le> length (path eval bdd)"
  using c v proof (induction bdd arbitrary: eval env)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b1 b2)
  from IF.prems (2)
  have vb1: "vars b1 \<subseteq> Mapping.keys eval" and vb2: "vars b2 \<subseteq> Mapping.keys eval"
    and x1: "x1 \<in> Mapping.keys eval"
    by simp_all
  obtain x11 :: bool where x1some: "Mapping.lookup eval x1 = Some x11"
    using x1 by (meson in_keysD)
  have i1j1: "length (path eval (reduce env b1)) \<le> length (path eval b1)" 
    using IF.IH (1) [OF IF.prems (1) vb1] .
  have i2j2: "length (path eval (reduce env b2)) \<le> length (path eval b2)" 
    using IF.IH (2) [OF IF.prems (1) vb2] .
  show ?case
  proof (cases "Mapping.lookup env x1 = None")
    case True note x1none = True
    have r: "reduce env (IF x1 b1 b2) =
      mkIF x1 (reduce (Mapping.update x1 True env) b1)  
              (reduce (Mapping.update x1 False env) b2)"
      unfolding reduce.simps using True by simp
    show ?thesis
    proof (cases "reduce (Mapping.update x1 True env) b1 =
           reduce (Mapping.update x1 False env) b2")
      case False note neq = False
      hence mk: "mkIF x1 (reduce (Mapping.update x1 True env) b1)  
              (reduce (Mapping.update x1 False env) b2) = 
        IF x1 (reduce (Mapping.update x1 True env) b1)  
              (reduce (Mapping.update x1 False env) b2)" 
        unfolding mkIF_def by simp
    show ?thesis
    proof (cases "x11")
      case True
      show ?thesis
        using IF.IH (1) [OF _ vb1]
        unfolding reduce.simps 
        using x1none x1some True neq
        using IF.prems
        unfolding mkIF_def 
        by auto (simp add: lookup_update_unfold)
    next
    case False
    show ?thesis 
      using IF.IH (2) [OF _ vb2]
      unfolding reduce.simps
      using x1none x1some False neq IF.prems
      unfolding mkIF_def
      by auto (simp add: lookup_update_unfold)
    qed
  next
    case True note b1b2eq = True
    have rb1: "reduce env (IF x1 b1 b2) = reduce (Mapping.update x1 True env) b1"
      unfolding r unfolding mkIF_def using True
      unfolding reduce.simps using x1some by auto
    show ?thesis
    proof (cases "x11")
      case True
      show ?thesis 
        using IF.prems (1,2)
        using IF.IH (1) [OF _ vb1] True x1none x1some b1b2eq
        unfolding reduce.simps mkIF_def
      by auto (metis le_SucI lookup_update_unfold)
   next
     case False
     show ?thesis 
        using IF.prems (1,2)
        using IF.IH (2) [OF _ vb2] False x1none x1some b1b2eq
        unfolding reduce.simps mkIF_def
      by auto (metis le_SucI lookup_update_unfold)
    qed
  qed
  next
  case False
  then obtain bl where x1envsome: "Mapping.lookup env x1 = Some bl" by auto
  show ?thesis
  proof (cases bl)
    case True
    have r: "reduce env (IF x1 b1 b2) = reduce env b1"
      unfolding reduce.simps using x1envsome True by auto
    show ?thesis
      using IF.prems (1,2) True x1some x1envsome 
      using IF.IH (1) [OF IF.prems (1) vb1] le_SucI by auto
  next
    case False note nbl = False
    have r: "reduce env (IF x1 b1 b2) = reduce env b2"
      unfolding reduce.simps using x1envsome False by auto
    show ?thesis
      using IF.prems (1,2) x1some x1envsome nbl 
      using IF.IH (2) [OF IF.prems (1) vb2] by auto
    qed
  qed
qed

definition depth_path :: "'a ifex \<Rightarrow> nat"
  where "depth_path bdd = (GREATEST n. \<exists>eval. n = length (path eval bdd) \<and>
                            vars bdd \<subseteq> Mapping.keys eval)"

lemma
  valuation_exists:
  fixes bdd :: "'a ifex"
  shows "\<exists>eval::'a env_bool. vars bdd \<subseteq> Mapping.keys eval"
proof (induct bdd)
  case Trueif
  then show ?case by (rule exI [of _ Mapping.empty], simp)
next
  case Falseif
  then show ?case by (rule exI [of _ Mapping.empty], simp)
next
  case (IF x1 bdd1 bdd2)
  from IF.hyps obtain eval1 :: "'a env_bool" and eval2 :: "'a env_bool"
    where v1: "vars bdd1 \<subseteq> Mapping.keys eval1"
    and v2: "vars bdd2 \<subseteq> Mapping.keys eval2" by metis
  show ?case
    apply (rule exI [of _ "Mapping.update x1 True (Mapping.combine (\<lambda>x y. x) eval1 eval2)"])
    using v1 v2 by fastforce
qed

lemma depth_path_exists:
  fixes bdd :: "'a ifex"
  shows "\<exists>n::nat. depth_path bdd = n" by simp

lemma "depth_path Trueif = 0" and "depth_path Falseif = 0"
  unfolding depth_path_def by (simp add: Greatest_equality)+

lemma "depth (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif)) = 2"
  unfolding depth.simps by simp

lemma "depth (reduce Mapping.empty (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif))) = 0"
  unfolding depth.simps reduce.simps mkIF_def by (simp)

lemma "depth_path (IF a\<^sub>1 Falseif Falseif) = 1"
proof (unfold depth_path_def, rule Greatest_equality)
  show "(\<exists>eval.
        1 = length (path eval (IF a\<^sub>1 Falseif Falseif)) \<and>
        vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys eval)"
  proof (rule exI [of _ "Mapping.of_alist [(a\<^sub>1,True)]"], rule conjI)
    show "1 = length (path (Mapping.of_alist [(a\<^sub>1, True)]) (IF a\<^sub>1 Falseif Falseif))"
      unfolding path.simps by (simp add: lookup_of_alist)
    show "vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys (Mapping.of_alist [(a\<^sub>1, True)])"
      by simp
    qed
  next
    fix y :: nat
    show "(\<exists>eval.
            y = length (path eval (IF a\<^sub>1 Falseif Falseif)) \<and>
            vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys eval) \<Longrightarrow> y \<le> 1"
    proof -
      assume e: "\<exists>eval::'a env_bool. y = length (path eval (IF a\<^sub>1 Falseif Falseif)) \<and> 
        vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys eval"
      show "y \<le> 1"
      proof -
      from e obtain eval
        where y: "y = length (path eval (IF a\<^sub>1 Falseif Falseif))" and
                 vars: "vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys eval" by auto
      from vars have "a\<^sub>1 \<in> Mapping.keys eval" by simp
      hence "path eval (IF a\<^sub>1 Falseif Falseif) = [a\<^sub>1]"
        unfolding path.simps
        by (metis bool.case_eq_if in_keysD option.simps(5))
      with y show ?thesis by simp
    qed
  qed
qed

value "depth (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif)))"

lemma "depth_path (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif))) = 3" (is "depth_path ?IF = 3")
proof (unfold depth_path_def, rule Greatest_equality)
  show "(\<exists>eval.
        3 = length (path eval ?IF) \<and>
        vars ?IF \<subseteq> Mapping.keys eval)"
  proof (rule exI [of _ "Mapping.of_alist [(a\<^sub>1,True)]"], rule conjI)
    show "3 = length (path (Mapping.of_alist [(a\<^sub>1, True)]) ?IF)"
      unfolding path.simps by (simp add: lookup_of_alist)
    show "vars ?IF \<subseteq> Mapping.keys (Mapping.of_alist [(a\<^sub>1, True)])"
      by simp
    qed
  next
    fix y :: nat
    show "(\<exists>eval.
            y = length (path eval ?IF) \<and>
            vars ?IF \<subseteq> Mapping.keys eval) \<Longrightarrow> y \<le> 3"
    proof -
      assume e: "\<exists>eval::'a env_bool. y = length (path eval ?IF) \<and> 
        vars ?IF \<subseteq> Mapping.keys eval"
      show "y \<le> 3"
      proof -
      from e obtain eval
        where y: "y = length (path eval ?IF)" and
                 vars: "vars ?IF \<subseteq> Mapping.keys eval" by auto
      from vars have "a\<^sub>1 \<in> Mapping.keys eval" by simp
      hence "path eval ?IF = [a\<^sub>1, a\<^sub>1, a\<^sub>1]"
        unfolding path.simps
        by (metis bool.case_eq_if in_keysD option.simps(5))
      with y show ?thesis by simp
    qed
  qed
qed

lemma "depth_path (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)) = 3" (is "depth_path ?IF = 3")
proof (unfold depth_path_def, rule Greatest_equality)
  show "(\<exists>eval.
        3 = length (path eval ?IF) \<and>
        vars ?IF \<subseteq> Mapping.keys eval)"
  proof (rule exI [of _ "Mapping.of_alist [(a\<^sub>1,True)]"], rule conjI)
    show "3 = length (path (Mapping.of_alist [(a\<^sub>1, True)]) ?IF)"
      unfolding path.simps by (simp add: lookup_of_alist)
    show "vars ?IF \<subseteq> Mapping.keys (Mapping.of_alist [(a\<^sub>1, True)])"
      by simp
    qed
  next
    fix y :: nat
    show "(\<exists>eval.
            y = length (path eval ?IF) \<and>
            vars ?IF \<subseteq> Mapping.keys eval) \<Longrightarrow> y \<le> 3"
    proof -
      assume e: "\<exists>eval::'a env_bool. y = length (path eval ?IF) \<and> 
        vars ?IF \<subseteq> Mapping.keys eval"
      show "y \<le> 3"
      proof -
      from e obtain eval
        where y: "y = length (path eval ?IF)" and
                 vars: "vars ?IF \<subseteq> Mapping.keys eval" by auto
      from vars
      have a1: "a\<^sub>1 \<in> Mapping.keys eval" by simp
      have "path eval ?IF = [a\<^sub>1, a\<^sub>1, a\<^sub>1] \<or> path eval ?IF = [a\<^sub>1, a\<^sub>1]"
      proof (cases "Mapping.lookup eval a\<^sub>1 = None")
        case True show ?thesis using a1
          by (simp add: True domIff keys_dom_lookup)
      next
        case False note a1some = False
        then obtain x1 where x1: "Mapping.lookup eval a\<^sub>1 = Some x1" by auto
        show ?thesis
        proof (cases x1)
          case True
          thus ?thesis unfolding path.simps using a1some x1 by simp
        next
          case False
          thus ?thesis unfolding path.simps using a1some x1 by simp
        qed
      qed
      with y show ?thesis by auto
    qed
  qed
qed

section\<open>Chemins\<close>

fun chemins :: "'a ifex \<Rightarrow> 'a list list"
  where "chemins Trueif = [[]]" |
  "chemins Falseif = [[]]" |
  "chemins (IF x t f) = append (map (Cons x) (chemins t)) (map (Cons x) (chemins f))"

definition chemins_set :: "'a ifex \<Rightarrow> 'a list set"
  where "chemins_set bdd = set (chemins bdd)"

lemma "chemins Trueif = [[]]" by simp

lemma "chemins (IF a1 Falseif Falseif) = [[a1],[a1]]" by simp

lemma "set (chemins Falseif) = {[]}" and "set (chemins Trueif) = {[]}" 
  unfolding chemins_set_def by simp_all

lemma "set (chemins (IF a1 Falseif Falseif)) = {[a1]}" 
  unfolding chemins_set_def by simp

value "chemins (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif)))"

value "set (chemins (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif))))"

lemma
  path_is_chemin:
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
  shows "path eval bdd \<in> set (chemins bdd)"
using v proof (induction bdd arbitrary: eval)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 bdd1 bdd2)
  show ?case
  proof (cases "Mapping.lookup eval x1 = None")
    case True
    then show ?thesis using IF.prems by auto (simp add: keys_is_none_rep)
  next
    case False
    then obtain x11 where m: "Mapping.lookup eval x1 = Some x11" by auto
    have p1: "path eval bdd1 \<in> set (chemins bdd1)" 
      and p2: "path eval bdd2 \<in> set (chemins bdd2)"
      using IF.IH (1,2) using IF.prems by simp_all
    show ?thesis
      using m p1 p2 unfolding path.simps chemins_set_def 
      by (cases x11, auto)
  qed
qed

fun max_list :: "'a::ord list \<Rightarrow> 'a" where
  "max_list (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> max x (max_list xs))"

definition "max_chemins bdd = max_list (map length (chemins bdd))"

value "max_chemins Falseif"

value "max_chemins Trueif"

value "max_chemins (IF a\<^sub>1 Falseif Falseif)"

value "chemins (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif)))"

value "max_chemins (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif)))"

lemma chemins_nonempty[simp]: "chemins bdd \<noteq> []" 
  by (induction bdd) simp_all

lemma chemins_finite[simp]: "finite (set (chemins bdd))"
  by (induction bdd) simp_all

lemma chemins_map: "chemins (IF x1 bdd1 bdd2) = map (Cons x1) (append (chemins bdd1) (chemins bdd2))"
  using chemins.simps (3) by simp

lemma
  assumes a: "a \<in> set (chemins bdd1) \<union> set (chemins bdd1)"
  shows "x1 # a \<in> set (chemins (IF x1 bdd1 bdd2))"
  unfolding chemins_map using a by simp

lemma
  set_chemins_IF_cons:
  assumes a: "a \<in> set (chemins (IF x1 bdd1 bdd2))"
  shows "\<exists>l\<in>set (chemins bdd1) \<union> set (chemins bdd2). a = x1 # l"
  using a unfolding chemins_map by auto

lemma
  max_list_in:
  fixes l :: "'a::ord list"
  assumes l: "l \<noteq> []"
  shows "\<exists>x\<in>(set l). x = max_list l"
  using l by (induct l, auto) (metis list.case_eq_if max_def)

lemma
  max_list_list_in:
  fixes l :: "'a list list"
  assumes l: "l \<noteq> []"
  shows "\<exists>x\<in>(set l). length x = max_list (map length l)"
  using l by (induct l, auto)
   (metis list.case_eq_if list.map_disc_iff max_def)

lemma max_list_Max: 
  assumes xs: "xs \<noteq> []"
  shows "max_list xs = Max (set xs)"
  using xs by (induction xs rule: induct_list012)(auto)

lemma
  max_chemins_in:
  shows "\<exists>l\<in>set(chemins bdd). length l = max_chemins bdd"
  unfolding max_chemins_def
  apply (rule max_list_list_in)
  using chemins_nonempty by auto

lemma
  assumes a: "a \<in> A" and ne: "a \<noteq> Max A" and f: "finite A"
  shows "a \<le> Max A"
  using a ne f by simp

lemma
  max_list_map:
  fixes l :: "nat list"
  assumes l: "l \<noteq> []"
  shows "max_list (map (\<lambda>x. x + 1) l) = 1 + max_list l"
  using l by (induct l, auto) (simp add: list.case_eq_if)

lemma max_list_append:
  fixes l :: "nat list"
  assumes l: "l \<noteq> []" and m: "m \<noteq> []"
  shows "max_list (l @ m) = max (max_list l) (max_list m)"
  using l m by (induct l, auto) (simp add: list.case_eq_if max.assoc)

lemma max_chemins_IF:
  "max_chemins (IF x1 bdd1 bdd2) = 
      1 + max (max_chemins bdd1) (max_chemins bdd2)"
proof -
  have m: "map length (map ((#) x1) (chemins bdd1 @ chemins bdd2)) = 
    map (\<lambda>x. x + 1) (map length (chemins bdd1 @ chemins bdd2))"
    by (induct "(chemins bdd1 @ chemins bdd2)", auto)
  have "max_chemins (IF x1 bdd1 bdd2) =
    max_list (map length (map ((#) x1) (chemins bdd1 @ chemins bdd2)))"
    unfolding max_chemins_def [of "(IF x1 bdd1 bdd2)"]
    unfolding chemins_map ..
  also have "max_list (map length (map ((#) x1) (chemins bdd1 @ chemins bdd2))) =
    1 + max_list (map length (chemins bdd1 @ chemins bdd2))"
    unfolding m
    by (rule max_list_map, simp)
  also have "... = 1 + max_list (map length (chemins bdd1) @ map length (chemins bdd2))"
    by simp
  also have "... = 1 + max (max_list (map length (chemins bdd1))) (max_list (map length (chemins bdd2)))"
    using max_list_append by simp
  also have "... = 1 + max (max_chemins bdd1) (max_chemins bdd2)"
    unfolding max_chemins_def [symmetric]..
  finally show ?thesis .
qed

theorem depth_eq_max_chemins: "depth bdd = max_chemins bdd"
proof (induction bdd)
  case Trueif
  then show ?case unfolding max_chemins_def by auto
next
  case Falseif
  then show ?case unfolding max_chemins_def by auto
next
  case (IF x1 bdd1 bdd2)
  show ?case
  proof (cases "max_chemins bdd1 \<le> max_chemins bdd2")
    case True hence d: "depth bdd1 \<le> depth bdd2" using IF.IH by simp
    have dIF: "depth (IF x1 bdd1 bdd2) = 1 + (depth bdd2)" 
      using d by simp
    have "max_chemins (IF x1 bdd1 bdd2) =
      1 + max (max_chemins bdd1) (max_chemins bdd2)"
      by (rule max_chemins_IF)
    hence mIF: "max_chemins (IF x1 bdd1 bdd2) = 1 + (max_chemins bdd2)"
      using True by simp
    show ?thesis unfolding dIF mIF using IF.IH (2) by simp
  next
    case False hence d: "depth bdd2 < depth bdd1" using IF.IH by simp
    have dIF: "depth (IF x1 bdd1 bdd2) = 1 + (depth bdd1)" 
      using d by simp
    have "max_chemins (IF x1 bdd1 bdd2) =
      1 + max (max_chemins bdd1) (max_chemins bdd2)"
      by (rule max_chemins_IF)
    hence mIF: "max_chemins (IF x1 bdd1 bdd2) = 1 + (max_chemins bdd1)"
      using False by simp
    show ?thesis unfolding dIF mIF using IF.IH (1) by simp
  qed
qed

corollary depth_path_le_max_chemins: 
  "depth_path (bdd::'a ifex) \<le> max_chemins bdd"
proof (rule ccontr)
  assume "\<not> depth_path bdd \<le> max_chemins bdd"
  hence "\<exists>eval. length (path eval bdd) > max_chemins bdd \<and> vars bdd \<subseteq> Mapping.keys eval"
    unfolding depth_path_def using depth_path_exists [of bdd]
    by auto (smt (z3) GreatestI_nat le_refl less_imp_le_nat nat_neq_iff valuation_exists)
  then obtain eval where leval: "length (path eval bdd) > max_chemins bdd" 
    and vbdd: "vars bdd \<subseteq> Mapping.keys eval" by auto
  show False 
    using path_is_chemin [OF vbdd] leval
    unfolding max_chemins_def 
    using chemins_nonempty [of bdd]
    by auto (metis (no_types, lifting) List.finite_set Max_ge imageI \<open>chemins bdd \<noteq> []\<close> le_imp_less_Suc list.map_disc_iff list.set_map max_list_Max not_less_eq)
qed

corollary "depth_path bdd \<le> depth bdd"
  by (simp add: depth_eq_max_chemins depth_path_le_max_chemins)

section\<open>Free Binary Decision Diagrams\<close>

text\<open>Free binary decision diagrams (FBDDs) are graph-based 
  data structures representing Boolean functions with the 
  constraint (additional to binary decision diagram) that 
  each variable is tested at most once during the computation.\<close>

abbreviation "fbdd == ifex_no_twice"

value "fbdd (IF x1 Trueif Falseif)"

value "fbdd (IF x1 (IF x1 Trueif Falseif) Falseif)"

lemma
  assumes f: "fbdd (IF x1 bdd1 bdd2)"
  shows "fbdd bdd1" using f by simp

lemma
  assumes f: "fbdd (IF x1 bdd1 bdd2)"
  shows "fbdd bdd2" using f by simp

lemma
  assumes f: "fbdd (IF x1 bdd1 bdd2)"
  shows "x1 \<notin> vars (bdd1)" using f by simp

lemma
  assumes f: "fbdd (IF x1 bdd1 bdd2)"
  shows "x1 \<notin> vars (bdd2)" using f by simp

lemma
  assumes f: "fbdd (IF x1 bdd1 bdd2)" 
  shows "depth_path (IF x1 bdd1 bdd2) = 1 + max (depth_path bdd1) (depth_path bdd2)"
proof (cases "depth_path bdd1 < depth_path bdd2")
  case True
  obtain n where g: "(GREATEST n.
      \<exists>eval. n = length (path eval bdd2) \<and> vars bdd2 \<subseteq> Mapping.keys eval) =
      n" by simp
  have "(\<exists>eval. n = length (path eval bdd2) \<and> vars bdd2 \<subseteq> Mapping.keys eval)"
    using Greatest_equality [OF ]
  
    unfolding depth_path_def
    using Greatest_equality
    unfolding depth_path_def using Greatest_equality apply auto try
    find_theorems "(GREATEST n. ?P n)"
    then obtain eval :: "'a env_bool"
    where "n = length (path eval bdd2) \<and> vars bdd2 \<subseteq> Mapping.keys eval" 
    unfolding depth_path_def
    unfolding Greatest_def apply auto
    try using True unfolding depth_path_def
  

lemma assumes f: "fbdd bdd"
  shows "depth bdd = depth_path bdd" 
  using f proof (induction bdd)
  case Trueif
  then show ?case
    by (metis bot_nat_0.extremum_uniqueI depth.simps(1) depth_eq_max_chemins depth_path_le_max_chemins)
next
  case Falseif
  then show ?case
    by (metis bot_nat_0.extremum_uniqueI depth.simps(2) depth_eq_max_chemins depth_path_le_max_chemins)
next
  case (IF x1 bdd1 bdd2)
  then show ?case 
  proof -
    have dbbd1: "depth bdd1 = depth_path bdd1" and 
      dbdd2: "depth bdd2 = depth_path bdd2"
      using IF.IH (1,2) IF.prems by simp_all
    show ?thesis
    proof (cases "(depth bdd1) < (depth bdd2)")
      case True
      hence "max (depth bdd1) (depth bdd2) = (depth bdd2)" by simp
      show ?thesis unfolding depth_path_def
      unfolding depth.simps depth_path_def  
    
qed







(*datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex*)

datatype ifex = CIF bool | IF nat ifex ifex

primrec 
valif :: "ifex => (nat => bool) => bool"
  where
  "valif (CIF b)    env = b" |
  "valif (IF b f t) env = (if env b then valif f env
                                      else valif t env)"

(*primrec valif :: "ifex => (nat => bool) => bool"
  where
  "valif (CIF b)    env = b" |
  "valif (VIF x)    env = env x" |
  "valif (IF b t e) env = (if valif b env then valif t env
                                      else valif e env)"
*)

lemma "valif (CIF True) f" by simp

lemma "\<not> valif (CIF False) f" by simp

(*lemma "valif (VIF 3) (\<lambda>x. True)" by simp*)

(*lemma "\<not> valif (VIF 3) (\<lambda>x. False)" by simp*)

lemma "valif (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp

(*lemma "valif (IF (VIF 3) (IF (VIF 3) (CIF True) (CIF False))
                         (IF (VIF 3) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp*)

(*lemma "\<not> valif (IF (VIF 3) (IF (VIF 2) (CIF True) (CIF False))
                         (IF (VIF 4) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp*)

lemma "\<not> valif (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False)))
              (\<lambda>x. if x = 2 then True else False)" by simp

(*lemma "\<not> valif (IF (VIF 3) (IF (VIF 3) (CIF True) (CIF False))
                         (IF (VIF 3) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 2 then True else False)" by simp*)

lemma "\<not> valif (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False)))
              (\<lambda>x. if x = 3 then True else False)" by simp

(*lemma "\<not> valif (IF (VIF 1) (IF (VIF 2) (IF (VIF 3) (IF (VIF 4) (CIF True) (CIF False)) 
                                                   (IF (VIF 4) (CIF True) (CIF False)))
                                       (IF (VIF 3) (IF (VIF 4) (CIF True) (CIF False)) 
                                                   (IF (VIF 4) (CIF True) (CIF False))))
                           (IF (VIF 4) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp*)

fun vars :: "ifex \<Rightarrow> nat set" 
  where
  "vars (IF v f t) =  insert v (vars f \<union> vars t)" |
  "vars (CIF b) = {}"

fun ifex_unique_var :: "ifex \<Rightarrow> bool"
  where
    "ifex_unique_var (CIF b) = True" |
    "ifex_unique_var (IF n f t) = (n \<notin> vars t \<and> n \<notin> vars f)"


lemma "ifex_unique_var (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False)))" by simp

lemma "\<not> ifex_unique_var (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False)))" by simp

fun depth :: "ifex \<Rightarrow> nat"
  where 
    "depth (CIF b) = 0" |
    "depth (IF b f t) = 1 + min (depth f) (depth t)" 

lemma "depth (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False))) = 2" by simp

text\<open>Pending definition\<close>

fun reduce :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> ifex"
  where
    "reduce (CIF b) env = CIF b" |
    "reduce (IF a f t) env = (if f = t then (reduce f env) else IF a (reduce f (env(a:=True)))
                               (reduce t (env(a:=False))))"

value "reduce (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False))) (\<lambda>x. if x = 3 then False else True)"

section\<open>Boolean expressions\<close>

text\<open>We are interested in boolean expressions that come from
  simplicial complexes, that is, collections of simplices
  that can be expressed as conjunctive normal forms.\<close>

datatype 'a bexp =
  Const bool |
  Atom 'a |
  Neg "'a bexp" |
  And "'a bexp" "'a bexp" |
  Or "'a bexp" "'a bexp"

fun bval where
  "bval (Const b) s = b" |
  "bval (Atom a) s = s a" |
  "bval (Neg b) s = (\<not> bval b s)" |
  "bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
  "bval (Or b1 b2) s = (bval b1 s \<or> bval b2 s)"

fun bool_expr_of_bexp :: "'a bexp \<Rightarrow> 'a bool_expr" 
where
  "bool_expr_of_bexp (Const b) = Const_bool_expr b" 
  | "bool_expr_of_bexp (Atom a) = Atom_bool_expr a" 
  | "bool_expr_of_bexp (Neg b) = Neg_bool_expr(bool_expr_of_bexp b)" 
  | "bool_expr_of_bexp (And b1 b2) = And_bool_expr (bool_expr_of_bexp b1) (bool_expr_of_bexp b2)"
  | "bool_expr_of_bexp (Or b1 b2) = Or_bool_expr (bool_expr_of_bexp b1) (bool_expr_of_bexp b2)"

lemma val_preservation:
  "val_bool_expr (bool_expr_of_bexp b) s = bval b s"
  by (induction b) auto 
term range
definition bexp_from_simplice :: "nat set => nat \<Rightarrow> nat bexp"
  where "bexp_from_simplice \<sigma> n = range
    (\<lambda>i. if i \<in> \<sigma> then (And i (bexp_from_simplice (\<sigma> - {i})) else (bexp_from_simplice (\<sigma> - {i})) {..<n}"



lemma
  
  
  
  assumes "depth (IF a t f) = n"
    and "a \<in> vars t"
  shows "True"


end