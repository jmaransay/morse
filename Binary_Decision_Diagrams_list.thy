
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
    "depth (IF b t f) = 1 + min (depth t) (depth f)"

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

lemma depth_mkIF: "depth (mkIF x t1 t2) \<le> Suc (min (depth t1) (depth t2))"
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
  also have "... \<le> Suc (min (depth ?xt) (depth ?xf))"
      using depth_mkIF by metis
  also have "... \<le> Suc (min (depth t) (depth f))"
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
  where "depth_path bdd = (LEAST n. \<exists>eval. n = length (path eval bdd) \<and>
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
    and v2: "vars bdd2 \<subseteq> Mapping.keys eval2" by (metis keys_map_values)
  show ?case
    apply (rule exI [of _ "Mapping.update x1 True (Mapping.combine (\<lambda>x y. x) eval1 eval2)"])
    using v1 v2 by fastforce
qed

lemma depth_path_exists:
  fixes bdd :: "'a ifex"
  shows "\<exists>n::nat. depth_path bdd = n" by simp

lemma "depth_path Trueif = 0" and "depth_path Falseif = 0"
  unfolding depth_path_def by simp_all

lemma "depth (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif)) = 1"
  unfolding depth.simps by simp

lemma "depth (reduce Mapping.empty (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif))) = 0"
  unfolding depth.simps reduce.simps mkIF_def by (simp)

lemma "depth_path (IF a\<^sub>1 Falseif Falseif) = 1" 
proof (unfold depth_path_def, rule Least_equality)
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
            vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys eval) \<Longrightarrow> 1 \<le> y "
    proof -
      assume e: "\<exists>eval::'a env_bool. y = length (path eval (IF a\<^sub>1 Falseif Falseif)) \<and> 
        vars (IF a\<^sub>1 Falseif Falseif) \<subseteq> Mapping.keys eval"
      show "1 \<le> y"
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
       (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif )) = 2" (is "depth_path ?IF = 2")
proof (unfold depth_path_def, rule Least_equality)
  show "(\<exists>eval.
        2 = length (path eval ?IF) \<and>
        vars ?IF \<subseteq> Mapping.keys eval)"
  proof (rule exI [of _ "Mapping.of_alist [(a\<^sub>1,False)]"], rule conjI)
    show "2 = length (path (Mapping.of_alist [(a\<^sub>1, False)]) ?IF)"
      unfolding path.simps by (simp add: lookup_of_alist)
    show "vars ?IF \<subseteq> Mapping.keys (Mapping.of_alist [(a\<^sub>1, False)])"
      by simp
    qed
  next
    fix y :: nat
    show "(\<exists>eval.
            y = length (path eval ?IF) \<and>
            vars ?IF \<subseteq> Mapping.keys eval) \<Longrightarrow> 2 \<le> y "
    proof -
      assume e: "\<exists>eval::'a env_bool. y = length (path eval ?IF) \<and> 
        vars ?IF \<subseteq> Mapping.keys eval"
      show "2 \<le> y"
      proof -
      from e obtain eval
        where y: "y = length (path eval ?IF)" and
                 vars: "vars ?IF \<subseteq> Mapping.keys eval" by auto
      from vars have "a\<^sub>1 \<in> Mapping.keys eval" by simp
      hence "path eval ?IF = [a\<^sub>1, a\<^sub>1]"
        unfolding path.simps try
        by (metis bool.case_eq_if in_keysD option.simps(5))
      with y show ?thesis by simp
    qed
  qed
qed


lemma "depth_path (IF a\<^sub>1 (IF a\<^sub>1 (IF a\<^sub>1 Falseif Falseif) Falseif)
       (IF a\<^sub>1 Falseif (IF a\<^sub>1 Falseif Falseif))) = 3" (is "depth_path ?IF = 3")
proof (unfold depth_path_def, rule Least_equality)
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
            vars ?IF \<subseteq> Mapping.keys eval) \<Longrightarrow> 3 \<le> y "
    proof -
      assume e: "\<exists>eval::'a env_bool. y = length (path eval ?IF) \<and> 
        vars ?IF \<subseteq> Mapping.keys eval"
      show "3 \<le> y"
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

lemma "depth bdd = depth_path bdd" try
proof (induct bdd)
  case Trueif
  then show ?case unfolding depth.simps depth_path_def by simp
next
  case Falseif
  then show ?case unfolding depth.simps depth_path_def by simp
next
  case (IF x1 bdd1 bdd2)
  obtain env1 where "(LEAST n.
            \<exists>eval. n = length (path eval bdd1) \<and> vars bdd1 \<subseteq> Mapping.keys eval) 
          =
        depth_path bdd1" using depth_path_def by metis
  then obtain n where "(\<exists>eval. n = length (path eval bdd1) \<and> vars bdd1 \<subseteq> Mapping.keys eval)"
    try
  obtain env1 where "depth_path bdd1 = length (path env1 bdd1)" and
                            "vars bdd1 \<subseteq> Mapping.keys env1"
    unfolding depth_path_def find_theorems "(LEAST n. _)" try
  show ?case
  proof (cases "Mapping.lookup env x1 = None")
    case True
    
qed
  

lemma
  assumes x: "x \<notin> Mapping.keys env"
  shows "depth (reduce env (IF x b1 b2)) \<le> depth (IF x b1 b2)"
  using x proof (induct rule: reduce.induct)
  case ("2_1" env)
  show ?case by simp
next
  case ("2_2" env)
  show ?case by simp
next
  case (1 uu x t1 t2)
  from "1.prems" have "Mapping.lookup uu y = None" try
  show ?case using "1.hyps" and "1.prems" sorry
qed

proof (induct b)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b1 b2)
  then show ?case sorry
qed


lemma "depth (reduce_alist [] b) \<le> depth b"
proof (induct b)
  case Trueif
  show ?case by simp
next
  case Falseif
  show ?case by simp
next
  case (IF x1 b1 b2)
  show ?case 
    unfolding reduce_alist.simps 
  proof (simp)
    have "depth (mkIF x1 (reduce_alist [(x1, True)] b1) (reduce_alist [(x1, False)] b2))
    \<le> Suc (min (depth (reduce_alist [(x1, True)] b1)) (depth (reduce_alist [(x1, False)] b2)))"
      by (rule depth_mkIF)
    have "depth (reduce_alist [(x1, True)] b1) \<le> depth b1 + 1"
    proof (induct b1)
      case Trueif
      then show ?case by simp
    next
      case Falseif
      then show ?case by simp
    next
      case (IF x2 b11 b12)
      show ?case proof (cases "x1 = x2")
        case True
        show ?thesis unfolding True reduce_alist.simps 
          apply simp using IF.hyps (1)
          apply auto unfolding True
          using suc_min
        try
        by (metis add.commute le_add_same_cancel2 reduce_alist.elims reduce_alist.simps(1) zero_order(1))
    qed
      try
      show "depth (mkIF x1 (reduce_alist [(x1, True)] b1) (reduce_alist [(x1, False)] b2))
    \<le> Suc (min (depth b1) (depth b2))"
      using IF.hyps using depth_mkIF
    
         try
  proof (cases "Mapping.lookup env x1")
    case None
    have "depth (mkIF x1 (reduce (Mapping.update x1 True env) b1) (reduce (Mapping.update x1 False env) b2)) 
          \<le> depth (IF x1 b1 b2)"
      unfolding depth.simps (3)
      using IF.hyps (1) [of "(Mapping.update x1 True env)"]
      using IF.hyps (2) [of "(Mapping.update x1 False env)"]
      unfolding mkIF_def by auto
    thus ?thesis using None unfolding reduce.simps by simp
  next
    case (Some b)
    show ?thesis
    proof (cases b)
      case True note b = True
      show ?thesis
      proof (cases "depth b1 \<le> depth b2")
        case True hence db1: "depth (IF x1 b1 b2) = Suc (depth b1)" by simp
        show ?thesis unfolding reduce.simps Some using b using db1
          by (simp add: IF.hyps(1) le_SucI)
      next
        case False hence db2: "depth (IF x1 b1 b2) = Suc (depth b2)" by simp
        show ?thesis unfolding reduce.simps Some using b using IF.hyps(1,2) [of env] using db2
          apply auto try

      qed
      
        using Some unfolding reduce.simps using True apply simp sorry
    next
      case False
      then show ?thesis sorry
    qed
      unfolding reduce.simps
    have "depth (reduce env (IF x1 b1 b2)) \<le> depth (IF x1 b1 b2)" try
    have "depth (reduce env (if b then b1 else b2)) \<le> depth (IF x1 b1 b2)"
      using IF.hyps [of env] apply (cases b) apply auto try
      unfolding reduce.simps

    show ?thesis unfolding reduce.simps
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