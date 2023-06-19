
theory Binary_Decision_Diagrams
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

value "depth (reduce_alist [] (IF finite_4.a\<^sub>1
                (IF finite_4.a\<^sub>1
                  (IF finite_4.a\<^sub>2 (IF finite_4.a\<^sub>3 Trueif Falseif) 
                                  (IF finite_4.a\<^sub>4 Falseif Trueif)) 
                  Trueif)
                Trueif))"


value "depth (reduce_alist [(finite_4.a\<^sub>1, False)] 
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

section\<open>The set of admissible BDTs for a given boolean function.\<close>

definition admissible_bdt :: "('a \<Rightarrow> bool) \<Rightarrow> ('a ifex) set"
  where "admissible_bdt f = {s. \<exists>env. vars s \<subseteq> Mapping.keys env \<and> agree f env = val_ifex s f}"

text\<open>An ifex representing a boolean function\<close>

lemma "(IF finite_4.a\<^sub>3 Trueif (IF finite_4.a\<^sub>1 Falseif Trueif)) \<in>
      admissible_bdt 
        (%x. if x = finite_4.a\<^sub>3 then True else if x = finite_4.a\<^sub>1 then False else True)"
  by (unfold admissible_bdt_def, rule, rule exI [of _ "(Mapping.update finite_4.a\<^sub>3 True (Mapping.update finite_4.a\<^sub>1 False Mapping.empty))"], rule conjI, auto simp add: agree_Nil agree_Cons)

text\<open>The order of the variables can change, but the ifex represents the same boolean function\<close>

lemma "(IF finite_4.a\<^sub>1 Falseif (IF finite_4.a\<^sub>3 Trueif Trueif))
         \<in> admissible_bdt 
        (%x. if x = finite_4.a\<^sub>3 then True else if x = finite_4.a\<^sub>1 then False else True)"
  by (unfold admissible_bdt_def, rule, rule exI [of _ "(Mapping.update finite_4.a\<^sub>3 True (Mapping.update finite_4.a\<^sub>1 False Mapping.empty))"], rule conjI, auto simp add: agree_Nil agree_Cons)

text\<open>The ifex may not be reduced, but still represents the same boolean function\<close>

lemma "(IF finite_4.a\<^sub>1
          (IF finite_4.a\<^sub>1 Falseif (IF finite_4.a\<^sub>3 Trueif Trueif))
            (IF finite_4.a\<^sub>3 Trueif Trueif))
         \<in> admissible_bdt 
        (%x. if x = finite_4.a\<^sub>3 then True else if x = finite_4.a\<^sub>1 then False else True)"
  by (unfold admissible_bdt_def, rule, rule exI [of _ "(Mapping.update finite_4.a\<^sub>3 True (Mapping.update finite_4.a\<^sub>1 False Mapping.empty))"], rule conjI, auto simp add: agree_Nil agree_Cons)

lemma "agree
            (%x. if x = finite_4.a\<^sub>3 then False else if x = finite_4.a\<^sub>1 then False else True)
             (Mapping.update finite_4.a\<^sub>3 False (Mapping.update finite_4.a\<^sub>1 False Mapping.empty))"
  by (simp add: agree_Cons agree_Nil)

section\<open>Ifex where variables appear only once.\<close>

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

fun path :: "'a env_bool \<Rightarrow> 'a ifex \<Rightarrow> 'a list option"
  where "path _ Trueif = Some []" |
  "path _ Falseif = Some []" |
  "path eval (IF x t f) = (case Mapping.lookup eval x of 
      None \<Rightarrow> None |
      Some True \<Rightarrow> (case (path eval t) of 
                        None \<Rightarrow> None |
                        Some l \<Rightarrow> Some (x # l)) |
      Some False \<Rightarrow> (case (path eval f) of 
                        None \<Rightarrow> None |
                        Some l \<Rightarrow> Some (x # l)))"

value "path Mapping.empty (IF x Trueif Falseif)"

lemma "path (Mapping.update x False env) (IF x (IF y Trueif Falseif) Falseif) 
  = Some [x]"
  by simp

lemma "path (Mapping.of_alist [(x, True), (y, True)]) 
                  (IF x (IF y Trueif Falseif) Falseif) 
  = Some [x, y]"
  by auto (simp add: lookup_of_alist)

definition olength :: "'a list option \<Rightarrow> nat option"
  where "olength l = (case l of None \<Rightarrow> None | Some m \<Rightarrow> Some (length m))"

value "olength (path (Mapping.of_alist [(finite_4.a\<^sub>1, True)]) 
            (IF finite_4.a\<^sub>1 Falseif Falseif))"

value "olength (path (Mapping.of_alist [(finite_4.a\<^sub>3, False)])
            (IF finite_4.a\<^sub>3 (IF finite_4.a\<^sub>1 Falseif Falseif) (Falseif)))"

lemma
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

lemma
  assumes v: "vars bdd \<subseteq> Mapping.keys eval"
    and c: "\<forall>x\<in>Mapping.keys eval.
          (Mapping.lookup env x = Mapping.lookup eval x \<or> Mapping.lookup env x = None)"
    and li: "olength (path eval (reduce env bdd)) = Some i"
    and lj: "olength (path eval bdd) = Some j"
  shows "i \<le> j"
  using c v li lj proof (induction bdd arbitrary: eval env i j)
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
  obtain x11 where x1some: "Mapping.lookup eval x1 = Some x11"
    using x1 by (meson in_keysD)
  obtain lb1 where pb1: "path eval b1 = Some lb1" by (meson path_some vb1)
  obtain lb2 where pb2: "path eval b2 = Some lb2" by (meson path_some vb2)
  obtain lrb1t where pb1t: "path eval (reduce (Mapping.update x1 True env) b1) = Some lrb1t"
    using path_reduce_some vb1 by blast
  obtain lrb1f where pb1f: "path eval (reduce (Mapping.update x1 False env) b1) = Some lrb1f"
    using path_reduce_some vb1 by blast
  obtain lrb2t where pb2t: "path eval (reduce (Mapping.update x1 True env) b2) = Some lrb2t"
    using path_reduce_some vb2 by blast
  obtain lrb2f where pb2f: "path eval (reduce (Mapping.update x1 False env) b2) = Some lrb2f"
    using path_reduce_some vb2 by blast
  obtain i1 where oreb1: "olength (path eval (reduce env b1)) = Some i1"
    using olength_reduce_some [OF vb1] by auto
  obtain i12 where oreb12: "olength (path eval (reduce (Mapping.update x1 True env) b1)) = Some i12"
    using olength_reduce_some [OF vb1] by auto
  obtain j1 where ob1: "olength (path eval b1) = Some j1"
    using olength_some [OF vb1] by auto
  have i1j1: "i1 \<le> j1" using IF.IH (1) [OF IF.prems (1) vb1 oreb1 ob1] .
  (*have i12j1: "i12 \<le> j1" using IF.IH (1) [OF _ vb1 oreb12 ob1] .*)
  obtain i2 where oreb2: "olength (path eval (reduce env b2)) = Some i2"
    using olength_reduce_some [OF vb2] by auto
  obtain i22 where oreb22: "olength (path eval (reduce (Mapping.update x1 False env) b2)) = Some i22"
    using olength_reduce_some [OF vb2] by auto
  obtain j2 where ob2: "olength (path eval b2) = Some j2"
    using olength_some [OF vb2] by auto
  have i2j2: "i2 \<le> j2" using IF.IH (2) [OF IF.prems (1) vb2 oreb2 ob2] .
  (*have i22j2: "i22 \<le> j2" using IF.IH (2) [OF _ vb2 oreb22 ob2] .*)
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
      case False
      hence mk: "mkIF x1 (reduce (Mapping.update x1 True env) b1)  
              (reduce (Mapping.update x1 False env) b2) = 
        IF x1 (reduce (Mapping.update x1 True env) b1)  
              (reduce (Mapping.update x1 False env) b2)" 
        unfolding mkIF_def by simp
      show ?thesis
      proof (cases "x11")
        case True
        have i12j1: "i12 \<le> j1" 
          using IF.IH (1) [OF _ vb1 oreb12 ob1] 
            IF.prems (1) x1none
          by (simp add: True lookup_update_unfold x1some)
        have li12: "length (the (path eval (reduce (Mapping.update x1 True env) b1)))
          = i12"
            and li: "length (the (path eval (reduce env (IF x1 b1 b2)))) = i"
          using pb1t oreb12 IF.prems (3)
          unfolding olength_def apply simp_all
          by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.sel)
        have "i = i12 + 1"
          unfolding li12 [symmetric] li [symmetric]
          unfolding r mk unfolding path.simps 
          using True x1some pb1t by auto
        moreover have "length (the (path eval (IF x1 b1 b2))) = j"
          and "j = j1 + 1" using IF.prems (4) unfolding path.simps
          using x1some using ob1 unfolding olength_def using True
           apply auto
            apply (metis option.case_eq_if option.distinct(1) option.sel)
          by (smt (verit, ccfv_SIG) True length_Cons option.case_eq_if option.distinct(1) option.sel)
        ultimately show ?thesis using IF.prems (2,3) 
          using i12j1 oreb12
          unfolding olength_def by auto
      next
        case False
        have i22j2: "i22 \<le> j2" 
          using IF.IH (2) [OF _ vb2 oreb22 ob2] 
            IF.prems (1) x1none
          by (simp add: False lookup_update_unfold x1some)
        have li22: "length (the (path eval (reduce (Mapping.update x1 False env) b2)))
          = i22"
            and li: "length (the (path eval (reduce env (IF x1 b1 b2)))) = i"
          using pb2f oreb22 IF.prems (3)
          unfolding olength_def apply simp_all
          by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.sel)
        have "i = i22 + 1"
          unfolding li22 [symmetric] li [symmetric]
          unfolding r mk unfolding path.simps 
          using False x1some pb2f by auto
        moreover have "length (the (path eval (IF x1 b1 b2))) = j"
          and "j = j2 + 1" using IF.prems (4) unfolding path.simps
          using x1some using ob2 unfolding olength_def using False
           apply auto
            apply (metis option.case_eq_if option.distinct(1) option.sel)
          by (smt (verit, ccfv_SIG) False length_Cons option.case_eq_if option.distinct(1) option.sel)
        ultimately show ?thesis using IF.prems (2,3)
          using i22j2 oreb22
          unfolding olength_def by auto        
      qed
    next
      case True note b1b2eq = True
      have rb1: "reduce env (IF x1 b1 b2) = reduce (Mapping.update x1 True env) b1"
        unfolding r unfolding mkIF_def using True
        unfolding reduce.simps using x1some by auto
      show ?thesis
      proof (cases "x11")
        case True
        have i12j1: "i12 \<le> j1" 
          using IF.IH (1) [OF _ vb1 oreb12 ob1] 
            IF.prems (1) x1none
          by (simp add: True lookup_update_unfold x1some)
        have li12: "length (the (path eval (reduce (Mapping.update x1 True env) b1)))
          = i12"
            and li: "length (the (path eval (reduce env (IF x1 b1 b2)))) = i"
          using pb1t oreb12 IF.prems (3) 
          unfolding olength_def apply simp_all
          by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.sel)
        have "i12 \<le> i"
          unfolding li12 [symmetric] li [symmetric]
          unfolding r rb1 unfolding path.simps 
          using True x1some pb1t
          using r rb1 by auto
        moreover have "length (the (path eval (IF x1 b1 b2))) = j"
          and "j = j1 + 1" using IF.prems (4) unfolding path.simps
          using x1some using ob1 unfolding olength_def using True
           apply auto
            apply (metis option.case_eq_if option.distinct(1) option.sel)
          by (smt (verit, ccfv_SIG) True length_Cons option.case_eq_if option.distinct(1) option.sel)
        ultimately show ?thesis using IF.prems (2,3) 
          using i12j1 oreb12
          unfolding olength_def
          by (metis li li12 rb1 trans_le_add1)
      next
        case False
        have i22j2: "i22 \<le> j2" 
          using IF.IH (2) [OF _ vb2 oreb22 ob2] 
            IF.prems (1) x1none
          by (simp add: False lookup_update_unfold x1some)
        have li22: "length (the (path eval (reduce (Mapping.update x1 False env) b2)))
          = i22"
            and li: "length (the (path eval (reduce env (IF x1 b1 b2)))) = i"
          using pb2f oreb22 IF.prems (3) 
          unfolding olength_def apply simp_all
          by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.sel)
        have "i22 \<le> i"
          unfolding li22 [symmetric] li [symmetric]
          unfolding r rb1 unfolding path.simps 
          using True x1some pb1t
          using r rb1 by auto
        moreover have "length (the (path eval (IF x1 b1 b2))) = j"
          and "j = j2 + 1" using IF.prems (4) unfolding path.simps
          using x1some using ob2 unfolding olength_def using False
           apply auto
            apply (metis option.case_eq_if option.distinct(1) option.sel)
          by (smt (verit, ccfv_SIG) False length_Cons option.case_eq_if option.distinct(1) option.sel)
        ultimately show ?thesis using IF.prems (2,3) 
          using i22j2 oreb12
          unfolding olength_def
          by (metis True li li22 rb1 trans_le_add1)
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
      proof (cases "x11")
        case True
        have li12: "length (the (path eval (reduce env b1)))
          = i1"
            and li: "length (the (path eval (reduce env (IF x1 b1 b2)))) = i"
          using vb1 oreb1 IF.prems (3)
          unfolding olength_def apply simp_all
          apply (simp add: option.case_eq_if path_reduce_exists)
          by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.inject)
        have "i1 = i"
          unfolding li12 [symmetric] li [symmetric]
          unfolding r unfolding path.simps ..
        moreover have "length (the (path eval (IF x1 b1 b2))) = j"
          and "j = j1 + 1" using IF.prems (4) unfolding path.simps
          using x1some using ob1 unfolding olength_def using True
           apply auto
            apply (metis option.case_eq_if option.distinct(1) option.sel)
          by (smt (verit, ccfv_SIG) True length_Cons option.case_eq_if option.distinct(1) option.sel)
        ultimately show ?thesis using IF.prems (2,3) 
          using i1j1 oreb12
          unfolding olength_def by auto
      next
        case False
        with IF.prems (1) x1some x1envsome True have False
          using x1 by fastforce
        thus ?thesis by fast
      qed
    next
      case False note nbl = False
      have r: "reduce env (IF x1 b1 b2) = reduce env b2"
        unfolding reduce.simps using x1envsome False by auto
      show ?thesis
      proof (cases "x11")
        case False
        have li12: "length (the (path eval (reduce env b2)))
          = i2"
            and li: "length (the (path eval (reduce env (IF x1 b1 b2)))) = i"
          using vb2 oreb2 IF.prems (3)
          unfolding olength_def apply simp_all
          apply (simp add: option.case_eq_if path_reduce_exists)
          by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.inject)
        have "i2 = i"
          unfolding li12 [symmetric] li [symmetric]
          unfolding r unfolding path.simps ..
        moreover have "length (the (path eval (IF x1 b1 b2))) = j"
          and "j = j2 + 1" using IF.prems (4) unfolding path.simps
          using x1some using ob2 unfolding olength_def using False
           apply auto
            apply (metis option.case_eq_if option.distinct(1) option.sel)
          by (smt (verit, ccfv_SIG) False length_Cons option.case_eq_if option.distinct(1) option.sel)
        ultimately show ?thesis using IF.prems (2,3) 
          using i2j2 oreb12
          unfolding olength_def by auto
      next
        case True
        with IF.prems (1) x1some x1envsome nbl have False
          using x1 by fastforce
        thus ?thesis by fast
      qed
    qed
  qed
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