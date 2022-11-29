
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

value "depth (reduce_alist  [(finite_4.a\<^sub>1, True)] (IF finite_4.a\<^sub>1
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
lemma vars_IFF_subset: "vars f\<subseteq> vars (IF x t f)" by auto

fun ifex_no_twice where 
  "ifex_no_twice (IF v t e) = (
  v \<notin> (vars t \<union> vars e) \<and> ifex_no_twice t \<and> ifex_no_twice e)" |
 "ifex_no_twice _ = True"

lemma
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

lemma
  (*assumes k: "Mapping.keys env = {}"*)
  shows "depth (reduce env b) \<le> depth b" nitpick
(*using k*)
proof (induction b arbitrary: env)
  case Trueif
  then show ?case by simp
next
  case Falseif
  then show ?case by simp
next
  case (IF x1 b1 b2)
  show ?case proof (cases "Mapping.lookup env x1 = None")
    case True
    have rhs: "depth (IF x1 b1 b2) = 1 + min (depth b1) (depth b2)" by simp
    have r: "reduce env (IF x1 b1 b2) =
        (mkIF x1 (reduce (Mapping.update x1 True env) b1) 
                (reduce (Mapping.update x1 False env) b2))"
    using True reduce.simps (1) [of env x1] mkIF_def by simp
    moreover have "depth (mkIF x1 (reduce (Mapping.update x1 True env) b1) 
                (reduce (Mapping.update x1 False env) b2))
  \<le> 1 + min (depth (reduce (Mapping.update x1 True env) b1)) 
            (depth (reduce (Mapping.update x1 False env) b2))"
      using depth_mkIF by simp
    moreover have "depth (reduce (Mapping.update x1 True env) b1) \<le> depth b1"
      using IF.IH (1) by simp
    moreover have "depth (reduce (Mapping.update x1 True env) b2) \<le> depth b2"
      using IF.IH (2) by simp
    ultimately
    have "depth (reduce env (IF x1 b1 b2)) \<le> 1 + min (depth b1) (depth b2)"
      by (smt (verit, ccfv_SIG) IF.IH(2) add_left_mono dual_order.trans min.mono)
    thus ?thesis using rhs by simp
  next
    case False
    then obtain b where x1b: "Mapping.lookup env x1 = Some b" by auto
    show ?thesis
    proof (cases b)
      case True
      have r: "reduce env (IF x1 b1 b2) = (reduce env b1)" 
        using reduce.simps True x1b by auto
      have db1: "depth (reduce env b1) \<le> depth b1" using IF.IH by simp
      have db2: "depth (reduce env b2) \<le> depth b2" using IF.IH by simp
      show ?thesis unfolding r using db1 db2 unfolding depth.simps (3) try sorry
    next
      case False
      then show ?thesis sorry
    qed

lemma
  assumes x: "Mapping.lookup env x = None"
  shows "depth (reduce env (IF x b1 b2)) \<le> depth (IF x b1 b2)"
proof
 have rhs: "depth (IF x1 b1 b2) = 1 + min (depth b1) (depth b2)" by simp
    have r: "reduce env (IF x1 b1 b2) =
        (mkIF x1 (reduce (Mapping.update x1 True env) b1) 
                (reduce (Mapping.update x1 False env) b2))"
    using True reduce.simps (1) [of env x1] mkIF_def by simp
    moreover have "depth (mkIF x1 (reduce (Mapping.update x1 True env) b1) 
                (reduce (Mapping.update x1 False env) b2))
  \<le> 1 + min (depth (reduce (Mapping.update x1 True env) b1)) 
            (depth (reduce (Mapping.update x1 False env) b2))"
      using depth_mkIF by simp
    moreover have "depth (reduce (Mapping.update x1 True env) b1) \<le> depth b1"
      using IF.IH (1) by simp
    moreover have "depth (reduce (Mapping.update x1 True env) b2) \<le> depth b2"
      using IF.IH (2) by simp
    ultimately
    have "depth (reduce env (IF x1 b1 b2)) \<le> 1 + min (depth b1) (depth b2)"
      by (smt (verit, ccfv_SIG) IF.IH(2) dual_order.trans min_def not_less_eq_eq plus_1_eq_Suc trans_le_add2)
    thus ?thesis using rhs by simp






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