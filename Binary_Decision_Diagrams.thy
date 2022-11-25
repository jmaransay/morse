
theory Binary_Decision_Diagrams
  imports
    Main
    "Boolean_Expression_Checkers.Boolean_Expression_Checkers"
begin


fun depth :: "'a ifex \<Rightarrow> nat"
  where
    "depth Trueif = 0" | "depth Falseif = 0" |
    "depth (IF b f t) = 1 + min (depth f) (depth t)"

lemma depth_mkIF: "depth (mkIF x t1 t2) \<le> Suc (max (depth t1) (depth t2))"
  unfolding mkIF_def by auto

lemma "depth (reduce env b) \<le> depth b"
proof (induct b arbitrary: env)
  case Trueif
  show ?case by simp
next
  case Falseif
  show ?case by simp
next
  case (IF x1 b1 b2)
  show ?case
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
        show ?thesis unfolding reduce.simps Some using b using db2 try

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

primrec valif :: "ifex => (nat => bool) => bool"
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