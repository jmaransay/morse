
theory Nonevasive
  imports
    "BDT"
begin

function nonevasive :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> nonevasive V K = False"
  | "V = {x} \<Longrightarrow> K = {{},{x}} \<Longrightarrow> nonevasive V K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> nonevasive V K = False"
  | "2 \<le> card V \<Longrightarrow> nonevasive V K =
    (\<exists>x\<in>V. nonevasive (V - {x}) (link_ext x V K) \<and> nonevasive (V - {x}) (cost x V K))"
  | "\<not> finite V \<Longrightarrow> nonevasive V K = False"
  unfolding link_ext_def cost_def
proof -
  fix P :: "bool" and x :: "(nat set \<times> nat set set)"
  assume ee: "(\<And>V K. V = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and ene: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)" 
      and se: "(\<And>V xa K. V = {xa} \<Longrightarrow> K \<noteq> {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and sc: "(\<And>V K. 2 \<le> card V \<Longrightarrow> x = (V, K) \<Longrightarrow> P)" 
      and inf: "(\<And>V K. infinite V \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
  show P
  proof (cases "finite (fst x)")
    case False
    show P
      by (rule inf [of "fst x" "snd x"], intro False) auto
  next
    case True note finitex = True
    show P
    proof (cases "fst x = {}")
      case True note ve = True
      show P using ee ve
        by (metis eq_fst_iff)
      next
        case False
        note vne = False
      show P
      proof (cases "card (fst x) = 1")
        case True then obtain xa where f: "fst x = {xa}" by (rule card_1_singletonE)
        show P
        proof (cases "snd x = {{xa},{}}")
          case True
          show P
            by (metis True ene f insert_commute prod.collapse)            
          next
          case False note kne = False
          show P
            by (metis f insert_commute kne prod.collapse se)
        qed
      next
        case False
        have card2: "2 \<le> card (fst x)" using finitex vne False
          by (metis One_nat_def Suc_1 card_gt_0_iff le_SucE not_less not_less_eq_eq)
        show P by (metis card2 prod.collapse sc)
        qed
      qed
    qed
qed (auto)
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  show "wf (measure (\<lambda>(V, K). card V))" by simp
  fix V :: "nat set" and K :: "nat set set" and x :: "nat"
  assume c: "2 \<le> card V" and x: "x \<in> V"
  show "((V - {x}, cost x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c x by simp
  show "((V - {x}, link_ext x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c x by simp
qed

lemma nonevasiveI1:
  assumes v: "V = {x}" and k: "K = {{},{x}}"
  shows "nonevasive V K"
  using nonevasive.simps (2) [OF v k] by fast

lemma nonevasiveI2:
  assumes v: "2 \<le> card V" 
    and k: "(\<exists>x\<in>V. nonevasive (V - {x}) (link_ext x V K) \<and> nonevasive (V - {x}) (cost x V K))"
  shows "nonevasive V K"
  unfolding nonevasive.simps (4) [OF v, of K] using k .

lemma assumes c: "cone {x} K" shows "K = {{x},{}} \<or> K = {}"
  using c unfolding cone_def powerset_def by (cases "K = {}", auto)

lemma assumes c: "cone V K" shows "nonevasive V K"
using c proof (cases "finite V")
  case True note finite = True
  assume c: "cone V K"
  show ?thesis
    using c finite proof (induct "card V" arbitrary: V K)
    case 0
    from "0.hyps" and finite have "V = {}" by (simp add: "0.prems"(2))
    then have False using "0.prems" (1) unfolding cone_def by simp 
    thus ?case by (rule ccontr)
  next
    case (Suc n)
    from Suc.prems and Suc.hyps (2) obtain x T
      where K: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" and T: "T \<subseteq> powerset (V - {x})"
      unfolding cone_def by auto
    show ?case using Suc.prems Suc.hyps (1,2)
    proof (cases n)
      case 0 then obtain y where v: "V = {y}"
        using Suc.hyps(2) card_1_singletonE by auto
      show ?thesis apply (rule nonevasiveI1 [of _ y]) apply (rule v)
        using v K T apply (cases "x = y") apply auto
        using powerset_def apply auto try
        
      unfolding K proof (intro nonevasiveI2)
    then show ?case sorry
next
  case (Suc x)
  then show ?case sorry
qed

  sorry

lemma assumes "zero_collapsible V K" shows "nonevasive V K"
  sorry


end