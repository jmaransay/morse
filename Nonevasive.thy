
theory Nonevasive
  imports
    "BDT"
begin

function nonevasive :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> nonevasive V K = False"
  | "V = {x} \<Longrightarrow> K = {} \<Longrightarrow> nonevasive V K = True"
  | "V = {x} \<Longrightarrow> K = {{},{x}} \<Longrightarrow> nonevasive V K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> nonevasive V K = False"
  (*This can be proven from the definition: | "2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> nonevasive V K = True"*)
  | "2 \<le> card V \<Longrightarrow> nonevasive V K =
    (\<exists>x\<in>V. nonevasive (V - {x}) (link_ext x V K) \<and> nonevasive (V - {x}) (cost x V K))"
  | "\<not> finite V \<Longrightarrow> nonevasive V K = False"
proof -
  fix P :: "bool" and x :: "(nat set \<times> nat set set)"
  assume ee: "(\<And>V K. V = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and se: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and sc: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)" 
      and sn: "(\<And>V xa K. V = {xa} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and en2: "(\<And>V K. 2 \<le> card V \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
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
      show P using ee True by (metis eq_fst_iff)
      next
      case False
      note vne = False
      show P
      proof (cases "card (fst x) = 1")
        case True then obtain xa where f: "fst x = {xa}" by (rule card_1_singletonE)
        show P
        proof (cases "snd x = {}")
          case True
          show P
            by (rule se [of "fst x" xa "snd x"], intro f, intro True) simp
          next
          case False note kne = False
          show P
          proof (cases "snd x = {{},{xa}}")
            case True
            show P
              by (rule sc [of "fst x" xa "snd x"], intro f, intro True) simp
          next
            case False
            show P
              by (rule sn [of "fst x" xa "snd x"], intro f, intro kne, intro False) simp
          qed
        qed
      next
        case False
        have card2: "2 \<le> card (fst x)" using finitex vne False
          by (metis One_nat_def Suc_1 card_gt_0_iff le_SucE not_less not_less_eq_eq)
        show P using en2 [of "fst x" "snd x"] card2 False by simp
         qed
      qed
    qed
qed (auto)
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  show "wf (measure (\<lambda>(V, K). card V))" by simp
  fix V :: "nat set" and K :: "nat set set" and x :: "nat"
  assume c: "2 \<le> card V" and x: "x \<in> V"
  show "((V - {x}, cost x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c  x by simp
  show "((V - {x}, link_ext x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c  x by simp
qed

lemma v_ge_2: assumes two: "2 \<le> card V" shows "nonevasive V {}"
  using two proof (induct "card V" arbitrary: V)
  case 0
  fix V :: "nat set"
  assume "0 = card V" and "2 \<le> card V"
  hence False by linarith
  thus "nonevasive V {}" by fast
next
  case (Suc n)
  assume two: "2 \<le> card V"
  then obtain x where x: "x \<in> V" by fastforce
  have n: "nonevasive (V - {x}) {}"
  proof (cases "2 \<le> card (V - {x})")
    case True
    show ?thesis
    proof (rule Suc.hyps (1))
      show "n = card (V - {x})" using Suc.hyps (2) using x by simp
      show "2 \<le> card (V - {x})" using True .
    qed
  next
    case False hence "card (V - {x}) = 1" using x two Suc.hyps (2) by simp
    then obtain y where V: "V - {x} = {y}" using card_1_singletonE by auto
    show ?thesis unfolding V using nonevasive.simps (2) by simp
  qed
  show "nonevasive V {}"
    unfolding nonevasive.simps (5) [OF two, of "{}"]
    using two link_ext_empty [of _ V] cost_empty [of _ V] n x by auto
qed

lemma assumes "V \<noteq> {}"  and f: "finite V" shows "nonevasive V {}"
  using v_ge_2 nonevasive.simps (2) f
  by (metis Suc_leI assms(1) card_1_singleton_iff card_gt_0_iff nle_le not_less_eq_eq numerals(2))

lemma nonevasiveI1:
  assumes v: "V = {x}" and k: "K = {{},{x}}"
  shows "nonevasive V K"
  using nonevasive.simps (3) [OF v k] by fast

lemma nonevasiveI2:
  assumes v: "2 \<le> card V" and kne: "K \<noteq> {}"
    and k: "(\<exists>x\<in>V. nonevasive (V - {x}) (link_ext x V K) \<and> nonevasive (V - {x}) (cost x V K))"
  shows "nonevasive V K"
  unfolding nonevasive.simps (5) [OF v] using k .

lemma assumes c: "cone {x} K" shows "K = {{x},{}} \<or> K = {}"
  using c unfolding cone_def powerset_def by (cases "K = {}", auto)

lemma cone_nonevasive: 
  assumes f: "finite V" and c: "cone V K" shows "nonevasive V K"
using c f proof (induct "card V" arbitrary: V K)
   case 0
   from "0.hyps" and finite have "V = {}" by (simp add: "0.prems"(2))
   then have False using "0.prems" (1) unfolding cone_def by simp 
   thus ?case by (rule ccontr)
 next
   case (Suc n)
   from `cone V K` obtain x T
     where K: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" and T: "T \<subseteq> powerset (V - {x})" 
       and x: "x \<in> V" unfolding cone_def by auto
   show ?case
   proof (cases "n = 0")
     case True
     hence "card V = 1" using Suc.hyps (2) by simp
     hence v: "V = {x}" using x using card_1_singletonE [OF `card V = 1`] by auto
     hence t: "T = {{}} \<or> T = {}" using T unfolding powerset_def by auto
     show ?thesis
     proof (cases "T = {}")
       case True
       show ?thesis unfolding v K True using nonevasive.simps (2) by simp
     next
       case False note tne = False
       show ?thesis
       proof (cases "T = {{}}")
        case True
        show ?thesis unfolding v K True using nonevasive.simps (3)
          by (simp add: insert_commute)
       next
        case False with tne and t have False by simp
        thus ?thesis by (rule ccontr)
       qed
     qed
   next
    case False
    hence "2 \<le> Suc n" by simp
    hence two: "2 \<le> card V" using Suc.hyps (2) by simp
    from two obtain y where y: "y \<in> V" and ynex: "y \<noteq> x" and xvy: "x \<in> V - {y}"
      using x Suc.prems (2)
      by (metis card_le_Suc0_iff_eq insertE insert_Diff not_less_eq_eq numeral_2_eq_2)
    have lp: "link_ext y (V - {x}) T \<subseteq> powerset (V - {y} - {x})"
      using T unfolding link_ext_def powerset_def by auto
    have cp: "cost y (V - {x}) T \<subseteq> powerset (V - {y} - {x})"
      using T unfolding cost_def powerset_def by auto
    show ?thesis unfolding nonevasive.simps (5) [OF two]
    proof (rule bexI [OF _ y], rule conjI)
      show "nonevasive (V - {y}) (link_ext y V K)"
      proof (rule Suc.hyps(1))
        show "n = card (V - {y})" using y Suc.hyps (2) by simp
        show "cone (V - {y}) (link_ext y V K)"
          unfolding link_ext_cone_eq [OF x ynex [symmetric] T K]
          unfolding cone_def
          by (rule bexI [OF _ xvy], rule exI [of _ "link_ext y (V - {x}) T"], rule conjI) 
            (intro lp, fast)
        show "finite (V - {y})" using `finite V` by fast
      qed
      show "nonevasive (V - {y}) (cost y V K)"
      proof (rule Suc.hyps(1))
        show "n = card (V - {y})" using y Suc.hyps (2) by simp
        show "cone (V - {y}) (cost y V K)"
          unfolding cost_cone_eq [OF x ynex [symmetric] T K]
          unfolding cone_def
          by (rule bexI [OF _ xvy], rule exI [of _ "cost y (V - {x}) T"], rule conjI)
            (intro cp, fast)
        show "finite (V - {y})" using `finite V` by fast
      qed
    qed
  qed
qed

lemma
  zerocollapsible__nonevasive:
  assumes f: "finite V" and z: "zero_collapsible V K" shows "nonevasive V K"
using z f proof (induct "card V" arbitrary: V K)
   case 0
   from "0.hyps" and finite have "V = {}" by (simp add: "0.prems"(2))
   then have False using "0.prems" (1) unfolding cone_def by simp 
   thus ?case by (rule ccontr)
 next
   case (Suc n)
   (*from `cone V K` obtain x T
     where K: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" and T: "T \<subseteq> powerset (V - {x})" 
       and x: "x \<in> V" unfolding cone_def by auto*)
   show ?case
   proof (cases "n = 0")
     case True
     hence "card V = 1" using Suc.hyps (2) by simp
     then obtain x where v: "V = {x}" using card_1_singletonE [OF `card V = 1`] by auto
     show ?thesis
     proof (cases "K = {}")
       case True
       show ?thesis unfolding v True using nonevasive.simps (2) by simp
     next
       case False note tne = False
       show ?thesis
       proof (cases "K = {{}, {x}}")
        case True
        show ?thesis unfolding v True using nonevasive.simps (3)
          by (simp add: insert_commute)
       next
         case False 
         have False using zero_collapsible.simps (4) [OF v tne False] 
           using Suc.prems (1) by simp
         thus ?thesis by (rule ccontr)
       qed
     qed
   next
    case False
    hence "2 \<le> Suc n" by simp
    hence two: "2 \<le> card V" using Suc.hyps (2) by simp
    obtain x where x: "x \<in> V" and cl: "cone (V - {x}) (link_ext x V K)" 
      and ccc: "zero_collapsible (V - {x}) (cost x V K)" and xxne: "V - {x} \<noteq> {}"
      using zero_collapsible.simps (5) [OF two, of K]
      by (metis Suc.prems(1) zero_collapsible.simps(1))
    show ?thesis
    proof (unfold nonevasive.simps (5) [OF two, of K], rule bexI [OF _ x], rule conjI)
      show "nonevasive (V - {x}) (cost x V K)" 
      proof (rule Suc.hyps)
        show "n = card (V - {x})" using x `Suc n = card V` by simp
        show "zero_collapsible (V - {x}) (cost x V K)" using ccc .
        show "finite (V - {x})" using `finite V` by simp
      qed
      show "nonevasive (V - {x}) (link_ext x V K)"
      proof (rule cone_nonevasive)
        show "finite (V - {x})" using `finite V` by simp
        show "cone (V - {x}) (link_ext x V K)" using cl .
      qed
    qed
  qed
qed

end