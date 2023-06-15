
theory Nonevasive
  imports
    "BDT"
begin

section\<open>Definition of \emph{non-evasive}\<close>

function non_evasive :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> non_evasive V K = False"
  | "V = {x} \<Longrightarrow> K = {} \<Longrightarrow> non_evasive V K = True"
  | "V = {x} \<Longrightarrow> K = {{},{x}} \<Longrightarrow> non_evasive V K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> non_evasive V K = False"
  (*This can be proven from the definition: | "2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> non_evasive V K = True"*)
  | "2 \<le> card V \<Longrightarrow> non_evasive V K =
    (\<exists>x\<in>V. non_evasive (V - {x}) (link_ext x V K) \<and> non_evasive (V - {x}) (cost x V K))"
  | "\<not> finite V \<Longrightarrow> non_evasive V K = False"
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

lemma v_ge_2: assumes two: "2 \<le> card V" shows "non_evasive V {}"
  using two proof (induct "card V" arbitrary: V)
  case 0
  fix V :: "nat set"
  assume "0 = card V" and "2 \<le> card V"
  hence False by linarith
  thus "non_evasive V {}" by fast
next
  case (Suc n)
  assume two: "2 \<le> card V"
  then obtain x where x: "x \<in> V" by fastforce
  have n: "non_evasive (V - {x}) {}"
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
    show ?thesis unfolding V using non_evasive.simps (2) by simp
  qed
  show "non_evasive V {}"
    unfolding non_evasive.simps (5) [OF two, of "{}"]
    using two link_ext_empty [of _ V] cost_empty [of _ V] n x by auto
qed

lemma assumes "V \<noteq> {}"  and f: "finite V" shows "non_evasive V {}"
  using v_ge_2 non_evasive.simps (2) f
  by (metis Suc_leI assms(1) card_1_singleton_iff card_gt_0_iff nle_le not_less_eq_eq numerals(2))

lemma non_evasiveI1:
  assumes v: "V = {x}" and k: "K = {{},{x}}"
  shows "non_evasive V K"
  using non_evasive.simps (3) [OF v k] by fast

lemma non_evasiveI2:
  assumes v: "2 \<le> card V" and kne: "K \<noteq> {}"
    and k: "(\<exists>x\<in>V. non_evasive (V - {x}) (link_ext x V K) \<and> non_evasive (V - {x}) (cost x V K))"
  shows "non_evasive V K"
  unfolding non_evasive.simps (5) [OF v] using k .

lemma assumes c: "cone {x} K" shows "K = {{x},{}} \<or> K = {}"
  using c unfolding cone_def powerset_def by (cases "K = {}", auto)

section\<open>Cone implies \emph{non-evasive}.\<close>

theorem cone_non_evasive:
  assumes f: "finite V" and c: "cone V K" shows "non_evasive V K"
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
       show ?thesis unfolding v K True using non_evasive.simps (2) by simp
     next
       case False note tne = False
       show ?thesis
       proof (cases "T = {{}}")
        case True
        show ?thesis unfolding v K True using non_evasive.simps (3)
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
    show ?thesis unfolding non_evasive.simps (5) [OF two]
    proof (rule bexI [OF _ y], rule conjI)
      show "non_evasive (V - {y}) (link_ext y V K)"
      proof (rule Suc.hyps(1))
        show "n = card (V - {y})" using y Suc.hyps (2) by simp
        show "cone (V - {y}) (link_ext y V K)"
          unfolding link_ext_cone_eq [OF x ynex [symmetric] T K]
          unfolding cone_def
          by (rule bexI [OF _ xvy], rule exI [of _ "link_ext y (V - {x}) T"], rule conjI) 
            (intro lp, fast)
        show "finite (V - {y})" using `finite V` by fast
      qed
      show "non_evasive (V - {y}) (cost y V K)"
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

section\<open>\emph{Zero-collapsible} implies \emph{non-evasive}.\<close>

theorem zerocollapsible__non_evasive:
  assumes f: "finite V" and z: "zero_collapsible V K" shows "non_evasive V K"
using z f proof (induct "card V" arbitrary: V K)
   case 0
   from "0.hyps" and finite have "V = {}" by (simp add: "0.prems"(2))
   then have False using "0.prems" (1) unfolding cone_def by simp 
   thus ?case by (rule ccontr)
 next
   case (Suc n)
   show ?case
   proof (cases "n = 0")
     case True
     hence "card V = 1" using Suc.hyps (2) by simp
     then obtain x where v: "V = {x}" using card_1_singletonE [OF `card V = 1`] by auto
     show ?thesis
     proof (cases "K = {}")
       case True
       show ?thesis unfolding v True using non_evasive.simps (2) by simp
     next
       case False note tne = False
       show ?thesis
       proof (cases "K = {{}, {x}}")
        case True
        show ?thesis unfolding v True using non_evasive.simps (3)
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
    proof (unfold non_evasive.simps (5) [OF two, of K], rule bexI [OF _ x], rule conjI)
      show "non_evasive (V - {x}) (cost x V K)" 
      proof (rule Suc.hyps)
        show "n = card (V - {x})" using x `Suc n = card V` by simp
        show "zero_collapsible (V - {x}) (cost x V K)" using ccc .
        show "finite (V - {x})" using `finite V` by simp
      qed
      show "non_evasive (V - {x}) (link_ext x V K)"
      proof (rule cone_non_evasive)
        show "finite (V - {x})" using `finite V` by simp
        show "cone (V - {x}) (link_ext x V K)" using cl .
      qed
    qed
  qed
qed

section\<open>\emph{No evaders} implies \emph{non-evasive}.\<close>

subsection\<open>Previous results.\<close>

lemma sorted_variables_remove:
  assumes vl: "(V, l) \<in> sorted_variables" and x: "x \<in> V" and f: "finite V"
  shows "(V - {x}, remove1 x l) \<in> sorted_variables"
  using vl x f proof (induct "card V" arbitrary: V l)
  case 0 from "0.hyps" "0.prems" (3) have "V = {}" by simp
  with "0.prems" (2) have False by fast
  thus "(V - {x}, remove1 x l) \<in> sorted_variables" by (rule ccontr)
next
  case (Suc n)
  from Suc.prems (1) obtain A l' y where v: "V = insert y A" and l: "l = y # l'" 
      and al: "(A, l') \<in> sorted_variables" and y: "y \<notin> A"
    using sorted_variables.simps [of V l] using `x \<in> V` by auto
  show "(V - {x}, remove1 x l) \<in> sorted_variables"
  proof (cases "V - {x} = {}")
    case True hence v: "V = {x}" using `x \<in> V` by auto hence l: "l = [x]"
      using \<open>(V, l) \<in> sorted_variables\<close> \<open>V = insert y A\<close> \<open>l = y # l'\<close> 
      using sorted_variables_length_coherent by fastforce
    show ?thesis unfolding v l
      by (simp add: sorted_variables.intros(1))
  next
    case False note vxne = False
    show ?thesis
    proof (cases "x = y")
      case True
      show ?thesis unfolding True unfolding v l using al y by simp
    next
      case False
      have yax: "y \<notin> A - {x}" using False \<open>V = insert y A\<close> using y by blast
      have vx: "V - {x} = insert y (A - {x})" using \<open>V = insert y A\<close> y False by auto
      have rxl: "remove1 x l = y # (remove1 x l')" using \<open>l = y # l'\<close> False by simp
      have axr: "(A - {x}, remove1 x l') \<in> sorted_variables"
      proof (rule Suc.hyps (1))
        show "n = card A" using \<open>V = insert y A\<close> y \<open>Suc n = card V\<close> `finite V`
          by auto
        show "(A, l') \<in> sorted_variables" by (rule al)
        show "x \<in> A" using `x \<in> V` \<open>V = insert y A\<close> y False by simp
        show "finite A" using `finite V` \<open>V = insert y A\<close> by simp
      qed
      show ?thesis unfolding vx rxl
        by (intro sorted_variables.intros (2), rule axr, rule yax)
    qed
  qed
qed

lemma length_evaluation: "length (evaluation l K) = 2^(length l)"
proof (induct l arbitrary: K)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case 
    unfolding evaluation.simps 
    unfolding length_append 
    unfolding Cons.hyps [of "link_ext a (set (a # l)) K"]
    unfolding Cons.hyps [of "cost a (set (a # l)) K"] by simp
qed

lemma evaluation_link_ext_depth_0:
  assumes v: "(V, l) \<in> sorted_variables" and l: "1 \<le> length l"
  shows "take (2^(length l - 1)) (evaluation l K) = evaluation (tl l) (link_ext (hd l) V K)"
proof (cases l)
  case Nil
  have False using Nil l by auto
  thus ?thesis by (rule ccontr)
next
  case (Cons x l)
  note l = Cons
  show ?thesis
  proof (cases "l = []")
    case True
    have v: "V = {x}" using v unfolding l True using sorted_variables.intros
      by (metis list.simps(15) sorted_variables_coherent)
    then show ?thesis unfolding True v l by auto
  next
    case False
    have s: "set (x # l) = V" 
      using sorted_variables_coherent [symmetric, OF v] unfolding l .
    show ?thesis
      unfolding evaluation.simps l list.sel (1,3)
      unfolding s
      using length_evaluation by simp
  qed
qed

lemma evaluation_cost_depth_0:
  assumes v: "(V, l) \<in> sorted_variables"
    and l: "1 \<le> length l"
  shows "drop (2^(length l - 1)) (evaluation l K) = evaluation (tl l) (cost (hd l) V K)"
proof (cases l)
  case Nil
  have False using Nil l by auto
  thus ?thesis by (rule ccontr)
next
  case (Cons x l)
  note l = Cons
  show ?thesis
  proof (cases "l = []")
    case True
    have v: "V = {x}" using v unfolding l True using sorted_variables.intros
      by (metis list.simps(15) sorted_variables_coherent)
    then show ?thesis unfolding True v l by auto
  next
    case False
    have s: "set (x # l) = V" 
      using sorted_variables_coherent [symmetric, OF v] unfolding l .
    show ?thesis
      unfolding evaluation.simps l list.sel (1,3)
      unfolding s
      using length_evaluation by simp
  qed
qed

subsection\<open>The @{term link_ext} of a variable \emph{wrt.} an evaluation list.}\<close>

function take_link_ext :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "take_link_ext n [] = []"
  | "take_link_ext 0 l = l"
  | "l \<noteq> [] \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> take_link_ext n l = (take n l) @ (take_link_ext n (drop n (drop n l)))"
by (auto+)
termination
  by (relation "measure(\<lambda>(n,l). n + length l)") (simp+)

(*TODO: take_link_ext fails with 'value', but works with the simplifier;
  the last rule in the definition is not an equation*)

lemma "take_link_ext 1 [0::int,1,2,3,4,5,6,7] = [0,2,4,6]" by simp

lemma "take_link_ext 2 [0::int,1,2,3,4,5,6,7] = [0,1,4,5]" by simp

lemma "take_link_ext 4 [0::int,1,2,3,4,5,6,7] = [0,1,2,3]" by simp

lemma take_link_ext_take:
  assumes l: "length l = 2 * n" shows "take_link_ext n l = take n l"
proof (cases "n = 0")
  case True
  show ?thesis using True l by auto
next
  case False note ng0 = False
  show ?thesis
  proof (cases "l = []")
    case True
    then show ?thesis unfolding True by simp
  next
    case False
    then show ?thesis 
      unfolding take_link_ext.simps (3) [OF False ng0]
      using l by simp
  qed
qed

lemma length_take_link_ext_2:
  assumes l: "length l = 2 * n"
  shows "length (take_link_ext n l) = n" 
  unfolding take_link_ext_take [OF l] by (simp add: l)

lemma assumes l: "length l = k" and i: "i + j = k"
  shows "\<exists>m m'. l = m @ m' \<and> length m = i \<and> length m' = j"
  apply (rule exI [of _ "take i l"], rule exI [of _ "drop i l"], rule conjI, simp)
  using i l by force

lemma take_link_ext_append:
  assumes ll: "length l = (2 * k) * n" and ll': "length l' = (2 * k') * n"
  shows "take_link_ext n (l @ l') = take_link_ext n l @ take_link_ext n l'"
using ll ll' proof (induct k arbitrary: l l')
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "n = 0")
    case True
    show ?thesis unfolding True by simp
  next
    case False
    have lne: "l \<noteq> []" using False Suc.prems(1) by fastforce
    define l2 where "l2 = take (2 * n) l"
    define l3 where "l3 = drop (2 * n) l"
    have l_append: "l = l2 @ l3" using l2_def l3_def by simp
    have l2l3l'ne: "(l2 @ l3) @ l' \<noteq> []" using lne l2_def l3_def by simp
    have ll2: "length l2 = 2 * n"
      using l2_def l_append Suc.prems (1) by fastforce
    have ll3: "length l3 = 2 * k * n"
      using l3_def l_append Suc.prems (1) by fastforce
    have t: "take_link_ext n l = (take n l2) @ (take_link_ext n l3)"
      unfolding take_link_ext.simps (3) [OF lne False]
      unfolding l_append
      by (metis append_same_eq append_take_drop_id drop_drop l3_def l_append mult.commute mult_2_right take_add take_drop)
    have tl2l3l': "take n ((l2 @ l3) @ l') = take n l2" using l2_def
      using ll2 by fastforce
    have tl2l3: "take n (l2 @ l3) = take n l2" using l2_def
      using ll2 by fastforce
    have ddl2l3l': "drop n (drop n ((l2 @ l3) @ l')) = l3 @ l'" using ll2 by simp
    have ddl2l3: "drop n (drop n (l2 @ l3)) = l3" using ll2 by simp
    have hyp: "take_link_ext n (l3 @ l') = take_link_ext n l3 @ take_link_ext n l'"
      by (rule Suc.hyps, intro ll3, intro Suc.prems (2))
    show ?thesis
      apply (subst l_append) 
      apply (subst take_link_ext.simps (3) [OF l2l3l'ne False])
      apply (subst take_link_ext.simps (3) [OF lne False])
      unfolding l_append unfolding tl2l3l' tl2l3 ddl2l3l' ddl2l3 
      apply (subst append_assoc)
      apply (subst hyp) ..
  qed
qed

lemma "take_link_ext 1 ([a\<^sub>1, a\<^sub>1, a\<^sub>1] @ [a\<^sub>1, a\<^sub>1, a\<^sub>1]) = ([a\<^sub>1, a\<^sub>1, a\<^sub>1])" by simp

lemma "take_link_ext 1 [a\<^sub>1, a\<^sub>1, a\<^sub>1] = ([a\<^sub>1, a\<^sub>1])" by simp

lemma "take_link_ext 1 [a\<^sub>1, a\<^sub>1, a\<^sub>1] @ take_link_ext 1 [a\<^sub>1, a\<^sub>1, a\<^sub>1] = ([a\<^sub>1, a\<^sub>1, a\<^sub>1, a\<^sub>1])" by simp

lemma take_link_ext_power_append:
  assumes k: "k < m" and lm: "length l = 2^m" and lm': "length l' = 2^m"
  shows "take_link_ext (2^k) (l @ l') = take_link_ext (2^k) l @ take_link_ext (2^k) l'"
proof(rule take_link_ext_append [of _ "2^(m-k-1)" _ _ "2^(m-k-1)"])
  show "length l = 2 * 2 ^ (m - k - 1) * 2 ^ k"
    using lm k
    by (metis Groups.mult_ac(2) add_diff_inverse_nat less_or_eq_imp_le not_less power_add power_minus_mult zero_less_diff)
  show "length l' = 2 * 2 ^ (m - k - 1) * 2 ^ k"
    using lm' k
    by (metis Groups.mult_ac(2) add_diff_inverse_nat less_or_eq_imp_le not_less power_add power_minus_mult zero_less_diff)
qed

lemma remove1_head: "remove1 x (x # l) = l" by simp

lemma remove1_reduce:
  assumes n: "n \<noteq> 0" and n': "n < length (x # l)" and d: "distinct (x # l)"
  shows "remove1 ((x # l) ! n) (x # l) = x # (remove1 (l ! (n - 1)) l)"
  using remove1.simps n d n' by auto

lemma nth_not_zero: assumes "n \<noteq> 0" shows "(x # l) ! n = l ! (n - 1)"
  using assms(1) by auto

text\<open>The case where @{term "n = 0"} is later used in the proof 
  of the general case for @{term "n"}.\<close>

lemma evaluation_nth_0_link_ext:
  assumes v: "(V, l) \<in> sorted_variables" and l: "0 < length l"
  shows "take_link_ext (2^((length l - 1) - 0)) (evaluation l K) =
          evaluation (remove1 (nth l 0) l) (link_ext (nth l 0) V K)"
proof -
  have one_l: "1 \<le> length l" using l by linarith
  have tlt: "take_link_ext (2^((length l - 1) - 0)) (evaluation l K) =
    take (2^((length l - 1) - 0)) (evaluation l K)"
    by (metis bot_nat_0.not_eq_extremum diff_zero l length_evaluation power_eq_if take_link_ext_take)
  have r: "remove1 (nth l 0) l = tl l" using l
    by (metis length_greater_0_conv list.exhaust list.sel(3) nth_Cons_0 remove1_head)
  have n: "nth l 0 = hd l" using l by (simp add: hd_conv_nth)
  show ?thesis unfolding tlt r unfolding n
    using evaluation_link_ext_depth_0 [OF v one_l] by simp
qed

lemma evaluation_nth_link_ext:
  assumes v: "(V, l) \<in> sorted_variables" and l: "n < length l"
  shows "take_link_ext (2^((length l - 1) - n)) (evaluation l K) =
          evaluation (remove1 (nth l n) l) (link_ext (nth l n) V K)"
proof (cases "n = 0")
  case True
  show ?thesis using evaluation_nth_0_link_ext [OF v] True l by simp
next
  case False
  show ?thesis
  using v l False proof (induction l arbitrary: n V K rule: list.induct)
  case Nil
  have False using Nil.prems (2) by simp
  thus ?case by (rule ccontr)
next
  case (Cons x l)
  have lrw: "length (x # l) - 1 - n = length l - 1 - (n - 1)"
    using Cons.prems(3) by auto
  have set_rw: "set (x # remove1 (l ! (n - 1)) l) = V - {l ! (n - 1)}"
    using Cons.prems (1)
    by (metis Cons.prems(2) Cons.prems(3) nth_not_zero remove1_reduce set_remove1_eq sorted_variables_coherent sorted_variables_distinct)
  (*This is probably the key step in the proof, since the "link" commutes we can 
    later rewrite the thesis to apply the induction hypothesis:*)
  have link_ext_x_l: "link_ext x (V - {l ! (n - 1)}) (link_ext (l ! (n - 1)) V K)
    = link_ext (l ! (n - 1)) (V - {x}) (link_ext x V K)"
  proof (rule link_ext_commute)
    show "l ! (n - 1) \<in> V" and "x \<in> V" using Cons.prems (1,2,3)
      using sorted_variables_coherent by force+
  qed
  have take_link_ext_link: "take_link_ext (2 ^ (length l - 1 - (n - 1)))
     (evaluation l (link_ext x (set (x # l)) K)) =
    evaluation (remove1 (l ! (n - 1)) l)
     (link_ext x (set (x # remove1 (l ! (n - 1)) l)) (link_ext (l ! (n - 1)) V K))"
    unfolding sorted_variables_coherent [symmetric, OF Cons.prems(1)]
    unfolding set_rw
    unfolding link_ext_x_l
  proof (cases "n = 1")
    case False
    show "take_link_ext (2 ^ (length l - 1 - (n - 1))) (evaluation l (link_ext x V K)) =
      evaluation (remove1 (l ! (n - 1)) l) (link_ext (l ! (n - 1)) (V - {x}) (link_ext x V K))"
    proof (rule Cons (1))
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "n - 1 < length l" using Cons.prems (2,3) by simp
      show "n - 1 \<noteq> 0" using False Cons.prems (3) by simp
    qed
  next
    case True
    have one: "1 - 1 = (0::nat)" by linarith
    show "take_link_ext (2 ^ (length l - 1 - (n - 1))) (evaluation l (link_ext x V K)) =
      evaluation (remove1 (l ! (n - 1)) l) (link_ext (l ! (n - 1)) (V - {x}) (link_ext x V K))"
      unfolding True one  
    proof (rule evaluation_nth_0_link_ext)
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "0 < length l" using Cons.prems (2,3) True by auto
    qed
  qed
  (*This is probably the key step in the proof, since the "link" commutes with "cost"
  we can later rewrite the thesis to apply the induction hypothesis:*)
  have link_ext_cost_x_l: "cost x (V - {l ! (n - 1)}) (link_ext (l ! (n - 1)) V K)
    = link_ext (l ! (n - 1)) (V - {x}) (cost x V K)"
  proof (rule link_ext_cost_commute [symmetric])
    show "l ! (n - 1) \<in> V" and "x \<in> V" using Cons.prems (1,2,3)
      using sorted_variables_coherent by force+
    show "x \<noteq> l ! (n - 1)" using sorted_variables_distinct [OF Cons.prems (1)]
      using Cons.prems(2) Cons.prems(3) by auto
  qed
  have take_link_ext_cost: "take_link_ext (2 ^ (length l - 1 - (n - 1)))
     (evaluation l (cost x (set (x # l)) K)) =
    evaluation (remove1 (l ! (n - 1)) l)
     (cost x (set (x # remove1 (l ! (n - 1)) l)) (link_ext (l ! (n - 1)) V K))"
    unfolding sorted_variables_coherent [symmetric, OF Cons.prems(1)]
    unfolding set_rw
    unfolding link_ext_cost_x_l
  proof (cases "n = 1")
  case False
  show "take_link_ext (2 ^ (length l - 1 - (n - 1))) (evaluation l (cost x V K)) =
      evaluation (remove1 (l ! (n - 1)) l) (link_ext (l ! (n - 1)) (V - {x}) (cost x V K))"
    proof (rule Cons (1))
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "n - 1 < length l" using Cons.prems (2,3) by simp
      show "n - 1 \<noteq> 0" using False Cons.prems (3) by simp
    qed
  next
    case True
    have one: "1 - 1 = (0::nat)" by linarith
    show "take_link_ext (2 ^ (length l - 1 - (n - 1))) (evaluation l (cost x V K)) =
      evaluation (remove1 (l ! (n - 1)) l) (link_ext (l ! (n - 1)) (V - {x}) (cost x V K))"
      unfolding True one  
    proof (rule evaluation_nth_0_link_ext)
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "0 < length l" using Cons.prems (2,3) True by auto
    qed
  qed
  show ?case
    unfolding evaluation.simps 
    unfolding remove1_reduce [OF Cons.prems (3) Cons.prems (2) sorted_variables_distinct [OF Cons.prems (1)]]
    unfolding nth_not_zero [OF Cons.prems (3)]
    unfolding evaluation.simps unfolding lrw
    unfolding take_link_ext_link [symmetric] take_link_ext_cost [symmetric]
  proof (rule take_link_ext_power_append [of _ "length l"])
    show "length l - 1 - (n - 1) < length l"
      using Cons.prems(2) Cons.prems(3) by force
    show "length (evaluation l (link_ext x (set (x # l)) K)) = 2 ^ length l" 
      and "length (evaluation l (cost x (set (x # l)) K)) = 2 ^ length l"
      by (rule length_evaluation)+
  qed
 qed
qed


subsection\<open>The @{term cost} of a variable \emph{wrt.} an evaluation list.}\<close>

(*TODO: define an intermediate list @{term "drop n l"}*)

function take_cost :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "take_cost n [] = []"
  | "take_cost 0 l = l"
  | "l \<noteq> [] \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> take_cost n l = (take n (drop n l)) @ (take_cost n (drop n (drop n l)))"
by (auto+)
termination
  by (relation "measure(\<lambda>(n,l). n + length l)") (simp+)

(*TODO: take_cost fails with 'value', but works with the simplifier;
  the last rule in the definition is not an equation*)

lemma "take_cost 1 [0::int,1,2,3,4,5,6,7] = [1,3,5,7]" by simp

lemma "take_cost 2 [0::int,1,2,3,4,5,6,7] = [2,3,6,7]" by simp

lemma "take_cost 4 [0::int,1,2,3,4,5,6,7] = [4,5,6,7]" by simp

lemma take_cost_take:
  assumes l: "length l = 2 * n" shows "take_cost n l = take n (drop n l)"
proof (cases "n = 0")
  case True
  show ?thesis using True l by auto
next
  case False note ng0 = False
  show ?thesis
  proof (cases "l = []")
    case True
    then show ?thesis unfolding True by simp
  next
    case False
    then show ?thesis
      unfolding take_cost.simps (3) [OF False ng0]
      using l by simp
  qed
qed

lemma length_take_cost_2:
  assumes l: "length l = 2 * n"
  shows "length (take_cost n l) = n" 
  unfolding take_cost_take [OF l] by (simp add: l)

lemma take_cost_append:
  assumes ll: "length l = (2 * k) * n" and ll': "length l' = (2 * k') * n"
  shows "take_cost n (l @ l') = take_cost n l @ take_cost n l'"
using ll ll' proof (induct k arbitrary: l l')
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "n = 0")
    case True
    show ?thesis unfolding True by simp
  next
    case False
    have lne: "l \<noteq> []" using False Suc.prems(1) by fastforce
    define l2 where "l2 = take (2 * n) l"
    define l3 where "l3 = drop (2 * n) l"
    have l_append: "l = l2 @ l3" using l2_def l3_def by simp
    have l2l3l'ne: "(l2 @ l3) @ l' \<noteq> []" using lne l2_def l3_def by simp
    have ll2: "length l2 = 2 * n"
      using l2_def l_append Suc.prems (1) by fastforce
    have ll3: "length l3 = 2 * k * n"
      using l3_def l_append Suc.prems (1) by fastforce
    have t: "take_cost n l = (take n (drop n l2)) @ (take_cost n l3)"
      unfolding take_cost.simps (3) [OF lne False]
      unfolding l_append by (simp add: ll2)
    have tl2l3l': "take n (drop n ((l2 @ l3) @ l')) = take n (drop n l2)" 
      using l2_def using ll2 by fastforce
    have tl2l3: "take n (drop n (l2 @ l3)) = take n (drop n l2)" using l2_def
      using ll2 by fastforce
    have ddl2l3l': "drop n (drop n ((l2 @ l3) @ l')) = l3 @ l'" using ll2 by simp
    have ddl2l3: "drop n (drop n (l2 @ l3)) = l3" using ll2 by simp
    have hyp: "take_cost n (l3 @ l') = take_cost n l3 @ take_cost n l'"
      by (rule Suc.hyps, intro ll3, intro Suc.prems (2))
    show ?thesis
      apply (subst l_append) 
      apply (subst take_cost.simps (3) [OF l2l3l'ne False])
      apply (subst take_cost.simps (3) [OF lne False])
      unfolding l_append 
      unfolding tl2l3l'
      unfolding tl2l3
      unfolding ddl2l3l' 
      unfolding ddl2l3 
      apply (subst append_assoc)
      apply (subst hyp) ..
  qed
qed

lemma "take_cost 1 ([a\<^sub>1, a\<^sub>1, a\<^sub>1] @ [a\<^sub>1, a\<^sub>1, a\<^sub>1]) = ([a\<^sub>1, a\<^sub>1, a\<^sub>1])" by simp

lemma "take_cost 1 [a\<^sub>1, a\<^sub>1, a\<^sub>1] = ([a\<^sub>1])" by simp

lemma "take_cost 1 [a\<^sub>1, a\<^sub>1, a\<^sub>1] @ take_cost 1 [a\<^sub>1, a\<^sub>1, a\<^sub>1] = ([a\<^sub>1, a\<^sub>1])" by simp

lemma take_cost_power_append:
  assumes k: "k < m" and lm: "length l = 2^m" and lm': "length l' = 2^m"
  shows "take_cost (2^k) (l @ l') = take_cost (2^k) l @ take_cost (2^k) l'"
proof(rule take_cost_append [of _ "2^(m-k-1)" _ _ "2^(m-k-1)"])
  show "length l = 2 * 2 ^ (m - k - 1) * 2 ^ k"
    using lm k
    by (metis Groups.mult_ac(2) add_diff_inverse_nat less_or_eq_imp_le not_less power_add power_minus_mult zero_less_diff)
  show "length l' = 2 * 2 ^ (m - k - 1) * 2 ^ k"
    using lm' k
    by (metis Groups.mult_ac(2) add_diff_inverse_nat less_or_eq_imp_le not_less power_add power_minus_mult zero_less_diff)
qed

text\<open>The case where @{term "n = 0"} is later used in the proof 
  of the general case for @{term "n"}.\<close>

lemma evaluation_nth_0_cost:
  assumes v: "(V, l) \<in> sorted_variables" and l: "0 < length l"
  shows "take_cost (2^((length l - 1) - 0)) (evaluation l K) =
          evaluation (remove1 (nth l 0) l) (cost (nth l 0) V K)"
proof -
  have one_l: "1 \<le> length l" using l by linarith
  have tlt: "take_cost (2^((length l - 1) - 0)) (evaluation l K) =
    take (2^((length l - 1) - 0)) (drop (2^((length l - 1) - 0)) (evaluation l K))"
    by (metis bot_nat_0.not_eq_extremum diff_zero l length_evaluation power_eq_if take_cost_take)
  have r: "remove1 (nth l 0) l = tl l" using l
    by (metis length_greater_0_conv list.exhaust list.sel(3) nth_Cons_0 remove1_head)
  have n: "nth l 0 = hd l" using l by (simp add: hd_conv_nth)
  show ?thesis unfolding tlt r unfolding n
    using evaluation_cost_depth_0 [OF v one_l]
    by (simp add: length_evaluation)
qed

lemma evaluation_nth_cost:
  assumes v: "(V, l) \<in> sorted_variables" and l: "n < length l"
  shows "take_cost (2^((length l - 1) - n)) (evaluation l K) =
          evaluation (remove1 (nth l n) l) (cost (nth l n) V K)"
proof (cases "n = 0")
  case True
  show ?thesis using evaluation_nth_0_cost [OF v] True l by simp
next
  case False
  show ?thesis
  using v l False proof (induction l arbitrary: n V K rule: list.induct)
  case Nil
  have False using Nil.prems (2) by simp
  thus ?case by (rule ccontr)
next
  case (Cons x l)
  have lrw: "length (x # l) - 1 - n = length l - 1 - (n - 1)"
    using Cons.prems(3) by auto
  have set_rw: "set (x # remove1 (l ! (n - 1)) l) = V - {l ! (n - 1)}"
    using Cons.prems (1)
    by (metis Cons.prems(2) Cons.prems(3) nth_not_zero remove1_reduce set_remove1_eq sorted_variables_coherent sorted_variables_distinct)
  (*This is probably the key step in the proof, since the "cost" commutes we can 
    later rewrite the thesis to apply the induction hypothesis:*)
  have cost_x_l: "cost x (V - {l ! (n - 1)}) (cost (l ! (n - 1)) V K)
    = cost (l ! (n - 1)) (V - {x}) (cost x V K)"
  proof (rule cost_commute)
    show "l ! (n - 1) \<in> V" and "x \<in> V" using Cons.prems (1,2,3)
      using sorted_variables_coherent by force+
  qed
  have take_cost_cost: "take_cost (2 ^ (length l - 1 - (n - 1)))
     (evaluation l (cost x (set (x # l)) K)) =
    evaluation (remove1 (l ! (n - 1)) l)
     (cost x (set (x # remove1 (l ! (n - 1)) l)) (cost (l ! (n - 1)) V K))"
    unfolding sorted_variables_coherent [symmetric, OF Cons.prems(1)]
    unfolding set_rw
    unfolding cost_x_l
  proof (cases "n = 1")
    case False
    show "take_cost (2 ^ (length l - 1 - (n - 1))) (evaluation l (cost x V K)) =
      evaluation (remove1 (l ! (n - 1)) l) (cost (l ! (n - 1)) (V - {x}) (cost x V K))"
    proof (rule Cons (1))
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "n - 1 < length l" using Cons.prems (2,3) by simp
      show "n - 1 \<noteq> 0" using False Cons.prems (3) by simp
    qed
  next
    case True
    have one: "1 - 1 = (0::nat)" by linarith
    show "take_cost (2 ^ (length l - 1 - (n - 1))) (evaluation l (cost x V K)) =
      evaluation (remove1 (l ! (n - 1)) l) (cost (l ! (n - 1)) (V - {x}) (cost x V K))"
      unfolding True one
    proof (rule evaluation_nth_0_cost)
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "0 < length l" using Cons.prems (2,3) True by auto
    qed
  qed
  (*This is probably the key step in the proof, since the "cost" commutes 
  with "link_ext" we can later rewrite the thesis to apply the induction hypothesis:*)
  have link_ext_cost_x_l: "link_ext x (V - {l ! (n - 1)}) (cost (l ! (n - 1)) V K)
    = cost (l ! (n - 1)) (V - {x}) (link_ext x V K)"
  proof (rule link_ext_cost_commute)
    show "l ! (n - 1) \<in> V" and "x \<in> V" using Cons.prems (1,2,3)
      using sorted_variables_coherent by force+
    show "l ! (n - 1) \<noteq> x" using sorted_variables_distinct [OF Cons.prems (1)]
      using Cons.prems(2) Cons.prems(3) by auto
  qed
  have take_cost_link_ext: "take_cost (2 ^ (length l - 1 - (n - 1)))
     (evaluation l (link_ext x (set (x # l)) K)) =
    evaluation (remove1 (l ! (n - 1)) l)
     (link_ext x (set (x # remove1 (l ! (n - 1)) l))
       (cost (l ! (n - 1)) V K))"
    unfolding sorted_variables_coherent [symmetric, OF Cons.prems(1)]
    unfolding set_rw
    unfolding link_ext_cost_x_l
  proof (cases "n = 1")
  case False
  show "take_cost (2 ^ (length l - 1 - (n - 1))) (evaluation l (link_ext x V K)) =
    evaluation (remove1 (l ! (n - 1)) l)
     (cost (l ! (n - 1)) (V - {x}) (link_ext x V K))"
  proof (rule Cons (1))
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "n - 1 < length l" using Cons.prems (2,3) by simp
      show "n - 1 \<noteq> 0" using False Cons.prems (3) by simp
    qed
  next
    case True
    have one: "1 - 1 = (0::nat)" by linarith
    show " take_cost (2 ^ (length l - 1 - (n - 1))) (evaluation l (link_ext x V K)) =
    evaluation (remove1 (l ! (n - 1)) l) (cost (l ! (n - 1)) (V - {x}) (link_ext x V K))"
      unfolding True one
    proof (rule evaluation_nth_0_cost)
      show "(V - {x}, l) \<in> sorted_variables" 
        using Cons.prems (1)
        using sorted_variables.cases by force
      show "0 < length l" using Cons.prems (2,3) True by auto
    qed
  qed
  show ?case
    unfolding evaluation.simps
    unfolding remove1_reduce [OF Cons.prems (3) Cons.prems (2) sorted_variables_distinct [OF Cons.prems (1)]]
    unfolding nth_not_zero [OF Cons.prems (3)]
    unfolding evaluation.simps unfolding lrw 
    unfolding take_cost_cost [symmetric] take_cost_link_ext [symmetric]
  proof (rule take_cost_power_append [of _ "length l"])
    show "length l - 1 - (n - 1) < length l"
      using Cons.prems(2) Cons.prems(3) by force
    show "length (evaluation l (link_ext x (set (x # l)) K)) = 2 ^ length l" 
      and "length (evaluation l (cost x (set (x # l)) K)) = 2 ^ length l"
      by (rule length_evaluation)+
  qed
 qed
qed

section\<open>Beads.\<close>

lemma evaluation_coherent:
  assumes e: "evaluation l K = evaluation l K'"
    and k: "K \<subseteq> powerset (set l)" and k': "K' \<subseteq> powerset (set l)"
  shows "K = K'"
  sorry

lemma assumes k: "K \<subseteq> powerset V" and x: "V \<noteq> {}" and f: "finite V" and kne: "K \<noteq> {}"
    and l: "\<exists>l. (V, l) \<in> sorted_variables \<and> evaluation l K \<in> not_evaders"
  shows "non_evasive V K"
proof -
  from l obtain l where vl: "(V, l) \<in> sorted_variables" 
    and e: "evaluation l K \<in> not_evaders" by auto
  have vsl: "V = set l" using sorted_variables_coherent [OF vl] .
  show ?thesis
    using f k vl e x kne
    unfolding vsl
  proof (induction l arbitrary: K)
    case Nil from `set [] \<noteq> {}` have False by simp
    thus ?case by simp
  next
    case (Cons v l)
    from `evaluation (v # l) K \<in> not_evaders`
    have ev_either: "(evaluation l (link_ext v (set (v # l)) K) = evaluation l (cost v (set (v # l)) K)) 
    \<or> ((evaluation l (link_ext v (set (v # l)) K) \<in> not_evaders) \<and> 
        (evaluation l (cost v (set (v # l)) K) \<in> not_evaders))"
    using not_evaders.simps [of "evaluation (v # l) K"]      
    unfolding evaluation.simps
    using append_eq_same_length(1) append_eq_same_length(2)
    using length_evaluation_eq by metis
  show ?case
  proof (cases "(evaluation l (link_ext v (set (v # l)) K) = evaluation l (cost v (set (v # l)) K))")
    case True
    have lc_eq: "link_ext v (set (v # l)) K = cost v (set (v # l)) K"
    proof (rule evaluation_coherent [of l])
      show "evaluation l (link_ext v (set (v # l)) K) = evaluation l (cost v (set (v # l)) K)"
        using True .
      show "link_ext v (set (v # l)) K \<subseteq> powerset (set l)"
        using link_ext_closed [of K "set (v # l)" v] Cons.prems (2,3)
        using sorted_variables_distinct by fastforce
      show "cost v (set (v # l)) K \<subseteq> powerset (set l)"
        using cost_closed [of K "set (v # l)" v] Cons.prems (2,3)
        using sorted_variables_distinct by fastforce
    qed
    have cone: "cone (set (v # l)) K"
    proof (rule cost_eq_link_ext_impl_cone [of v])
     show "cost v (set (v # l)) K = link_ext v (set (v # l)) K" using lc_eq ..
     show "v \<in> set (v # l)" by simp
     show "K \<subseteq> powerset (set (v # l))" using Cons.prems (2) .
     show "K \<noteq> {}" using Cons.prems (6) .
   qed
   show ?thesis using cone_non_evasive [OF Cons.prems (1) cone] .
 next
   case False
   have el: "(evaluation l (link_ext v (set (v # l)) K) \<in> not_evaders)" and
        ec: "(evaluation l (cost v (set (v # l)) K) \<in> not_evaders)"
     using ev_either False by simp_all
   have svl: "set (v # l) - {v} = set l"
     using Cons.prems (3) using sorted_variables_distinct by fastforce
   have ne_l: "non_evasive (set l) (link_ext v (set (v # l)) K)"
   proof (rule Cons)
     show "finite (set l)" using Cons.prems (1) by simp
     show "link_ext v (set (v # l)) K \<subseteq> powerset (set l)"
       using link_ext_closed [OF Cons.prems (2), of v] unfolding svl .
     show "(set l, l) \<in> sorted_variables"
       using Cons.prems(3) sorted_variables_distinct sorted_variables_remove by fastforce
     show "evaluation l (link_ext v (set (v # l)) K) \<in> not_evaders" using el .
     show "set l \<noteq> {}"
       by (metis False ec el evaluation.simps(2) set_empty true_evader)
     show "link_ext v (set (v # l)) K \<noteq> {}" sorry
   qed
   have ne_c: "non_evasive (set l) (cost v (set (v # l)) K)"
   proof (rule Cons)
     show "finite (set l)" using Cons.prems (1) by simp
     show "cost v (set (v # l)) K \<subseteq> powerset (set l)"
       using cost_closed [OF Cons.prems (2), of v] 
       unfolding svl .
     show "(set l, l) \<in> sorted_variables"
       using Cons.prems(3) sorted_variables_distinct sorted_variables_remove by fastforce
     show "evaluation l (cost v (set (v # l)) K) \<in> not_evaders" using ec .
     show "set l \<noteq> {}"
       by (metis False ec el evaluation.simps(2) set_empty true_evader)
     show "cost v (set (v # l)) K \<noteq> {}" sorry
   qed
   have c2: "2 \<le> card (set (v # l))" sorry
   show ?thesis
   proof (unfold non_evasive.simps (5) [OF c2, of _], intro bexI [of _ v] conjI)
    show "non_evasive (set (v # l) - {v}) (link_ext v (set (v # l)) K)"
      using ne_l unfolding svl .
    show "non_evasive (set (v # l) - {v}) (cost v (set (v # l)) K)"
       using ne_c unfolding svl .
    show "v \<in> set (v # l)" by simp
  qed
  qed
qed
  

lemma evaluation_coherent:
  assumes e: "evaluation l K = evaluation l K'"
    and k: "K \<subseteq> powerset (set l)" and k': "K' \<subseteq> powerset (set l)"
  shows "K = K'"
  using e k k' proof (induct l arbitrary: K K')
  case Nil
  then show ?case 
    unfolding powerset_def using evaluation.simps (1,2)
    by (metis Pow_empty list.inject list.set(1) subset_singleton_iff)
next
  case (Cons a l)
  from Cons.prems (1)
  have "evaluation l (link_ext a (set (a # l)) K) @ evaluation l (cost a (set (a # l)) K)
    = evaluation l (link_ext a (set (a # l)) K') @ evaluation l (cost a (set (a # l)) K')"
    unfolding evaluation.simps .
  hence el: "evaluation l (link_ext a (set (a # l)) K) = evaluation l (link_ext a (set (a # l)) K')"
    and ec: "evaluation l (cost a (set (a # l)) K) = evaluation l (cost a (set (a # l)) K')"
    using length_evaluation_eq by auto
  have leq: "(link_ext a (set (a # l)) K) = (link_ext a (set (a # l)) K')"
  proof (rule Cons.hyps(1))
    show "evaluation l (link_ext a (set (a # l)) K) = evaluation l (link_ext a (set (a # l)) K')"
      by (rule el)
    show "link_ext a (set (a # l)) K \<subseteq> powerset (set l)" 
      using Cons.prems (2) unfolding link_ext_def powerset_def by auto
    show "link_ext a (set (a # l)) K' \<subseteq> powerset (set l)"
      using Cons.prems (3) unfolding link_ext_def powerset_def by auto
  qed
  have ceq: "(cost a (set (a # l)) K) = (cost a (set (a # l)) K')"
  proof (rule Cons.hyps(1))
    show "evaluation l (cost a (set (a # l)) K) = evaluation l (cost a (set (a # l)) K')"
      by (rule ec)
    show "cost a (set (a # l)) K \<subseteq> powerset (set l)" 
      using Cons.prems (2) unfolding cost_def powerset_def by auto
    show "cost a (set (a # l)) K' \<subseteq> powerset (set l)"
      using Cons.prems (3) unfolding cost_def powerset_def by auto
  qed
  show ?case
  proof
    show "K \<subseteq> K'"
    proof
      fix x assume x: "x \<in> K" show "x \<in> K'"
      proof (cases "a \<in> x")
        case False
        show ?thesis
          using Cons.prems (2,3) leq ceq x False
          unfolding powerset_def cost_def link_ext_def try by force by fast
    sorry
qed

lemma
  assumes e: "evaluation l K \<in> not_evaders"
  shows "\<exists>n<length l. link_ext (l!n) (set l) K = cost (l!n) (set l) K"
  using e proof (induction l arbitrary: K)
  case Nil
  then show ?case using evaluation.simps
    by (metis false_evader true_evader)
next
  case (Cons a l)
  from Cons.prems
  have "(evaluation l (link_ext a (set (a # l)) K) = evaluation l (cost a (set (a # l)) K)) 
    \<or> ((evaluation l (link_ext a (set (a # l)) K) \<in> not_evaders) \<and> 
        (evaluation l (cost a (set (a # l)) K) \<in> not_evaders))"
    using not_evaders.simps [of "evaluation (a # l) K"]
    unfolding evaluation.simps 
    using append_eq_same_length(1) append_eq_same_length(2)
    using length_evaluation_eq by metis
  show ?case
  proof (cases "(evaluation l (link_ext a (set (a # l)) K) = evaluation l (cost a (set (a # l)) K))")
    case True
    show ?thesis using True thm evaluation.simps
qed

lemma
  assumes k: "K \<subseteq> powerset V" and vl: "(V, l) \<in> sorted_variables"
    and f: "finite V"
    and ene: "evaluation l K \<in> not_evaders" and x: "x \<in> V"
  shows "evaluation (remove1 x l) (link_ext x V K) \<in> not_evaders"
  thm not_evaders.intros evaluation.simps thm link_ext_def
  using k vl f ene x proof (induct l arbitrary: V l K rule: list.induct)
  case Nil have "V = {}" using Nil.prems (2) using Nil using sorted_variables.simps [of "{}" "[]"] Nil
  case 0 have v: "V = {}" using "0.hyps" "0.prems"(3) by force
  hence False using `x \<in> V` by fast 
  thus "evaluation (remove1 x l) (link_ext x V K) \<in> not_evaders" by (rule ccontr)
next
  case (Suc n)
  
  hence "l = []" using "Suc.prems"(5) by auto
  have "K = {} \<or> K = {{}}" using v "0.prems" (1) try
    using "0.prems"(5) by auto
  from evaluation.simps

lemma
  assumes k: "K \<subseteq> powerset V" and vl: "(V, l) \<in> sorted_variables"
    and ene: "evaluation l K \<in> not_evaders" and x: "x \<in> V"
  shows "(V - {x}, remove1 x l) \<in> sorted_variables"
    and "evaluation (remove1 x l) (link_ext x V K) \<in> not_evaders"
proof -
  from vl obtain A l' y where v: "V = insert y A" and l: "l = y # l'" 
      and al: "(A, l') \<in> sorted_variables" and y: "y \<notin> A"
    using sorted_variables.simps [of V l] using x by auto
  have "(V - {x}, remove1 x l) \<in> sorted_variables"
  proof (cases "V - {x} = {}")
    case True hence v: "V = {x}" using x by auto hence l: "l = [x]" 
      using vl using \<open>V = insert y A\<close> \<open>l = y # l'\<close> sorted_variables_length_coherent 
      by fastforce
    show ?thesis unfolding v l
      by (simp add: sorted_variables.intros(1))
  next
    case False note vxne = False
    show ?thesis
    proof (cases "x = y")
      case True
      show ?thesis unfolding True unfolding v l using al y by simp
    next
      case False
      have vx: "V - {x} = insert y (A - {x})" using \<open>V = insert y A\<close> y False by auto
      have rxl: "remove1 x l = y # (remove1 x l')" using \<open>l = y # l'\<close> False by simp
      have "(A - {x}, remove1 x l') \<in> sorted_variables"
      show ?thesis unfolding vx rxl
      proof (intro sorted_variables.intros (2))
        show "(A - {x}, remove1 x l') \<in> sorted_variables" 
          using al using sorted_variables.intros

    have "(V - {x}, remove1 x l) \<in> sorted_variables"
    using vl x using sorted_variables.simps
    using False remove1_idem sorted_variables_coherent vl by fastforce
  have "K = link_ext x V K" using False k unfolding link_ext_def powerset_def apply auto try

lemma assumes k: "K \<subseteq> powerset V" and x: "V \<noteq> {}" and f: "finite V" 
  and l: "\<exists>l. (V, l) \<in> sorted_variables \<and> evaluation l K \<in> not_evaders"
  shows "non_evasive V K"
  using x k f l proof (induct "card V" arbitrary: V K)
  case 0 have v: "V = {}" using "0.prems" (3) "0.hyps" by simp  
  hence False using "0.prems" (1) by fast
  thus "non_evasive V K" by (rule ccontr)
next
  case (Suc n)
  show "non_evasive V K"
  proof (cases "n = 0")
    case True
    then obtain x where v: "V = {x}" using Suc.hyps (2)
      by (metis One_nat_def card_1_singletonE)
    show ?thesis
    proof (cases "K = {} \<or> K = {{x}, {}}")
      case True
      show ?thesis using True using non_evasive.simps (2,3) [OF v, of K] by blast
    next
      case False
      have k: "K = {{x}} \<or> K = {{}}"
        unfolding powerset_def using v using False
        by (metis Suc.prems(2) doubleton_eq_iff powerset_singleton_cases)
      from Suc.prems (4)
      obtain l where vl: "(V, l) \<in> sorted_variables" and el: "evaluation l K \<in> not_evaders"
        by auto
      have l: "l = [x]"
        using sorted_variables_coherent [OF vl]
        using sorted_variables_length_coherent [OF vl]
        unfolding v
        by (metis card_1_singleton_iff empty_iff length_0_conv length_Suc_conv list.set(1) list.set_intros(1) list.simps(15) set_ConsD)
      show ?thesis
      proof (cases "K = {{x}}")
        case True
        have "evaluation l K = [True, False]"
          unfolding l True
          unfolding evaluation.simps link_ext_def cost_def powerset_def
          using evaluation.simps (1,2) using v apply auto
          by (smt (verit, ccfv_threshold) Suc.prems(1) append.left_neutral append_Cons bot.extremum emptyE empty_Collect_eq evaluation.simps(1) evaluation.simps(2))
        hence "evaluation l K \<notin> not_evaders"
          using tf_not_not_evader by simp
        hence False using el by simp
        thus ?thesis by (rule ccontr)
      next
        case False hence k: "K = {{}}" using k by fast
        have "evaluation l K = [False, True]"
          unfolding l k
          unfolding evaluation.simps link_ext_def cost_def powerset_def
          using evaluation.simps (1,2) using v by auto
        hence "evaluation l K \<notin> not_evaders"
          using ft_not_not_evader by simp
        hence False using el by simp
        thus ?thesis by (rule ccontr)
      qed
    qed
  next
    case False
    hence two: "2 \<le> card V" using Suc.hyps (2) by simp
    obtain x where x: "x \<in> V" using two by fastforce
    have ne_link: "non_evasive (V - {x}) (link_ext x V K)"
    proof (rule Suc.hyps (1))
      show "n = card (V - {x})" using x Suc.hyps (2) by simp
      show "V - {x} \<noteq> {}" using False \<open>n = card (V - {x})\<close> by force
      show "link_ext x V K \<subseteq> powerset (V - {x})"
        using Suc.prems (2)
        using link_ext_def powerset_def by force
      show "finite (V - {x})" using Suc.prems(3) by blast
      show "\<exists>l. (V - {x}, l) \<in> sorted_variables \<and> evaluation l (link_ext x V K) \<in> not_evaders"
        using Suc
    from Suc
    show "non_evasive V K" unfolding non_evasive.simps (5) [OF two, of K]
  hence k: "K = {} \<or> K = {{}}" using "0.prems" (1) unfolding powerset_def by auto
  show "non_evasive V K" unfolding v using k using non_evasive.simps



end