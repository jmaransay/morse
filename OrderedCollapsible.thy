
theory OrderedCollapsible
  imports
    "Nonevasive"
begin

definition cone_peak :: "nat set \<Rightarrow> nat set set \<Rightarrow> nat \<Rightarrow> bool"
  where "cone_peak V K v = (\<exists>B. B \<subseteq> powerset (V - {v})
                      \<and> K = B \<union> {s. \<exists>b\<in>B. s = insert v b})"

lemma cone_cone_peak:
  "cone V K \<equiv> (\<exists>v\<in>V. cone_peak V K v)" unfolding cone_def cone_peak_def .

section\<open>Definition of \emph{ordered-no-evasive}\<close>

function ordered_non_evasive :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_non_evasive l K = False"
  | "0 < length l \<Longrightarrow> ordered_non_evasive l K = ((cone_peak (set l) K (hd l))
      | (ordered_non_evasive (tl l) (cost (hd l) (set l) K) \<and>
          ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

(*Definition using an additional set for the vertexes, instead of just a list:

function ordered_non_evasive :: "nat set \<Rightarrow> nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> ordered_non_evasive V l K = False"
  | "0 < card V \<Longrightarrow> set l = V \<Longrightarrow> ordered_non_evasive V l K = ((cone_peak V K (hd l))
      | (ordered_non_evasive (V - {hd l}) (tl l) (cost (hd l) V K)) \<and>
          ordered_non_evasive (V - {hd l}) (tl l) (link_ext (hd l) V K))"
  | "0 < card V \<Longrightarrow> set l \<noteq> V \<Longrightarrow> ordered_non_evasive V l K = False"
  | "\<not> finite V \<Longrightarrow> ordered_non_evasive V l K = False"
proof -
  fix P :: "bool" and x :: "(nat set \<times> nat list \<times> nat set set)"
  assume ee: "(\<And>V l K. V = {} \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and se: "(\<And>V l K. 0 < card V \<Longrightarrow> set l = V \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and sne: "(\<And>V l K. 0 < card V \<Longrightarrow> set l \<noteq> V \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and inf: "(\<And>V l K. infinite V \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
  show P
  proof (cases "finite (fst x)")
    case False
    show P by (rule inf [of "fst x" "fst (snd x)" "snd (snd x)"], intro False) auto
  next
    case True note finitex = True
    show P
    proof (cases "fst x = {}")
      case True note ve = True
      show P using ee True by (metis eq_fst_iff)
      next
      case False
      show P
        by (metis False card_gt_0_iff eq_fst_iff inf se sne)
    qed
  qed
qed auto
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  show "wf (measure (\<lambda>(V, K). card V))" by simp
  fix V :: "nat set" and l :: "nat list"and K :: "nat set set" and x :: "nat"
  assume c: "0 < card V" and s: "set l = V"
  show "((V - {hd l}, tl l, cost (hd l) V K), V, l, K) \<in> measure (\<lambda>(V, K). card V)"
    using c s by auto (simp add: card_gt_0_iff)
  show "((V - {hd l}, tl l, link_ext (hd l) V K), V, l, K) \<in> measure (\<lambda>(V, K). card V)"
    using c s by auto (simp add: card_gt_0_iff)
qed*)

lemma cone_peak_cost_cone_eq:
  assumes v: "v \<in> V" and c: "cone_peak V K v" and yv: "y \<noteq> v" 
  shows "cone_peak (V - {y}) (cost y V K) v"
proof -
  from c obtain B where K: "K = B \<union> {s. \<exists>b\<in>B. s = insert v b}" and B: "B \<subseteq> powerset (V - {v})"
    unfolding cone_peak_def by auto
  have ceq: "cost y V K = cost y (V - {v}) B \<union> {s. \<exists>t\<in>cost y (V - {v}) B. s = insert v t}"
    by (rule cost_cone_eq, intro v, intro yv [symmetric], intro B, intro K)
  show ?thesis
  proof (unfold cone_peak_def, intro exI [of _ "cost y (V - {v}) B"], rule conjI)
    show "cost y (V - {v}) B \<subseteq> powerset (V - {y} - {v})"
      using B unfolding cost_def powerset_def by auto
    show "cost y V K = cost y (V - {v}) B \<union> {s. \<exists>b\<in>cost y (V - {v}) B. s = insert v b}"
      by (rule ceq)
  qed
qed

lemma cone_peak_link_ext_cone_eq:
  assumes v: "v \<in> V" and c: "cone_peak V K v" and yv: "y \<noteq> v" 
  shows "cone_peak (V - {y}) (link_ext y V K) v"
proof -
  from c obtain B where K: "K = B \<union> {s. \<exists>b\<in>B. s = insert v b}" and B: "B \<subseteq> powerset (V - {v})"
    unfolding cone_peak_def by auto
  have ceq: "link_ext y V K = link_ext y (V - {v}) B \<union> {s. \<exists>t\<in>link_ext y (V - {v}) B. s = insert v t}"
    by (rule link_ext_cone_eq, intro v, intro yv [symmetric], intro B, intro K)
  show ?thesis
  proof (unfold cone_peak_def, intro exI [of _ "link_ext y (V - {v}) B"], rule conjI)
    show "link_ext y (V - {v}) B \<subseteq> powerset (V - {y} - {v})"
      using B unfolding link_ext_def powerset_def by auto
    show "link_ext y V K = link_ext y (V - {v}) B \<union> {s. \<exists>b\<in>link_ext y (V - {v}) B. s = insert v b}"
      by (rule ceq)
  qed
qed

lemma cone_is_one:
  assumes K: "K \<subseteq> powerset (set l)" and v: "v \<in> set l" and d: "distinct l" 
    and c: "cone_peak (set l) K v" shows "ordered_non_evasive l K"
using K v c d proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  show ?case
  proof (cases "length l")
    case 0
    then have False using less.prems (2) by simp
    thus ?thesis by (rule ccontr)
  next
    case (Suc nat)
    obtain a l' where l: "l = a # l'" and ll: "0 < length l"
    apply (rule list.set_cases [of v])
    using less.prems (2) by simp+
  show ?thesis
  proof (cases "v = a")
    case True
    show ?thesis
      unfolding ordered_non_evasive.simps (2) [OF ll] using l True less.prems (3) by simp
  next
    case False
    have "ordered_non_evasive (tl l) (cost (hd l) (set l) K)"
    proof (rule less.hyps)
      show "length (tl l) < length l" using ll by simp
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        using less.prems (1) l unfolding powerset_def cost_def by (simp add: l subset_iff)
      show "v \<in> set (tl l)" using less.prems (2) False l by simp
      show "cone_peak (set (tl l)) (cost (hd l) (set l) K) v"
        using cone_peak_cost_cone_eq [OF less.prems (2) less.prems (3), of "hd l"] 
          l False less.prems (4) by simp
      show "distinct (tl l)" using distinct_tl [OF less.prems (4)] .
    qed
    moreover have "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)"
    proof (rule less.hyps)
      show "length (tl l) < length l" using ll by simp
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using less.prems (1) l unfolding powerset_def link_ext_def by auto
      show "v \<in> set (tl l)" using less.prems (2) False l by simp
      show "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) v"
        using cone_peak_link_ext_cone_eq [OF less.prems (2) less.prems (3), of "hd l"] 
          l False less.prems (4) by simp
      show "distinct (tl l)" using distinct_tl [OF less.prems (4)] .
    qed
    ultimately show ?thesis 
      unfolding ordered_non_evasive.simps (2) [OF ll] by simp
  qed
 qed
qed

function ordered_zero_collapsible :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_zero_collapsible l K = False"
  | "0 < length l \<Longrightarrow> ordered_zero_collapsible l K = ((cone_peak (set l) K (hd l))
      | (ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
          cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

function ordered_m_collapsible :: "nat \<Rightarrow> nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_m_collapsible m l K = False"
  | "0 < length l \<Longrightarrow> ordered_m_collapsible m l K = ((cone_peak (set l) K (hd l))
      | (ordered_m_collapsible m (tl l) (cost (hd l) (set l) K) \<and>
         ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)))"
  by (auto+)
termination by (relation "Wellfounded.measure (\<lambda>(m,l,K). length l)", auto)

end