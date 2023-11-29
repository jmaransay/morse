
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
qed


end