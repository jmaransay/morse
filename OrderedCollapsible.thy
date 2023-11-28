
theory OrderedCollapsible
  imports
    "Nonevasive"
begin

definition cone_peak :: "nat set \<Rightarrow> nat set set \<Rightarrow> nat \<Rightarrow> bool"
  where "cone_peak V K v = (\<exists>B. B \<subseteq> powerset (V - {v})
                      \<and> K = B \<union> {s. \<exists>b\<in>B. s = insert v b})"

lemma cone_cone_peak: 
  "cone V K \<equiv> (\<exists>v\<in>V. cone_peak V K v)" unfolding cone_def cone_peak_def .


section\<open>Definition of \emph{ordered-zero-collapsible}\<close>
thm cone_def
function ordered_zero_collapsible :: "nat set \<Rightarrow> nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> ordered_zero_collapsible V l K = False"
  | "V = {x} \<Longrightarrow> l = [x] \<Longrightarrow> K = {} \<Longrightarrow> ordered_zero_collapsible V l K = True"
  | "V = {x} \<Longrightarrow> l = [x] \<Longrightarrow> K = {{},{x}} \<Longrightarrow> ordered_zero_collapsible V l K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> ordered_zero_collapsible V l K = False"
  (*This can be proven from the definition: | "2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> non_evasive V K = True"*)
  | "2 \<le> card V \<Longrightarrow> ordered_zero_collapsible V l K =
      ((cone_peak V K (hd l))
      | (cone_peak (V - {hd l}) (link_ext (hd l) V K) (hd (tl l)) \<and> ordered_zero_collapsible (V - {hd l}) (tl l) (cost (hd l) V K)))"
  | "\<not> finite V \<Longrightarrow> ordered_zero_collapsible V l K = False"
proof -
  fix P :: "bool" and x :: "(nat set \<times> nat list \<times> nat set set)"
  assume ee: "(\<And>V l K. V = {} \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and se: "(\<And>V xa l K. V = {xa} \<Longrightarrow> l = [xa] \<Longrightarrow> K = {} \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and sc: "(\<And>V xa l K. V = {xa} \<Longrightarrow> l = [xa] \<Longrightarrow> K = {{}, {xa}} \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and sn: "(\<And>V xa K l. V = {xa} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{}, {xa}} \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
      and en2: "(\<And>V l K. 2 \<le> card V \<Longrightarrow> x = (V, l, K) \<Longrightarrow> P)"
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
      note vne = False
      show P
      proof (cases "card (fst x) = 1")
        case True then obtain xa where f: "fst x = {xa}" by (rule card_1_singletonE)
        show P
        proof (cases "snd (snd x) = {}")
          case True
          show P using se [of "fst x" xa "fst (snd x)" "snd (snd x)"] using f True apply auto try
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


end