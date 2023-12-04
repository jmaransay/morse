
theory OrderedCollapsible
  imports
    "Nonevasive"
begin

definition cone_peak :: "nat set \<Rightarrow> nat set set \<Rightarrow> nat \<Rightarrow> bool"
  where "cone_peak V K v = (v \<in> V \<and>
                    (\<exists>B. B \<subseteq> powerset (V - {v}) \<and> K = B \<union> {s. \<exists>b\<in>B. s = insert v b}))"

lemma cone_cone_peak:
  "cone V K \<equiv> (\<exists>v\<in>V. cone_peak V K v)" unfolding cone_def cone_peak_def by simp

lemma "cone {} K = False"
  by (simp add: not_cone_empty_vertex_set)

lemma "cone_peak {} K v = False" by (simp add: cone_peak_def)

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
  have vvy: "v \<in> V - {y}" using v yv by simp
  have ceq: "cost y V K = cost y (V - {v}) B \<union> {s. \<exists>t\<in>cost y (V - {v}) B. s = insert v t}"
    by (rule cost_cone_eq, intro v, intro yv [symmetric], intro B, intro K)
  show ?thesis
  proof (unfold cone_peak_def, intro conjI, intro vvy, intro exI [of _ "cost y (V - {v}) B"], rule conjI)
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
  have vvy: "v \<in> V - {y}" using v yv by simp
  have ceq: "link_ext y V K = link_ext y (V - {v}) B \<union> {s. \<exists>t\<in>link_ext y (V - {v}) B. s = insert v t}"
    by (rule link_ext_cone_eq, intro v, intro yv [symmetric], intro B, intro K)
  show ?thesis
  proof (unfold cone_peak_def, intro conjI, intro vvy, intro exI [of _ "link_ext y (V - {v}) B"], rule conjI)
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

text\<open>A cone over a vertex @{term v} is @{term ordered_zero_collapsible}.\<close>

lemma cone_is_ordered_zero_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and v: "l = v # l'" and d: "distinct l"
    and c: "cone_peak (set l) K v" shows "ordered_zero_collapsible l K"
proof -
  from v have ll: "0 < length l" by simp
  show ?thesis using ordered_zero_collapsible.simps(2) [OF ll] using c v by simp
qed

lemma cone_is_ordered_m_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and v: "l = v # l'" and d: "distinct l"
    and c: "cone_peak (set l) K v" shows "ordered_m_collapsible n l K"
proof -
  from v have ll: "0 < length l" by simp
  show ?thesis
  proof (induct n)
    case 0
    then show ?case using ordered_m_collapsible.simps(2) [OF ll] using c v by simp
  next
    case (Suc n)
    show ?case using ordered_m_collapsible.simps(2) [OF ll, of "Suc n" K] using c v by simp
  qed
qed

text\<open>For sets of vertexes of cardinality less or equal to @{term "2::nat"}, the three previous
  definitions are equivalent.\<close>

lemma cs_card_leq_2: assumes K: "K \<subseteq> powerset V" and c: "V = {v1,v2}" and v1v2: "v1 \<noteq> v2" 
    and sc: "closed_subset K"
  shows "K = {} \<or> K = {{}} \<or> K = {{v1},{}} \<or> K = {{v2},{}} \<or> K = {{v1},{v2},{}} \<or> K = {{v1,v2},{v1},{v2},{}}"
proof -
  have pV: "powerset V = {{v1,v2},{v1},{v2},{}}" using c unfolding powerset_def by auto
  thus ?thesis using K sc unfolding closed_subset_def
    by (smt (verit, ccfv_threshold) empty_subsetI insert_commute insert_subset subset_antisym subset_insert subset_insertI)
qed

lemma cone_is_one:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l" and lne: "l \<noteq> []"
  shows "ordered_m_collapsible 0 l K = cone_peak (set l) K (hd l)"
proof (cases l)
  case Nil
  have "ordered_m_collapsible 0 l K = False" using ordered_m_collapsible.simps (1) [OF Nil] .
  moreover have "cone_peak (set l) K (hd l) = False" using lne local.Nil by auto
  ultimately show ?thesis by fast
next
  case (Cons a list)
  hence l0: "0 < length l" by simp
  have "ordered_m_collapsible 0 (a # list) K = cone_peak (set l) K (hd l)"
  proof (cases "cone_peak (set l) K (hd l)")
    case True
    then show ?thesis using ordered_m_collapsible.simps (2) [OF l0, of 0 K]
      using local.Cons by blast
  next
    case False
    then show ?thesis using ordered_m_collapsible.simps (2) [OF l0, of 0 K] try
  qed
    using ordered_m_collapsible.simps (2)
  show ?thesis sorry
qed
  
  using ordered_m_collapsible.simps


lemma cone_is_one:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_zero_collapsible l K" 
  shows "ordered_m_collapsible 1 l K"
using K c d proof (induct "length l" arbitrary: l K rule: less_induct)
    case less
    from less.prems (2) have l0: "0 < length l" by auto
    from less.prems (2) and ordered_zero_collapsible.simps (2) [OF l0, of K]
    have ei: "(cone_peak (set l) K (hd l) \<or>
       ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
      cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l))" by simp
    show ?case
    proof (cases "cone_peak (set l) K (hd l)")
      case True
      show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0] using True by simp
      next
        case False
        hence cost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" and
          link: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)" using ei False by simp_all
        have "ordered_m_collapsible 1 (tl l) (cost (hd l) (set l) K)"
        proof (rule less.hyps)
          show "length (tl l) < length l" using l0 by simp
          show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
            using less.prems (1) l0 unfolding powerset_def cost_def
            by (smt (verit, del_insts) Diff_insert_absorb insert_absorb length_greater_0_conv list.exhaust_sel list.simps(15) mem_Collect_eq subset_iff)
          show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using cost by simp
          show "distinct (tl l)" by (simp add: distinct_tl less.prems(3))
        qed
        from link have "ordered_m_collapsible 0 (tl l) (link_ext (hd l) (set l) K)"
          using ordered_m_collapsible.simps (2) []
          try
        proof (rule less.hyps)
        proof (cases "tl l = []")
      case True have False using cost unfolding True by simp
      thus ?thesis by (rule ccontr)
    next
      case False hence tl0: "0 < length (tl l)" by blast
      have "ordered_m_collapsible 0 (tl l) (link_ext (hd l) (set l) K)
        = cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)"
        using ordered_m_collapsible.simps (2) [OF tl0] using link
        
      then show ?thesis unfolding ordered_m_collapsible.simps (2) [OF tl0] using link
    qed
      
      using ordered_m_collapsible.simps using link
    proof (rule less.hyps)
    show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0] using less.hyps
qed
  

proof -
  from v have l0: "0 < length l" by auto
  from c and ordered_zero_collapsible.simps (2) [OF l0, of K]
  have ei: "(cone_peak (set l) K (hd l) \<or>
     ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
     cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l))" by simp
  show ?thesis
  proof (cases "cone_peak (set l) K (hd l)")
    case True
    show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0] using True by simp
  next
    case False 
    hence "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
     cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)" using ei False by simp
    show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0]
  qed
    
using K v c d proof (induct "length l" arbitrary: l K rule: less_induct)


lemma cone_is_one:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l" and c: "card (set l) \<le> 2"
    and sc: "closed_subset K"
    and o: "ordered_non_evasive l K" shows "ordered_zero_collapsible l K"
proof (cases "card (set l) = 0")
  case True hence le: "l = []" by simp
  from o have False using ordered_non_evasive.simps (1) [OF le, of K] by simp
  thus ?thesis by (rule ccontr)
next
  case False note lne = False
  show ?thesis
  proof (cases "card (set l) = 1")
    case True then obtain v1 where lv1: "l = [v1]" and ll: "0 < length l" using d
      by (metis One_nat_def distinct_card length_0_conv length_Suc_conv less_numeral_extra(1))
    show ?thesis
      using o unfolding ordered_non_evasive.simps (2) [OF ll]
      unfolding ordered_zero_collapsible.simps (2) [OF ll] unfolding lv1 by simp
  next
    case False hence "card (set l) = 2" using c lne by linarith
    hence ll2: "length l = 2" using d by (simp add: distinct_card)
    then obtain v1 v2 where lv1v2: "l = [v1,v2]" and ll: "0 < length l" and v1v2: "v1 \<noteq> v2"
      using d lne
      by (metis (no_types, opaque_lifting) One_nat_def Suc_1 distinct_length_2_or_more length_Cons length_tl less_numeral_extra(3) list.exhaust_sel list.sel(3) list.size(3) zero_less_Suc)
    hence Keq: "K = {} \<or> K = {{}} \<or> K = {{v1},{}} \<or> K = {{v2},{}} \<or> K = {{v1},{v2},{}} \<or> K = {{v1,v2},{v1},{v2},{}}"
      using cs_card_leq_2 [OF K _ v1v2 sc] by simp
    show ?thesis
    proof (cases "K = {}")
      case True show ?thesis using o
        using ordered_non_evasive.simps (2) [OF ll, of K]
        using ordered_zero_collapsible.simps (2) [OF ll, of K]
        unfolding True cone_peak_def by simp
    next
      case False note Kne = False
      show ?thesis
      proof (cases "K = {{}}")
        case True show ?thesis using o
        using ordered_non_evasive.simps (2) [OF ll, of K]
        using ordered_zero_collapsible.simps (2) [OF ll, of K]
        unfolding True cone_peak_def powerset_def lv1v2 v1v2 link_ext_def cost_def by auto
      next
        case False note Knne = False
        show ?thesis
        proof (cases "K = {{v1},{}}")
          case True
          show ?thesis using o
            using ordered_non_evasive.simps (2) [OF ll, of K]
            using ordered_zero_collapsible.simps (2) [OF ll, of K]
            unfolding True cone_peak_def powerset_def lv1v2 v1v2 link_ext_def cost_def 
            try by auto
  
      using Keq K o
      unfolding ordered_non_evasive.simps (2) [OF ll]
      unfolding ordered_zero_collapsible.simps (2) [OF ll] 
      unfolding lv1v2 using v1v2 apply simp
      unfolding cone_peak_def powerset_def link_ext_def cost_def
           apply simp+ try apply auto apply simp try

  next
    case False
    then show ?thesis sorry
  qed
    
qed
  

  


end