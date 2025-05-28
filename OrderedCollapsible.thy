
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

lemma cone_peak_empty: "cone_peak {} K v = False" by (simp add: cone_peak_def)

lemma cone_peak_cc_empty: assumes l: "l \<noteq> []" shows "cone_peak (set l) {} (hd l)"
  using l unfolding cone_peak_def by simp

lemma cone_peak_nempty_aux: shows "\<nexists>B. {{}} = B \<union> {s. \<exists>b\<in>B. s = insert x b}"
proof (rule)
  assume b: "\<exists>B. {{}} = B \<union> {s. \<exists>b\<in>B. s = insert x b}"
  then obtain B where b: "{{}} = B \<union> {s. \<exists>b\<in>B. s = insert x b}" by auto
  show False
  proof (cases "B = {}")
    case True
    then show ?thesis using b by simp
  next
    case False
    then show ?thesis using b
      by (smt (verit) Un_insert_right equals0I insertI1 insert_absorb insert_not_empty mem_Collect_eq singletonD)
  qed
qed

lemma not_cone_peak_cc_empty: shows "\<not> cone_peak (set l) {{}} (hd l)"
proof (cases l)
  case Nil
  then show ?thesis using cone_peak_empty by simp
next
  case (Cons a list)
  show ?thesis
  proof (rule ccontr, simp)
    assume cp: "cone_peak (set l) {{}} (hd l)"
    obtain B where B: "B \<subseteq> powerset (set l - {hd l})" and Be: "{{}} = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}" 
      using cone_peak_def [of "set l" "{{}}" "hd l"] cp by auto
    show False using cone_peak_nempty_aux by (metis (no_types, lifting) ext Be)
  qed
qed

text\<open>Proposition 1 in the paper\<close>

lemma cone_peak_cost_eq_link_ext: 
  assumes v: "v \<in> V" and c: "cone_peak V K v" shows "cost v V K = link_ext v V K"
proof -
  obtain B where B: "B \<subseteq> powerset (V - {v})" and K: "K = B \<union> {s. \<exists>b\<in>B. s = insert v b}"
    using c unfolding cone_peak_def by auto
  show ?thesis
    by (rule cone_impl_cost_eq_link_ext [of _ _ B], rule v, rule B, rule K)
qed

lemma cost_eq_link_ext_cone_peak: 
  assumes v: "v \<in> V" and K: "K \<subseteq> powerset V" and c: "cost v V K = link_ext v V K" 
    shows "cone_peak V K v"
proof (unfold cone_peak_def, intro conjI, rule v)
  have "K = (cost v V K) \<union> {s. \<exists>b\<in>(cost v V K). s = insert v b}"
  proof
    show "cost v V K \<union> {s. \<exists>b\<in>cost v V K. s = insert v b} \<subseteq> K"
      using K c v unfolding powerset_def cost_def link_ext_def by auto
    show "K \<subseteq> cost v V K \<union> {s. \<exists>b\<in>cost v V K. s = insert v b}"
    proof (subst c, unfold cost_def link_ext_def powerset_def, rule)
      fix xa
      assume xa: "xa \<in> K"
      show "xa \<in> {s \<in> Pow V. v \<notin> s \<and> insert v s \<in> K} \<union>
                {s. \<exists>t\<in>{s \<in> Pow (V - {v}). s \<in> K}. s = insert v t}"
      proof (cases "v \<in> xa")
        case False then show ?thesis using xa c K 
          unfolding cost_def link_ext_def powerset_def by blast
      next
        case True
        have "xa - {v} \<in> {s \<in> Pow V. v \<notin> s \<and> insert v s \<in> K}"
          using xa K True mk_disjoint_insert unfolding powerset_def
          by fastforce
        hence "xa - {v} \<in> {s \<in> Pow (V - {v}). s \<in> K}"
          using c unfolding cost_def link_ext_def powerset_def by simp
        hence "xa \<in> {s. \<exists>t\<in>{s \<in> Pow (V - {v}). s \<in> K}. s = insert v t}"
          using True by auto
        thus ?thesis by fast
      qed
    qed
  qed
  moreover have "cost v V K \<subseteq> powerset (V - {v})" 
    using K
    unfolding cost_def powerset_def by auto
  ultimately show "\<exists>B\<subseteq>powerset (V - {v}). K = B \<union> {s. \<exists>b\<in>B. s = insert v b}" by auto
qed

corollary proposition_1:
  assumes v: "v \<in> V" and K: "K \<subseteq> powerset V" shows "cone_peak V K v \<equiv> (cost v V K = link_ext v V K)"
  using cone_peak_cost_eq_link_ext [OF v, of K]
  using cost_eq_link_ext_cone_peak [OF v K] by argo

text\<open>Proposition 2 in our paper.\<close>

lemma proposition_2:
  assumes K: "K \<subseteq> powerset V" and c: "closed_subset K"
  shows "K = cost v V K \<union> join_vertex v (link_ext v V K)"
proof -
  have "K = cost v V K \<union> join_vertex v (link v V K)" using complex_decomposition [OF K c] .
  moreover have "link v V K = link_ext v V K"
    using K c 
    unfolding link_def link_ext_def powerset_def closed_subset_def by auto
  ultimately show ?thesis by simp
qed

section\<open>Definition of \emph{ordered-no-evasive}\<close>

function ordered_non_evasive :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_non_evasive l K = False"
  | "0 < length l \<Longrightarrow> ordered_non_evasive l K = ((cone_peak (set l) K (hd l))
      | (ordered_non_evasive (tl l) (cost (hd l) (set l) K) \<and>
          ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

lemma ordered_non_evasive_empty_cc: 
  assumes lne: "l \<noteq> []" shows "ordered_non_evasive l {}"
proof (cases l)
  case Nil
  have False using lne Nil by fast thus ?thesis by (rule ccontr)
next
  case (Cons a list)
  have "cone_peak (set l) {} (hd l)" by (rule cone_peak_cc_empty, simp add: Cons)
  thus ?thesis using ordered_non_evasive.simps (2) Cons by simp
qed

lemma ordered_non_evasive_empty: shows "\<not> ordered_non_evasive l {{}}"
proof (induct l)
  case Nil
  then show ?case using ordered_non_evasive.simps (1) by simp
next
  case (Cons a l)
  assume one: "\<not> ordered_non_evasive l {{}}" 
  have c: "cost (hd (a # l)) (set (a # l)) {{}} = {{}}" unfolding cost_def powerset_def by auto
  have l: "link_ext (hd (a # l)) (set (a # l)) {{}} = {}" unfolding link_ext_def powerset_def list.sel by auto
  have "\<not> cone_peak (set (a # l)) {{}} (hd (a # l))" by (rule not_cone_peak_cc_empty)
  moreover have "\<not> ordered_non_evasive (tl (a # l)) (cost (hd (a # l)) (set (a # l)) {{}})"
    unfolding c unfolding list.sel using one . 
  (*moreover have "ordered_non_evasive (tl (a # l)) (link_ext (hd (a # l)) (set (a # l)) {{}})"
    unfolding l unfolding list.sel using ordered_non_evasive_empty_cc .*)
  ultimately show ?case by simp
qed

section\<open>Lemmas about @{term cone_peak}.\<close>

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
  | "1 = length l \<Longrightarrow> ordered_zero_collapsible l K = cone_peak (set l) K (hd l)" (*It might be rewritten as True?*) 
  | "1 < length l \<Longrightarrow> ordered_zero_collapsible l K = ((cone_peak (set l) K (hd l))
      | (ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
          cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))))" 
  by auto (metis One_nat_def length_0_conv less_one linorder_neqE_nat)
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

(*function ordered_zero_collapsible :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_zero_collapsible l K = False"
  | "0 < length l \<Longrightarrow> ordered_zero_collapsible l K = ((cone_peak (set l) K (hd l))
      | (ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
          cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)*)

lemma ordered_zero_collapsible_intro1 [intro]: "l = [] \<Longrightarrow> ordered_zero_collapsible l K = False" 
  using ordered_zero_collapsible.simps (1) .

lemma ordered_zero_collapsible_intro2 [intro]: "1 = length l \<Longrightarrow> cone_peak (set l) K (hd l) \<Longrightarrow> ordered_zero_collapsible l K" 
  using ordered_zero_collapsible.simps (2) by simp

lemma ordered_zero_collapsible_intro3 [intro]: "1 < length l 
    \<Longrightarrow> (ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) 
          \<and> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))) \<Longrightarrow> ordered_zero_collapsible l K" 
  using ordered_zero_collapsible.simps (2) by simp

lemma ordered_zero_collapsible_cc_empty: assumes l: "0 < length l" shows "ordered_zero_collapsible l {}"
  using l
  by (metis cone_peak_cc_empty length_0_conv less_one linorder_neq_iff ordered_zero_collapsible.simps(3)
      ordered_zero_collapsible_intro2)

lemma ordered_zero_collapsible_empty: "\<not> ordered_zero_collapsible [] {{}}" by simp

lemma not_ordered_zero_collapsible_not_empty: 
  assumes l0: "0 < length l" shows "\<not> ordered_zero_collapsible l {{}}"
proof (cases "1 = length l")
  case True show "\<not> ordered_zero_collapsible l {{}}"
    unfolding ordered_zero_collapsible.simps (2) [OF True, of "{{}}"]
    using not_cone_peak_cc_empty .
next
  case False hence l: "1 < length l" using l0 by linarith
  show ?thesis
    using l proof (induct "length l" arbitrary: l)
    case 0 then have False by simp thus ?case by simp
  next
    case (Suc x)
    have le: "link_ext (hd l) (set l) {{}} = {}" unfolding link_ext_def powerset_def by simp
    have ce: "cost (hd l) (set l) {{}} = {{}}" unfolding cost_def powerset_def by auto
    have c1: "\<not> cone_peak (set l) {{}} (hd l)" using not_cone_peak_cc_empty [of "l"] .
    moreover have c2: "cone_peak (set (tl l)) (link_ext (hd l) (set l) {{}}) (hd (tl l))"
      unfolding le using cone_peak_cc_empty using Suc.prems
      by (metis Nitpick.size_list_simp(2) One_nat_def not_less_iff_gr_or_eq zero_less_Suc)
    moreover have "\<not> ordered_zero_collapsible (tl l) (cost (hd l) (set l) {{}})" 
      unfolding ce
    proof (cases "1 = length (tl l)")
      case True
      then show "\<not> ordered_zero_collapsible (tl l) {{}}"
        using not_cone_peak_cc_empty ordered_zero_collapsible.simps(2) by blast
    next
      case False
      show "\<not> ordered_zero_collapsible (tl l) {{}}"
      proof (rule Suc.hyps(1))
        show "x = length (tl l)" using Suc.hyps (2) by simp
        show "1 < length (tl l)" using False Suc.prems by simp
      qed
    qed
    ultimately show "\<not> ordered_zero_collapsible l {{}}" 
      using ordered_zero_collapsible.simps (3) [OF Suc.prems(1), of "{{}}"] by simp
  qed
qed

text\<open>A cone over a vertex @{term v} is @{term ordered_zero_collapsible}.\<close>

lemma cone_is_ordered_zero_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and v: "l = v # l'" and d: "distinct l"
    and c: "cone_peak (set l) K v" shows "ordered_zero_collapsible l K"
proof -
  from v have ll: "0 < length l" by simp
  consider (l0) "0 = length l" | (l1) "1 = length l" | (lg1) "1 < length l" by linarith
  then show ?thesis
  proof (cases)
    case l0
    show ?thesis using l0 ll by simp
  next
    case l1
    show ?thesis using ordered_zero_collapsible.simps(2) [OF l1] c v by simp
  next
    case lg1
    show ?thesis using ordered_zero_collapsible.simps(3) [OF lg1] c v by simp
  qed
qed

function ordered_m_collapsible :: "nat \<Rightarrow> nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_m_collapsible m l K = False"
  | "0 < length l \<Longrightarrow> 0 = m \<Longrightarrow> ordered_m_collapsible m l K = ordered_zero_collapsible l K"
  | "0 < length l \<Longrightarrow> 0 < m \<Longrightarrow> ordered_m_collapsible m l K = ((cone_peak (set l) K (hd l))
      | (ordered_m_collapsible m (tl l) (cost (hd l) (set l) K) \<and>
         ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)))"
  by (auto+)
termination by (relation "Wellfounded.measure (\<lambda>(m,l,K). length l)", auto)

lemma ordered_m_collapsible_cc_empty: assumes l: "0 < length l" shows "ordered_m_collapsible m l {}"
  using l
  by (metis cone_peak_cc_empty neq0_conv ordered_m_collapsible.simps(1,2,3) ordered_zero_collapsible_cc_empty)

lemma ordered_m_collapsible_empty: "\<not> ordered_m_collapsible m [] {{}}" by simp

lemma not_ordered_m_collapsible_not_empty:
  assumes l0: "0 < length l" shows "\<not> ordered_m_collapsible m l {{}}"
proof (cases "m = 0")
  case True
  thus ?thesis 
    using ordered_m_collapsible.simps (2) [OF l0, of 0 "{{}}"]
    using l0 not_ordered_zero_collapsible_not_empty by blast
next
  case False hence m0: "0 < m" by simp
  show ?thesis
  using l0 proof (induct "length l" arbitrary: l)
  case 0
  then have False by simp thus ?case by (rule ccontr)
next
  case (Suc n)
  hence sm: "0 < length l" by simp
  have le: "link_ext (hd l) (set l) {{}} = {}" using l0 unfolding link_ext_def powerset_def by auto
  have c: "cost (hd l) (set l) {{}} = {{}}" using l0 unfolding link_ext_def powerset_def by auto
  show ?case
  proof (cases "tl l = []")
    case True
    show ?thesis
      using ordered_m_collapsible.simps (3) [OF sm m0, of "{{}}"] 
      unfolding c
      using True not_cone_peak_cc_empty ordered_m_collapsible.simps(1) by blast
  next
    case False
    show ?thesis
      using ordered_m_collapsible.simps (3) [OF sm m0, of "{{}}"] 
      unfolding c
      using False not_cone_peak_cc_empty ordered_m_collapsible.simps(1) Suc.hyps by simp
    qed
  qed
qed

text\<open>A cone over a vertex @{term v} is @{term ordered_m_collapsible}.\<close>

lemma cone_is_ordered_m_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and v: "l = v # l'" and d: "distinct l"
    and c: "cone_peak (set l) K v" shows "ordered_m_collapsible n l K"
proof -
  from v have ll: "0 < length l" by simp
  show ?thesis
  proof (induct n)
    case 0
    have "ordered_zero_collapsible l K"
      by (rule cone_is_ordered_zero_collapsible, intro K, rule v, rule d, rule c)
    then show ?case using ordered_m_collapsible.simps(2) [OF ll, of n K]
      using ll ordered_m_collapsible.simps(2) by blast
  next
    case (Suc n)
    show ?case using ordered_m_collapsible.simps(2) [OF ll, of "Suc n" K] using c v by simp
  qed
qed

text\<open>For sets of vertexes of cardinality less or equal to @{term "2::nat"}, the three previous
  definitions are equivalent.\<close>

lemma cs_card_leq_2: assumes K: "K \<subseteq> powerset V" and c: "V = {v1,v2}" and v1v2: "v1 \<noteq> v2" 
    and sc: "closed_subset K"
  shows "K = {} \<or> K = {{}} \<or> K = {{},{v1}} \<or> K = {{},{v2}} \<or> K = {{},{v1},{v2}} \<or> K = {{},{v1},{v2},{v1,v2}}"
proof -
  have pV: "powerset V = {{v1,v2},{v1},{v2},{}}" using c unfolding powerset_def by auto
  thus ?thesis using K sc unfolding closed_subset_def
    by (smt (verit, ccfv_threshold) empty_subsetI insert_commute insert_subset subset_antisym subset_insert subset_insertI)
qed

lemma ordered_zero_collapsible_ordered_one_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_zero_collapsible l K"
  shows "ordered_m_collapsible 1 l K"
proof -
  consider (l0) "0 = length l" | (l1) "1 = length l" | (lg1) "1 < length l" by linarith
  then show ?thesis
  proof (cases)
    case l0
    then show ?thesis using ordered_m_collapsible.simps (1) c by simp
  next
    case l1 hence l: "0 < length l" by auto
    show ?thesis
      using ordered_m_collapsible.simps (3) [OF l]
      using ordered_zero_collapsible.simps (2) [OF l1]
      using c less_one by presburger
  next
    case lg1 hence l: "0 < length l" by auto
    show ?thesis
      using K c d lg1 proof (induct "length l" arbitrary: l K rule: less_induct)
      case less
      from less.prems (4) have l1: "1 < length l" and l0: "0 < length l" by auto
      from ordered_zero_collapsible.simps (3) [OF l1, of K] and less.prems (2)
      have ei: "(cone_peak (set l) K (hd l) \<or>
        ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
          cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l)))" by simp
      show ?case
      proof (cases "length l \<le> 2")
        case False note l2 = False
        show ?thesis
        proof (cases "cone_peak (set l) K (hd l)")
          case True
          show ?thesis using ordered_m_collapsible.simps (3) [OF l0, of "1"] using True by simp
        next
          case False
          hence cost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" 
            and link: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))" 
            using ei False by simp_all
          have "ordered_m_collapsible 1 (tl l) (cost (hd l) (set l) K)"
          proof (rule less.hyps)
            show "length (tl l) < length l" using l0 by simp
            show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
              using less.prems (1) l0 unfolding powerset_def cost_def
              by (smt (verit, del_insts) Diff_insert_absorb insert_absorb length_greater_0_conv list.exhaust_sel list.simps(15) mem_Collect_eq subset_iff)
            show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using cost by simp
            show "distinct (tl l)" by (simp add: distinct_tl less.prems(3))
            show "1 < length (tl l)" using l2 by simp
          qed
          moreover have "ordered_m_collapsible 0 (tl l) (link_ext (hd l) (set l) K)"
          proof (rule cone_is_ordered_m_collapsible [of _ _ "hd (tl l)" "tl (tl l)"])
            have "link_ext (hd l) (set l) K \<subseteq> powerset (set l - {hd l})"
              by (rule link_ext_closed [OF less.prems (1)])
            thus "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
              using l1 less.prems (3)
              by (metis hd_Cons_tl list.size(3) not_less_zero remove1_head set_remove1_eq)
            show "tl l = hd (tl l) # tl (tl l)" using l1
              by (metis diff_less_mono dual_order.refl length_tl list.collapse list.size(3) not_less_zero)
            show "distinct (tl l)" using less.prems (3) by (rule distinct_tl)
            show "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
              using link .
          qed
          ultimately show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0] using l0 by fastforce
        qed
      next
        case True note le2 = True
        show ?thesis
        proof (cases "length l = 1")
          case True hence l0: "0 < length l" and zl: "0 < (1::nat)" by simp_all
          show ?thesis unfolding ordered_m_collapsible.simps(3) [OF l0 zl] 
            using ei True
            unfolding cone_peak_def using l1 l0 ei by linarith
          next
            case False hence l2: "length l = 2" using le2 l0 by linarith
            show ?thesis using l2 ei by auto
        qed
      qed
    qed
  qed
qed

lemma ordered_m_collapsible_0_ordered_m_collapsible_one:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_m_collapsible 0 l K"
  shows "ordered_m_collapsible 1 l K"
proof (cases "l = []")
  case True from c have False using True by simp
  thus ?thesis by force
next
  case False hence l0: "0 < length l" by auto
  show ?thesis
    using c 
    using ordered_m_collapsible.simps (2) [OF l0, of "0"]
    using ordered_m_collapsible.simps (3) [OF l0, of "1"]
    using K d ordered_zero_collapsible_ordered_one_collapsible by blast
qed

lemma ordered_m_collapsible_suc:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_m_collapsible m l K" 
  shows "ordered_m_collapsible (m + 1) l K"
  using c proof (induct m rule: less_induct)
  case (less m)
  note f = less.prems (1)
  show ?case using K d f proof (induct "length l" arbitrary: l K m rule: less_induct)
    case less
    show ?case
    proof (cases "l = []")
      case True have False using c True
        using less.prems(3) ordered_m_collapsible.simps(1) by blast
      thus ?thesis using ordered_m_collapsible.simps (1) [OF True, of "m + 1"] by simp
    next
      case False hence l0: "0 < length l" by auto
      show ?thesis
      proof (cases "cone_peak (set l) K (hd l)")
        case True thus ?thesis using ordered_m_collapsible.simps (3) [OF l0, of "m + 1"] by simp
      next
        case False note notcone = False
        show ?thesis
        proof (cases "m = 0")
          case False note mn0 = False
          from less.prems (3) and ordered_m_collapsible.simps (3) [OF l0, of m K]
          have cost: "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" 
            and link: "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
            using notcone False by blast+
          have "ordered_m_collapsible (m + 1) (tl l) (cost (hd l) (set l) K)"
          proof (rule less.hyps)
            show "length (tl l) < length l" using l0 by simp
            have "cost (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
              by (rule cost_closed, intro less.prems (1))
            thus "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
              using l0 less.prems (2)
              by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
            show "distinct (tl l)" using distinct_tl [OF less.prems (2)] .
            show "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" using cost .
          qed
          moreover have "ordered_m_collapsible (m - 1 + 1) (tl l) (link_ext (hd l) (set l) K)"
          proof (rule less.hyps)
            show "length (tl l) < length l" using l0 by simp
            have "link_ext (hd l) (set l) K \<subseteq> powerset (set l - {hd l})"
              by (rule link_ext_closed, intro less.prems (1))
            thus "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
              using l0 less.prems (2)
              by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
            show "distinct (tl l)" using distinct_tl [OF less.prems (2)] .
            show "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
              using link .
          qed
        ultimately show ?thesis using mn0 using ordered_m_collapsible.simps (3) [OF l0] by simp
        next
          case True
          show ?thesis using less.prems unfolding True
            using l0 notcone ordered_m_collapsible.simps(2)
            by (metis add_cancel_left_left ordered_m_collapsible_0_ordered_m_collapsible_one)
        qed
      qed
    qed
  qed
qed

lemma ordered_zero_collapsible_ordered_non_evasive:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_zero_collapsible l K"
  shows "ordered_non_evasive l K"
using K c d proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  show ?case
  proof (cases "l = []")
    case True have False using less.prems (2) True by simp
    thus ?thesis by simp
  next
    case False
    hence l0: "0 < length l" by auto
    show ?thesis
    proof (cases "1 = length l")
      case True
      from less.prems (2) and ordered_zero_collapsible.simps (2) [OF True]
      have ei: "cone_peak (set l) K (hd l)" by simp
      thus ?thesis using ordered_non_evasive.simps (2) [OF l0] by simp
    next
      case False hence l2: "2 \<le> length l" using l0 by linarith
      hence tl_ne: "[] \<noteq> tl l" using False l0
        by (metis One_nat_def Suc_pred length_tl list.size(3))
      show ?thesis
      proof (cases "cone_peak (set l) K (hd l)")
        case True
        show ?thesis using ordered_non_evasive.simps (2) [OF l0] using True by simp
       next
        case False
        hence cost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" 
          and link: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
          using l2 using less.prems (2) by simp_all
        have "ordered_non_evasive (tl l) (cost (hd l) (set l) K)"
        proof (rule less.hyps)
          show "length (tl l) < length l" using l0 by simp
          have "cost (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
            by (rule cost_closed, intro less.prems (1))
          thus "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
            using l0 less.prems (3)
            by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
          show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using cost by simp
          show "distinct (tl l)" by (simp add: distinct_tl less.prems(3))
        qed
        moreover have "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)"
        proof (rule cone_is_one [of _ _ "hd (tl l)"])
          have "link_ext (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
            by (rule link_ext_closed, intro less.prems (1))
          thus "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
            using l0 less.prems(3)
            by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
          show "hd (tl l) \<in> set (tl l)" using tl_ne by simp
          show "distinct (tl l)" using less.prems (3) by (rule distinct_tl)
          show "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
            using link .
      qed
      ultimately show ?thesis 
        unfolding ordered_m_collapsible.simps (2) [OF l0] using l0 by fastforce
      qed
    qed
  qed
qed

lemma ordered_m_collapsible_ordered_non_evasive:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l" and c: "ordered_m_collapsible m l K" 
  shows "ordered_non_evasive l K"
  using c proof (induct m rule: less_induct)
  case (less m)
  note f = less.prems (1)
  show ?case using K d f proof (induct "length l" arbitrary: l K m rule: less_induct)
    case less
    show ?case
    proof (cases "l = []")
      case True have False using less.prems (3) True by simp
      thus ?thesis by simp
    next
      case False
      hence l0: "0 < length l" by auto
      show ?thesis
      proof (cases "cone_peak (set l) K (hd l)")
        case True thus ?thesis using ordered_non_evasive.simps (2) [OF l0] by simp
      next
        case False note notcone = False
        show ?thesis
        proof (cases "m = 0")
          case False note mn0 = False
          from less.prems (3) and ordered_m_collapsible.simps (3) [OF l0, of m K]
          have cost: "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" 
            and link: "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
          using notcone False by blast+
          have "ordered_non_evasive (tl l) (cost (hd l) (set l) K)"
          proof (rule less.hyps)
            show "length (tl l) < length l" using l0 by simp
            have "cost (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
              by (rule cost_closed, intro less.prems (1))
            thus "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
              using l0 less.prems (2)
              by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
          show "distinct (tl l)" using distinct_tl [OF less.prems (2)] .
          show "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" using cost .
        qed
        moreover have "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)"
        proof (rule less.hyps)
          show "length (tl l) < length l" using l0 by simp
          have "link_ext (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
            by (rule link_ext_closed, intro less.prems (1))
          thus "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
            using l0 less.prems (2)
            by (metis length_greater_0_conv  list.collapse remove1_head set_remove1_eq)
          show "distinct (tl l)" using distinct_tl [OF less.prems (2)] .
          show "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
            using link .
        qed
        ultimately show ?thesis using mn0 using ordered_non_evasive.simps (2) [OF l0] by simp
      next
        case True
        show ?thesis using less.prems unfolding True
          using l0 notcone ordered_m_collapsible.simps(2)
          using ordered_zero_collapsible_ordered_non_evasive by blast
        qed
      qed
    qed
  qed
qed

lemma ordered_non_evasive_ordered_m_collapsible_length:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l" and c: "ordered_non_evasive l K"
  shows "ordered_m_collapsible (length l) l K"
  using K d c proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  show ?case
  proof (cases "[] = l")
    case True have False using less.prems (3) True by simp
    thus ?thesis by simp
  next
    case False
    hence l0: "0 < length l" by auto
    show ?thesis
    proof (cases "cone_peak (set l) K (hd l)")
      case True
      show ?thesis using ordered_m_collapsible.simps (3) [OF l0, of "length l", of K]
      using True l0 by blast
    next
      case False
      from less.prems (3)
      have cost: "ordered_non_evasive (tl l) (cost (hd l) (set l) K)" and
        link: "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)" 
      using ordered_non_evasive.simps (2) [OF l0, of K] False by simp_all
    have cost_minus_one: "ordered_m_collapsible (length (tl l)) (tl l) (cost (hd l) (set l) K)"
    proof (rule less.hyps)
      show "length (tl l) < length l" using l0 by simp
      have "cost (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
        by (rule cost_closed, intro less.prems (1))
      thus "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using less.prems (2) l0
        by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
      show "distinct (tl l)"
        using distinct_tl less.prems(2) by auto
      show "ordered_non_evasive (tl l) (cost (hd l) (set l) K)"
        using less.prems (3) ordered_non_evasive.simps (2) [OF l0, of K] False by simp
    qed
    have cost: "ordered_m_collapsible (length (tl l) + 1) (tl l) (cost (hd l) (set l) K)"
    proof (rule ordered_m_collapsible_suc)
      have "cost (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
        by (rule cost_closed, intro less.prems (1))
      thus "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        using less.prems (2) l0
        by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
      show "distinct (tl l)"
        using distinct_tl less.prems(2) by auto
      show "ordered_m_collapsible (length (tl l)) (tl l) (cost (hd l) (set l) K)"
        using cost_minus_one .
    qed
    moreover have link: "ordered_m_collapsible (length (tl l)) (tl l) (link_ext (hd l) (set l) K)"
    proof (rule less.hyps)
      show "length (tl l) < length l" using l0 by simp
      have "link_ext (hd l) (set l) K \<subseteq> powerset (set l - {hd l})" 
        by(rule link_ext_closed, intro less.prems (1)) 
      thus "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using less.prems (2) l0
        by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
      show "distinct (tl l)"
        using distinct_tl less.prems(2) by auto
      show "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)"
        using less.prems (3) ordered_non_evasive.simps (2) [OF l0, of K] False by simp
    qed
    ultimately show ?thesis using ordered_m_collapsible.simps (3) [OF l0, of "length l", of K] l0
      by simp
    qed
  qed
qed

corollary ordered_non_evasive_ordered_m_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_non_evasive l K"
  shows "\<exists>m. ordered_m_collapsible m l K"
  by (rule exI [of _ "length l"], rule ordered_non_evasive_ordered_m_collapsible_length [OF K d c])

lemma not_cone_outer_vertex_insert:
  assumes K: "K \<subseteq> powerset V" and v: "v \<in> V" and w: "w \<notin> V" and nc: "\<not> cone_peak V K v"
  shows "\<not> cone_peak (insert w V) K v"
proof (rule)
  assume c: "cone_peak (insert w V) K v"
  then obtain B where B: "B \<subseteq> powerset (insert w V - {v})" and Kd: "K = B \<union> {s. \<exists>b\<in>B. s = insert v b}" 
    unfolding cone_peak_def by auto
  from K and w and B and Kd have "B \<subseteq> powerset (V - {v})" unfolding powerset_def by auto
  with nc and Kd and v show False unfolding cone_peak_def by auto
qed

definition vertex_of_simpl_complex :: "nat set set \<Rightarrow> nat set"
  where "vertex_of_simpl_complex K = {v. {v} \<in> K}"

lemma "vertex_of_simpl_complex {} = {}" unfolding vertex_of_simpl_complex_def by simp

lemma "vertex_of_simpl_complex {{}} = {}" unfolding vertex_of_simpl_complex_def by simp

lemma "vertex_of_simpl_complex {{v}} = {v}" unfolding vertex_of_simpl_complex_def by simp

text\<open>Beware that when we are dealing with subsets not closed by subset relation
    the previous definition does not work nicely:\<close>

lemma assumes v: "v \<noteq> w" shows "vertex_of_simpl_complex {{v,w}} = {}" 
  using v unfolding vertex_of_simpl_complex_def by simp

lemma not_cone_outer_vertex: assumes v: "v \<notin> (set l)"
  shows "\<not> cone_peak (set l) K v"
  using v unfolding cone_peak_def by simp

lemma not_cone_outer_vertex_simpl_complex: 
  assumes v: "v \<notin> vertex_of_simpl_complex K"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" and Kne: "K \<noteq> {}"
  shows "\<not> cone_peak (set l) K v"
proof (rule ccontr, simp)
  assume c: "cone_peak (set l) K v"
  hence "{v} \<in> K" using Kne K cs unfolding powerset_def cone_peak_def closed_subset_def
    by (smt (verit, del_insts) Un_iff empty_subsetI ex_in_conv insert_mono mem_Collect_eq)
  thus False using v unfolding vertex_of_simpl_complex_def by simp
qed

lemma ordered_m_collapsible_swap:
  assumes v: "v \<notin> vertex_of_simpl_complex K" and l: "l \<noteq> []"
    and d: "distinct l" and vnl: "v \<notin> set l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
    and o: "ordered_m_collapsible m (v # l) K" and m: "0 < m"
  shows "ordered_m_collapsible m (hd l # v # tl l) K"
proof (cases "tl l = []")
  case True note tl = True
    from l and tl have hdl: "l = [hd l]" using list.collapse by fastforce
  hence sl: "set l = {hd l}" by (metis empty_set list.simps(15))
  consider (ke) "K = {}" | (kee) "K = {{}}" | (kne) "K = {{hd l}, {}}"
  proof -
    from sl have "K = {} | K = {{}} | K = {{hd l}, {}}"
      using powerset_singleton_cases [of K "hd l"]
      using K and cs
      unfolding powerset_def closed_subset_def
      by (metis insertCI insert_absorb insert_commute subset_insertI)
    thus ?thesis using ke kee kne by fastforce
  qed
  then show ?thesis
  proof (cases)
    case ke
    then show ?thesis
      by (simp add: ordered_m_collapsible_cc_empty)
  next
    case kne
    have l1: "0 < length (hd l # v # tl l)" using l by simp
    have "cone_peak (set (hd l # v # tl l)) K (hd (hd l # v # tl l))"
      unfolding kne list.sel (1,3) cone_peak_def powerset_def
      proof (intro conjI)
         show "hd l \<in> set (hd l # v # tl l)" by simp
         show "\<exists>B\<subseteq>Pow (set (hd l # v # tl l) - {hd l}). {{hd l}, {}} = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
           by (intro exI [of _ "{{}}"], simp)
      qed
    thus ?thesis unfolding ordered_m_collapsible.simps (3) [OF l1 m] by simp
  next
    case kee
    have "ordered_non_evasive (v # l) {{}}"
    proof (rule ordered_m_collapsible_ordered_non_evasive [of _ _ m])
      show "{{}} \<subseteq> powerset (set (v # l))" unfolding powerset_def by simp
      show "distinct (v # l)" using vnl d by simp
      show "ordered_m_collapsible m (v # l) {{}}" using kee o by blast
    qed
    moreover have "\<not> ordered_non_evasive (v # l) {{}}" using ordered_non_evasive_empty .
    ultimately have False by simp
    thus ?thesis by (rule ccontr)
  qed
next
  case False note tl = False
  show ?thesis
  proof (cases "K = {}")
    case True show ?thesis unfolding True
      using ordered_m_collapsible_cc_empty by blast
  next
    case False note Kne = False
    consider (cp) "cone_peak (set (v # l)) K v" | (cnp) "\<not> cone_peak (set (v # l)) K v" by auto
    then show ?thesis
    proof (cases)
      case cp
      have cnp_v: "\<not> cone_peak (set (v # l)) K v"
      proof (rule not_cone_outer_vertex_simpl_complex)
        show "v \<notin> vertex_of_simpl_complex K" using v.
        show "K \<subseteq> powerset (set (v # l))" using K unfolding powerset_def by auto
        show "closed_subset K" using cs .
        show "K \<noteq> {}" using Kne .
      qed
      with cp have False by simp
      thus ?thesis by simp
    next
      case cnp
      have lvl: "0 < length (v # l)" using l tl by simp
      have llvl: "0 < length (hd l # v # tl l)" using l tl by simp
      have ll: "0 < length l" using l tl by simp
      have ltl: "0 < length (tl l)" using tl by blast
      have lvtl: "0 < length (v # tl l)" using l tl by (simp add: Nitpick.size_list_simp(2))
      have lvtl1: "1 < length (v # tl l)" using tl
        by (metis One_nat_def Suc_less_eq length_Cons length_greater_0_conv)
      have cK: "cost v (set l) K = K" and clK: "cost v (set (v # l)) K = K"
        using vnl K
        unfolding cost_def powerset_def by auto
      from o and cnp have ozc_c: "ordered_m_collapsible m l (cost v (set (v # l)) K)"
        and cp_l: "ordered_m_collapsible (m - 1) (tl (v # l)) (link_ext (hd (v # l)) (set (v # l)) K)"
        using ordered_m_collapsible.simps (3) [OF lvl m, of K] by simp_all
      from ozc_c have ozc_K: "ordered_m_collapsible m l K" using clK by simp
      show ?thesis
      proof (cases "cone_peak (set l) K (hd l)")
        case True
        have "cone_peak (set (hd l # v # tl l)) K (hd l)"
        proof (unfold cone_peak_def powerset_def, intro conjI)
          show "hd l \<in> set (hd l # v # tl l)" by simp
          from True obtain B where B_subset: "B \<subseteq> Pow (set l - {hd l})" and KB: "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
            unfolding cone_peak_def powerset_def by auto
          show "\<exists>B\<subseteq>Pow (set (hd l # v # tl l) - {hd l}). K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
          proof (rule exI [of _ B], intro conjI)
            show "B \<subseteq> Pow (set (hd l # v # tl l) - {hd l})"
              using B_subset l vnl
              by (metis (no_types, lifting) Pow_mono d distinct.simps(2) distinct_length_2_or_more list.collapse remove1_head set_remove1_eq
                set_subset_Cons subset_trans) (*TODO: Unusually slow; review*)
            show "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}" using KB by simp
          qed
        qed
        then show ?thesis using ordered_m_collapsible.simps (3) [OF llvl m] by simp
      next
        case False
        from o ozc_K
        have ozc_tl: "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)"
          and cp: "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
          unfolding ordered_m_collapsible.simps (3) [OF ll m] using False by simp_all
        have "ordered_m_collapsible m (v # tl l) (cost (hd l) (set (hd l # v # tl l)) K)"
        proof -
          have "ordered_m_collapsible m (tl (v # tl l)) (cost (hd (v # tl l)) (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K))"
          proof -
            have "(cost v (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K)) = cost (hd l) (set l) K"
              using vnl l tl K d unfolding cost_def powerset_def apply auto
               apply (metis in_mono list.exhaust_sel remove1_head set_remove1_eq)
              by (metis list.exhaust_sel remove1_head set_remove1_eq subset_iff)
          thus ?thesis using ozc_tl by simp
        qed
        moreover have "ordered_m_collapsible (m - 1) (tl (v # tl l)) (link_ext (hd (v # tl l)) (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K))"
        proof -
          have "(link_ext (hd (v # tl l)) (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K)) = {}"
            using vnl l tl K d unfolding link_ext_def powerset_def cost_def by auto
          thus ?thesis using tl l d
            by (metis cone_is_ordered_m_collapsible cost_empty distinct.simps(2) empty_subsetI link_ext_empty list.exhaust list.sel(3)
                list.set_intros(1) proposition_1)
        qed
        ultimately show ?thesis
          using ordered_m_collapsible.simps (3) [OF lvtl m, of "(cost (hd l) (set (hd l # v # tl l)) K)"] by simp
      qed
      moreover have "ordered_m_collapsible (m - 1) (tl (hd l # v # tl l)) (link_ext (hd (hd l # v # tl l)) (set (hd l # v # tl l)) K)"
      proof (cases "cone_peak (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K) (hd (v # tl l))")
        case True note cpl = True
        show ?thesis
        proof (cases "m = 1")
          case False
          have m10: "0 < m - 1" using False m by simp
          show ?thesis using True
            using ordered_m_collapsible.simps (3) [OF lvtl m10 , of "(link_ext (hd l) (set (hd l # v # tl l)) K)"] by simp
        next
          case True
          have m10: "0 = m - 1" using m True by simp
          show ?thesis 
            using cpl ordered_m_collapsible.simps (2) [OF lvtl m10, of "(link_ext (hd l) (set (hd l # v # tl l)) K)"]
            unfolding ordered_zero_collapsible.simps (3) [OF lvtl1] by simp
        qed
      next
        case False note ncpl = False
        show ?thesis
        proof (cases "1 = m")
          case False
          hence m10: "0 < m - 1" using m by simp
          have "ordered_m_collapsible (m - 1) (tl (v # tl l)) (cost (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K))"
          proof -
            have cl: "(cost (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) = 
              (link_ext (hd l) (set (hd l # v # tl l)) K)"
             using vnl l d K
             unfolding cost_def link_ext_def powerset_def by auto
            show ?thesis
            proof -
             have ll: "(link_ext (hd l) (set l) K) = (link_ext (hd l) (set (hd l # v # tl l)) K)"
               using vnl K l
               unfolding link_ext_def powerset_def
               by auto (metis list.exhaust_sel set_ConsD subset_iff)
             show ?thesis using cp unfolding cl unfolding ll unfolding list.sel (1,3) by simp
           qed
         qed
         moreover have "ordered_m_collapsible (m - 1 - 1) (tl (v # tl l))
          (link_ext (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K))"
         proof -
           have "(link_ext (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) = {}"
             using vnl K unfolding link_ext_def powerset_def by auto
           thus ?thesis
             using tl ordered_m_collapsible_cc_empty by simp
         qed
        ultimately show ?thesis
          using ordered_m_collapsible.simps (3) [OF lvtl m10 , of "(link_ext (hd l) (set (hd l # v # tl l)) K)"] by simp
      next
        case True
        hence m10: "0 = m - 1" using m by simp
        have "ordered_zero_collapsible (tl l) (cost v (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K))"
        proof -
          have cl: "(cost v (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) = 
          (link_ext (hd l) (set (hd l # v # tl l)) K)"
             using vnl l d K
             unfolding cost_def link_ext_def powerset_def by auto
          have ll: "(link_ext (hd l) (set l) K) = (link_ext (hd l) (set (hd l # v # tl l)) K)"
            using vnl K l
            unfolding link_ext_def powerset_def by auto (metis list.exhaust_sel set_ConsD subset_iff)
          show ?thesis unfolding cl unfolding ll [symmetric] 
            using cp using ordered_m_collapsible.simps (2) [OF ltl m10] by simp
        qed
        moreover have "cone_peak (set (tl l)) (link_ext v (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) (hd (tl l))" 
        proof -
          have "(link_ext (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) = {}"
             using vnl K unfolding link_ext_def powerset_def by auto
           thus ?thesis
             using cone_peak_cc_empty [OF tl] by simp
       qed
       ultimately show ?thesis
          unfolding list.sel (1,3)
           unfolding ordered_m_collapsible.simps (2) [OF lvtl m10]
           unfolding ordered_zero_collapsible.simps (3) [OF lvtl1] by simp
       qed
      qed
      ultimately show ?thesis 
        using ordered_m_collapsible.simps (3) [OF llvl m, of K] by simp
      qed
    qed
  qed
qed

lemma ordered_m_collapsible_swap_rev: 
  assumes v: "v \<notin> vertex_of_simpl_complex K" and l: "l \<noteq> []"
    and d: "distinct l" and vnl: "v \<notin> set l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
    and o: "ordered_m_collapsible m (hd l # v # tl l) K" and m: "0 < m"
  shows "ordered_m_collapsible m (v # l) K"
proof (cases "tl l = []")
  case True note tl = True
    from l and tl have hdl: "l = [hd l]" using list.collapse by fastforce
  hence sl: "set l = {hd l}" by (metis empty_set list.simps(15))
  consider (ke) "K = {}" | (kee) "K = {{}}" | (kne) "K = {{hd l}, {}}"
  proof -
    from sl have "K = {} | K = {{}} | K = {{hd l}, {}}"
      using powerset_singleton_cases [of K "hd l"] K cs
      unfolding powerset_def closed_subset_def
      by (metis insertCI insert_absorb insert_commute subset_insertI)
    thus ?thesis using ke kee kne by fastforce
  qed
  then show ?thesis
  proof (cases)
    case ke
    thus ?thesis by (simp add: ordered_m_collapsible_cc_empty)
  next
    case kne
    have l1: "0 < length l" using l by simp
    have l2: "0 < length (v # l)" using l by simp
    have c: "cost (hd (v # l)) (set (v # l)) K = K"
      using vnl unfolding kne
      unfolding cost_def powerset_def using v unfolding vertex_of_simpl_complex_def using sl by auto
    have le: "link_ext (hd (v # l)) (set (v # l)) K = {}"
      using vnl unfolding kne
      unfolding link_ext_def powerset_def using v unfolding vertex_of_simpl_complex_def using sl by auto
    have cp: "cone_peak (set l) K (hd l)"
    proof (unfold kne cone_peak_def powerset_def, intro conjI)
      show "\<exists>B\<subseteq>Pow (set l - {hd l}). {{hd l}, {}} = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
           by (intro exI [of _ "{{}}"], simp)
      show "hd l \<in> set l" using l hd_in_set [] by auto
    qed
    have "ordered_m_collapsible m (tl (v # l)) (cost (hd (v # l)) (set (v # l)) K)"
      unfolding c unfolding list.sel using ordered_m_collapsible.simps (3) [OF l1 m, of K]
      using cp by simp
    moreover have "ordered_m_collapsible (m - 1) (tl (v # l)) (link_ext (hd (v # l)) (set (v # l)) K)"
      unfolding le unfolding list.sel using m using l ordered_m_collapsible_cc_empty by simp
    ultimately show ?thesis using ordered_m_collapsible.simps (3) [OF l2 m] by simp
  next
    case kee
    have "ordered_non_evasive (hd l # v # tl l) {{}}"
    proof (rule ordered_m_collapsible_ordered_non_evasive [of _ _ m])
      show "{{}} \<subseteq> powerset (set (hd l # v # tl l))" unfolding powerset_def by simp
      show "distinct (hd l # v # tl l)" using vnl d l tl by auto
      show "ordered_m_collapsible m (hd l # v # tl l) {{}}" using kee o by blast
    qed
    moreover have "\<not> ordered_non_evasive (hd l # v # tl l) {{}}" using ordered_non_evasive_empty .
    ultimately have False by simp
    thus ?thesis by (rule ccontr)
  qed
next
  case False note tl = False
  show ?thesis
  proof (cases "K = {}")
    case True show ?thesis unfolding True
      using ordered_m_collapsible_cc_empty by blast
  next
    case False note Kne = False
    consider (cp) "cone_peak (set (hd l # v # tl l)) K v" | (cnp) "\<not> cone_peak (set (hd l # v # tl l)) K v" by auto
    then show ?thesis
    proof (cases)
      case cp
      have False
      proof -
        have Kv: "K \<subseteq> powerset (set (hd l # v # tl l))"
          using K l using Pow_mono [of "set l" "set (hd l # v # tl l)"]
          unfolding powerset_def
          by (metis hd_Cons_tl insert_commute l list.simps(15) order.trans subset_insertI)
        have "\<not> cone_peak (set (hd l # v # tl l)) K v" 
          by (rule not_cone_outer_vertex_simpl_complex, intro v, intro Kv, intro cs, intro Kne)
        with cp show False by fast
      qed
      thus ?thesis by simp
    next
      case cnp
      have lvl: "0 < length (v # l)" and ll: "0 < length l" and vtl: "0 < length (v # tl l)" 
        and lvtl: "0 < length (hd l # v # tl l)" using l by simp_all
      have vtl1: "1 < length (v # tl l)" and tl0: "0 < length (tl l)" 
        using length_Suc_conv tl by fastforce+
      have "ordered_m_collapsible m (tl (v # l)) (cost (hd (v # l)) (set (v # l)) K)"
      proof -
        have c: "cost (hd (v # l)) (set (v # l)) K = K"
          using K unfolding cost_def powerset_def using vnl by auto
        show ?thesis 
          unfolding c unfolding list.sel
        proof -
          show "ordered_m_collapsible m l K"
          proof (cases "cone_peak (set l) K (hd l)")
            case True
            then show ?thesis using ordered_m_collapsible.simps (3) [OF ll m, of K] by simp
          next
            case False
            have ncp_lvl: "\<not> cone_peak (set (hd l # v # tl l)) K (hd (hd l # v # tl l))"
            proof (rule ccontr, simp, unfold cone_peak_def powerset_def)
              assume "hd l \<in> insert (hd l) (insert v (set (tl l))) \<and>
                (\<exists>B\<subseteq>Pow (insert (hd l) (insert v (set (tl l))) - {hd l}). K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}) "
              then obtain B where "B\<subseteq>Pow (set (hd l # v # tl l) - {hd (hd l # v # tl l)})"
                and "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd (hd l # v # tl l)) b}" by auto
              then have "B\<subseteq>Pow (set l - {hd l})" and "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}" 
                using l vnl K unfolding powerset_def by auto
              thus False using False l unfolding cone_peak_def powerset_def by auto
            qed
            have ncp_cost: "\<not> cone_peak (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K) v"
            proof (rule not_cone_outer_vertex_simpl_complex)
              show "v \<notin> vertex_of_simpl_complex (cost (hd l) (set (hd l # v # tl l)) K)" 
                using v vnl unfolding vertex_of_simpl_complex_def cost_def powerset_def by simp
              show "cost (hd l) (set (hd l # v # tl l)) K \<subseteq> powerset (set (v # tl l))" 
                using K unfolding cost_def powerset_def by auto
              show "closed_subset (cost (hd l) (set (hd l # v # tl l)) K)" 
                using cs unfolding cost_def powerset_def closed_subset_def by auto
              show "cost (hd l) (set (hd l # v # tl l)) K \<noteq> {}" 
                using Kne unfolding cost_def powerset_def
                using closed_subset_def cs by force
            qed
            have omc_c: "ordered_m_collapsible m (v # tl l) (cost (hd l) (set (hd l # v # tl l)) K)"
                  and omc_l: "ordered_m_collapsible (m - 1) (v # tl l) (link_ext (hd l) (set (hd l # v # tl l)) K)"
              using o ncp_lvl unfolding ordered_m_collapsible.simps (3) [OF lvtl m, of K]
              unfolding list.sel by simp_all
            have "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)"
            proof -
              have "ordered_m_collapsible m (tl l) (cost v (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K))"
                using omc_c 
                unfolding ordered_m_collapsible.simps (3) [OF vtl m, of ]
                unfolding list.sel using ncp_cost by simp
              moreover have "(cost v (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K)) = (cost (hd l) (set l) K)"
                using vnl K d l
                unfolding cost_def powerset_def apply auto
                apply (metis DiffD1 DiffD2 in_mono list.exhaust_sel set_ConsD singleton_iff)
                by (metis list.exhaust_sel remove1_head set_remove1_eq subset_iff)
              ultimately show ?thesis by simp
            qed
            moreover have "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
            proof (cases "link_ext (hd l) (set l) K = {}")
              case True
              then show ?thesis unfolding True
                using ordered_m_collapsible_cc_empty tl0 by blast
            next
              case False note link_ne = False
              have ncp_link: "\<not> cone_peak (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K) v"
              proof (rule not_cone_outer_vertex_simpl_complex)
                show "v \<notin> vertex_of_simpl_complex (link_ext (hd l) (set (hd l # v # tl l)) K)" 
                  using K v vnl unfolding vertex_of_simpl_complex_def link_ext_def powerset_def by auto
                show "link_ext (hd l) (set (hd l # v # tl l)) K \<subseteq> powerset (set (v # tl l))" 
                  using K unfolding link_ext_def powerset_def by auto
                show "closed_subset (link_ext (hd l) (set (hd l # v # tl l)) K)"
                  using cs K vnl unfolding link_ext_def powerset_def closed_subset_def 
                  by auto (meson insert_mono)
                show "link_ext (hd l) (set (hd l # v # tl l)) K \<noteq> {}" 
                  using Kne link_ne cs unfolding link_ext_def powerset_def closed_subset_def
                  by auto
              qed              
              have c_eq_l: "cost (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K) = link_ext (hd l) (set (hd l # v # tl l)) K"
                using vnl K d l
                unfolding link_ext_def cost_def powerset_def by auto
              have l_eq_l: "link_ext (hd l) (set (hd l # v # tl l)) K = link_ext (hd l) (set l) K"
                using vnl K unfolding link_ext_def powerset_def
                by auto (metis l list.exhaust_sel set_ConsD subset_iff)
              show ?thesis
              proof (cases "0 < m - 1")
              case True
              from omc_l have "ordered_m_collapsible (m - 1) (tl (v # tl l)) (cost (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K))"
                unfolding ordered_m_collapsible.simps (3) [OF vtl True]
                unfolding list.sel using ncp_link by simp
              thus ?thesis using c_eq_l l_eq_l by simp
            next
              case False hence m1: "0 = m - 1" by simp
              have "ordered_zero_collapsible (tl l) (cost v (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K))"
                using omc_l unfolding ordered_m_collapsible.simps (2) [OF vtl m1]
                unfolding ordered_zero_collapsible.simps (3) [OF vtl1] unfolding list.sel
                using ncp_link by simp
              thus ?thesis using ordered_m_collapsible.simps (2) [OF tl0 m1] c_eq_l l_eq_l by simp
            qed
          qed
          ultimately show ?thesis using ordered_m_collapsible.simps (3) [OF ll m, of K] by simp
        qed
      qed
    qed
    moreover have "ordered_m_collapsible (m - 1) (tl (v # l)) (link_ext (hd (v # l)) (set (v # l)) K)"
    proof -
      have le: "link_ext (hd (v # l)) (set (v # l)) K = {}"
        using K unfolding link_ext_def powerset_def using vnl by auto
      show ?thesis unfolding le unfolding list.sel
        using ll ordered_m_collapsible_cc_empty by blast
      qed
      ultimately show ?thesis using cnp using ordered_m_collapsible.simps (3) [OF lvl m, of K] by simp
    qed
  qed
qed

text\<open>Beware that when we are dealing with subsets not closed by subset relation
    the previous definition does not work nicely:\<close>

text\<open>Lemma 4.1 as stated in our paper in DML. We split it into four different lemmas\<close>

lemma cost_cost_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
  shows "cost (hd l) (set l - {hd (tl l)}) (cost (hd (tl l)) (set l) K) = 
          cost (hd (tl l)) (set l - {hd l}) (cost (hd l) (set l) K)"
  using l d K cs unfolding powerset_def cost_def closed_subset_def by auto

lemma cost_link_ext_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" 
  shows "cost (hd l) (set l - {hd (tl l)}) (link_ext (hd (tl l)) (set l) K) = 
          link_ext (hd (tl l)) (set l - {hd l}) (cost (hd l) (set l) K)"
  using l d K cs unfolding powerset_def cost_def link_ext_def closed_subset_def
  by auto (metis Nitpick.size_list_simp(2) One_nat_def distinct_length_2_or_more list.exhaust_sel not_numeral_le_zero numeral_le_one_iff semiring_norm(69))

lemma link_ext_cost_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" 
  shows "link_ext (hd l) (set l - {hd (tl l)}) (cost (hd (tl l)) (set l) K) = 
          cost (hd (tl l)) (set l - {hd l}) (link_ext (hd l) (set l) K)"
  using l d K cs unfolding powerset_def cost_def link_ext_def closed_subset_def
  by auto (metis Nitpick.size_list_simp(2) One_nat_def distinct_length_2_or_more list.exhaust_sel not_numeral_le_zero numeral_le_one_iff semiring_norm(69))

lemma link_ext_link_ext_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" 
  shows "link_ext (hd l) (set l - {hd (tl l)}) (link_ext (hd (tl l)) (set l) K) = 
          link_ext (hd (tl l)) (set l - {hd l}) (link_ext (hd l) (set l) K)"
  using l d K cs unfolding powerset_def link_ext_def closed_subset_def
  by auto (metis insert_commute)+

text\<open>Lemma 4.2 as stated in our paper in DML\<close>

lemma ordered_m_collapsible_swap_main:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
    and m: "0 < m" 
    and o: "ordered_m_collapsible m l K"
    and ncp: "\<not> cone_peak (set l) K (hd l)"
    and ncp_cost: "\<not> cone_peak (set (tl l)) (cost (hd l) (set l) K) (hd (tl l))"
    and ncp_link: "\<not> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
  shows "ordered_m_collapsible m ((hd (tl l)) # (hd l) # (tl (tl l))) K"
proof -
  have l_ss_c: "link_ext (hd l) (set l) K \<subset> cost (hd l) (set l) K"
    by (metis K closed_subset_link_eq_link_ext cone_peak_cc_empty cone_peak_empty cost_eq_link_ext_cone_peak cs hd_in_set link_subset_cost ncp o
        order_less_le ordered_m_collapsible.simps(1))
  have l_ne: "link_ext (hd l) (set l) K \<noteq> {}"
    by (metis cone_peak_cc_empty length_greater_0_conv m ncp ncp_link o ordered_m_collapsible.simps(1,3))
  have o_m_c: "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" 
    using o ncp
    by (metis length_greater_0_conv m ordered_m_collapsible.simps(1,3))
  have o_m_1_l: "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)" 
    using o ncp
    by (metis length_greater_0_conv m ordered_m_collapsible.simps(1,3))
  have o_m_c_c: "ordered_m_collapsible m (tl (tl l)) (cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
    using o_m_c ncp_cost
    by (metis length_greater_0_conv m ordered_m_collapsible.simps(1,3))
  have o_m_c_l: "ordered_m_collapsible (m - 1) (tl (tl l)) (cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
    using o_m_1_l ncp_link
    by (smt (verit, best) Nitpick.size_list_simp(2) One_nat_def less_numeral_extra(4) ordered_m_collapsible.elims(2,3) ordered_m_collapsible.simps(1,3)
        ordered_zero_collapsible.elims(2))
  have o_m_l_c: "ordered_m_collapsible (m - 1) (tl (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
    using o_m_c ncp_cost
    by (metis length_greater_0_conv m ordered_m_collapsible.simps(1,3))
  have o_m_l_l: "ordered_m_collapsible (m - 1 - 1) (tl (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
    using o_m_1_l ncp_link
    by (smt (verit, del_insts) K add_diff_inverse_nat cancel_comm_monoid_add_class.diff_cancel d diff_add_inverse2 diff_is_0_eq l length_tl less_one nat_1_add_1
        ncp not_gr_zero o order.strict_trans2 ordered_m_collapsible.simps(3) ordered_m_collapsible_suc zero_diff)
  (*have lc_cc_ne: "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subset> cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
    using ncp_cost
    by (metis K closed_subset_cost closed_subset_link_eq_link_ext cost_closed cost_eq_link_ext_cone_peak cs d empty_iff hd_in_set link_subset_cost
        list.collapse list.sel(2) o_m_c_c ordered_m_collapsible.simps(1) psubsetI remove1_head set_remove1_eq)
  have ll_cl_ne: "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subset> cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
    using ncp_link o_m_c_l sorry*)
  have one: "hd (tl l) \<in> set l" using l
    by (metis Nitpick.size_list_simp(2) One_nat_def list.set_sel(1,2) not_numeral_le_zero numeral_le_one_iff semiring_norm(69))
  have two: "hd l \<in> set l" using l
    by (metis hd_in_set list.sel(2) one)
  have three: "set l - {hd (tl l)} = set (hd l # tl (tl l))" 
    using l d apply auto
        apply (metis list.sel(1,3) list.set_cases)
        apply (metis list.set_sel(1) list.size(3) not_numeral_le_zero)
        apply (metis Nitpick.size_list_simp(2) One_nat_def distinct_length_2_or_more list.collapse not_numeral_le_zero numeral_le_one_iff semiring_norm(69))
      apply (metis list.sel(2) list.set_sel(2))
    by (metis distinct.simps(2) empty_iff empty_set list.collapse list.sel(2))
  have four: "set l = set (hd (tl l) # hd l # tl (tl l))" using l three
    by (metis hd_in_set insert_Diff list.collapse list.set_intros(2) list.simps(15) o_m_c_c ordered_m_collapsible.simps(1) tl_Nil)
  have five: "set l - {hd l} = set (tl l)" using l d
    by (metis empty_iff empty_set list.collapse remove1_head set_remove1_eq two)
  show ?thesis
  proof (cases "link_ext (hd (tl l)) (set l) K = {}")
    case True note l_e = True
    hence c_K: "cost (hd (tl l)) (set l) K = K"
      by (metis K Un_empty_left all_not_in_conv closed_subset_def cost_empty cs empty_subsetI link_ext_empty proposition_2 sup_bot_right)
    show ?thesis 
    proof (rule ordered_m_collapsible_swap_rev)
      show f: "hd (tl l) \<notin> vertex_of_simpl_complex K" using l_e
        unfolding link_ext_def vertex_of_simpl_complex_def powerset_def by auto
      show "hd l # tl (tl l) \<noteq> []" by simp
      show "distinct (hd l # tl (tl l))" using d
        by (metis distinct_length_2_or_more distinct_singleton list.collapse tl_Nil)
      show "hd (tl l) \<notin> set (hd l # tl (tl l))" using d l o_m_c
        by (metis distinct.simps(2) distinct_tl l_e l_ne list.collapse ordered_m_collapsible.simps(1) set_ConsD)
      show "K \<subseteq> powerset (set (hd l # tl (tl l)))" using K f cs
        unfolding powerset_def vertex_of_simpl_complex_def closed_subset_def
        by (smt (verit) Diff_insert_absorb \<open>hd (tl l) \<notin> set (hd l # tl (tl l))\<close> c_K cost_closed insert_commute list.exhaust_sel list.simps(15) o_m_c_c
            ordered_m_collapsible.simps(1) powerset_def tl_Nil)
      show "closed_subset K" using cs .
      show "ordered_m_collapsible m (hd (hd l # tl (tl l)) # hd (tl l) # tl (hd l # tl (tl l))) K" using o l
        by (metis list.collapse list.sel(1,3) o_m_c ordered_m_collapsible.simps(1))
      show "0 < m" using m .
    qed
  next
    case False
    have "ordered_m_collapsible m (tl (hd (tl l) # hd l # tl (tl l))) (cost (hd (hd (tl l) # hd l # tl (tl l))) (set (hd (tl l) # hd l # tl (tl l))) K)"
    proof -
      have "ordered_m_collapsible m (hd l # tl (tl l)) (cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K)"
      proof (cases "cone_peak (set (hd (tl l) # hd l # tl (tl l))) (cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K) (hd l)")
        case True
        show ?thesis 
        proof (rule cone_is_ordered_m_collapsible [of _ _ "hd l"])
          show "cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K \<subseteq> powerset (set (hd l # tl (tl l)))"
            using K unfolding cost_def powerset_def by auto
          show "hd l # tl (tl l) = hd l # tl (tl l)" ..
          show "distinct (hd l # tl (tl l))" using d l
            by (metis distinct_length_2_or_more distinct_singleton list.collapse list.sel(2))
          from True obtain B where Bp: "B\<subseteq>powerset (set (hd (tl l) # hd l # tl (tl l)) - {hd l})" 
             and c: "cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}" unfolding cone_peak_def by auto
          show "cone_peak (set (hd l # tl (tl l))) (cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K) (hd l)"
          proof (unfold cone_peak_def, intro conjI)
            show "hd l \<in> set (hd l # tl (tl l))" by simp
            show "\<exists>B\<subseteq>powerset (set (hd l # tl (tl l)) - {hd l}). cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
            proof (intro exI [of _ B], intro conjI)
              show "B \<subseteq> powerset (set (hd l # tl (tl l)) - {hd l})" 
                using Bp c unfolding cost_def powerset_def by auto
              show "cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
                using c .
            qed
          qed
        qed
      next
        case False
        have c_reduce: "cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K) =
                cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
          unfolding list.sel unfolding three [symmetric] four [symmetric] five [symmetric]
            by (rule cost_cost_commute_length_ge2, intro l, intro d, intro K, intro cs)
        have "ordered_m_collapsible m (tl (hd l # tl (tl l)))
          (cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K))"
          unfolding c_reduce
          unfolding list.sel using o_m_c_c .
        moreover have "ordered_m_collapsible (m - 1) (tl (hd l # tl (tl l)))
          (link_ext (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K))" 
          by (metis five four link_ext_cost_commute list.sel(1,3) o_m_c_l o_m_l_c one three two)
        ultimately show ?thesis using ordered_m_collapsible.simps (3) [ of "hd l # tl (tl l)", OF _ m] by simp
      qed
      thus ?thesis by simp
    qed      
    moreover have "ordered_m_collapsible (m - 1) (tl (hd (tl l) # hd l # tl (tl l))) (link_ext (hd (hd (tl l) # hd l # tl (tl l))) (set (hd (tl l) # hd l # tl (tl l))) K)"
    proof (cases "0 = m - 1")
      case True
      have length1: "1 < length (hd l # tl (tl l))" and lengthhdtl0: "0 < length (hd l # tl (tl l))"  
        by (metis length_0_conv length_Suc_conv less_one not_less_eq o_m_l_c ordered_m_collapsible.simps(1)) auto
      hence ltltl0: "0 < length ((tl (tl l)))" by simp
      hence ltl1: "1 < length (tl l)" by simp
      from o_m_1_l have "ordered_zero_collapsible (tl l) (link_ext (hd l) (set l) K)" 
        using ordered_m_collapsible.simps (2) [OF _ True, of "tl l"] by fastforce
      then have ozc: "ordered_zero_collapsible (tl (tl l)) (cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))" 
        and cp: "cone_peak (set (tl (tl l))) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) (hd (tl (tl l)))" 
        using ordered_zero_collapsible.simps (3) [OF ltl1, of "link_ext (hd l) (set l) K"]
        using ncp_link by simp_all
      have "ordered_zero_collapsible (tl (hd l # tl (tl l)))
     (cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K))"
        using ozc unfolding list.sel
        by (metis K True cost_link_ext_commute_length_ge2 cs d five four l ltltl0 o_m_l_c ordered_m_collapsible.simps(2) three)
      moreover have "cone_peak (set (tl (hd l # tl (tl l))))
     (link_ext (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K)) (hd (tl (hd l # tl (tl l))))"
        using cp unfolding list.sel
        by (metis five four link_ext_commute one three two)
      ultimately have "ordered_zero_collapsible (hd l # tl (tl l)) (link_ext (hd (tl l)) (set (hd (tl l) # hd l # tl (tl l))) K)"
        unfolding ordered_zero_collapsible.simps (3) [OF length1] by simp
      thus ?thesis using ordered_m_collapsible.simps (2) [OF _ True] by simp
    next
      case False
      hence m1: "0 < m - 1" using m by linarith
      have "ordered_m_collapsible (m - 1) (tl (tl (hd (tl l) # hd l # tl (tl l))))
      (cost (hd (tl (hd (tl l) # hd l # tl (tl l)))) (set (tl (hd (tl l) # hd l # tl (tl l))))
        (link_ext (hd (hd (tl l) # hd l # tl (tl l))) (set (hd (tl l) # hd l # tl (tl l))) K))"
        by (metis K cost_link_ext_commute_length_ge2 cs d five four l list.sel(1,3) o_m_l_c three)
      moreover have
     "ordered_m_collapsible (m - 1 - 1) (tl (tl (hd (tl l) # hd l # tl (tl l))))
      (link_ext (hd (tl (hd (tl l) # hd l # tl (tl l)))) (set (tl (hd (tl l) # hd l # tl (tl l))))
        (link_ext (hd (hd (tl l) # hd l # tl (tl l))) (set (hd (tl l) # hd l # tl (tl l))) K))"
        by (metis five four link_ext_commute list.sel(1,3) o_m_l_l one three two)
      ultimately show ?thesis
        using ordered_m_collapsible.simps (3) [OF _ m1, of "tl (hd (tl l) # hd l # tl (tl l))" "link_ext (hd (hd (tl l) # hd l # tl (tl l))) (set (hd (tl l) # hd l # tl (tl l))) K"]
        by simp
    qed
    ultimately show ?thesis using ordered_m_collapsible.simps (3) [of "hd (tl l) # hd l # tl (tl l)", OF _ m] by simp
  qed
qed

section\<open>Main Theorem.\<close>

text\<open>Theorem 4.1 as stated in our paper in DML\<close>

(*lemma nat_induct_3 [case_names 0 1 2 Suc, induct type: nat]:
  fixes n
  assumes p0: "P 0" and p1: "P 1" and p2: "P 2" and f: "\<forall>n \<ge> 2. P n \<longrightarrow> P (Suc n)"
  shows "P n"
proof (induct rule: nat_induct)
  case 0
  show ?case using p0 .
next
  case (Suc n)
  then show ?case using p1 p2 f
    by (metis One_nat_def Suc_1 less_2_cases linorder_not_less)
qed*)

lemma nat_induct_3 [case_names 0 1 2 Suc, induct type: nat]:
  fixes n
  assumes p0: "P 0" and p1: "P 1" and p2: "P 2" and f: "\<And>n. n \<ge> 2 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
proof (induct rule: nat_induct)
  case 0
  show ?case using p0 .
next
  case (Suc n)
  then show ?case using p1 p2 f
    by (metis One_nat_def Suc_1 less_2_cases linorder_not_less)
qed

lemma ozc_cost_collapses_link_ext:
  assumes ozc: "ordered_zero_collapsible l K" and d: "distinct l" 
    and lne: "l \<noteq> []"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
  shows "(cost (hd l) (set l) K, link_ext (hd l) (set l) K) \<in> collapses_rtrancl"
using ozc d lne K cs proof (induct "length l" arbitrary: l K rule: nat_induct_3)
  case 0
  from "0.prems" (3) and "0.hyps" have False by simp thus ?case by (rule ccontr)
next
  case (1 l)
  from "1.hyps" obtain v where lv: "l = [v]" by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "K = {} | K = {{}} | K = {{}, {v}}"
    using powerset_singleton_cases [of K "v"] using "1.prems" (4,5) unfolding closed_subset_def by auto
  then consider (Ke) "K = {}" | (Ks) "K = {{}}" | (Ks1) "K = {{}, {v}}" by auto
  then show ?case
  proof (cases)
    case Ke
    show ?thesis unfolding Ke unfolding link_ext_empty cost_empty
      using collapses_rtrancl_def by blast
  next
    case Ks hence False using "1.prems" (1,3) unfolding Ks
      using not_ordered_zero_collapsible_not_empty [of l] by simp
    thus ?thesis by (rule ccontr)
  next
    case Ks1
    have "cost (hd l) (set l) K = {{}}" unfolding Ks1 cost_def powerset_def lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" unfolding Ks1 link_ext_def powerset_def lv list.sel by auto
    ultimately show ?thesis by (simp add: collapses_rtrancl_def)
  qed
next
  case 2
  from "2.hyps" and "2.prems" (2) obtain v w where lv: "l = [v,w]" and vw: "v \<noteq> w"
    by (metis One_nat_def Suc_1 diff_Suc_1 distinct_length_2_or_more length_0_conv length_tl list.exhaust_sel nat.simps(3))
  have "K = {} | K = {{}} | K = {{}, {v}} | K = {{}, {w}} | K = {{}, {v}, {w}} | K = {{}, {v}, {w}, {v,w}}"
    using cs_card_leq_2 [OF "2.prems" (4) _ vw "2.prems" (5)] using lv by simp
  then consider "K = {}" | "K = {{}}" | "K = {{}, {v}}" | "K = {{}, {w}}" 
      | "K = {{}, {v}, {w}}" | "K = {{}, {v}, {w}, {v,w}}" by fastforce
  then show ?case proof (cases)
    case 1
    show ?thesis unfolding 1 unfolding link_ext_empty cost_empty
      using collapses_rtrancl_def by blast
  next
    case 2
    hence False using "2.prems" (1,3) unfolding 2
      using not_ordered_zero_collapsible_not_empty [of l] by simp
    thus ?thesis by (rule ccontr)
  next
    case 3
    have "cost (hd l) (set l) K = {{}}" unfolding 3 cost_def powerset_def lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" unfolding 3 link_ext_def powerset_def lv list.sel by auto
    ultimately show ?thesis by (simp add: collapses_rtrancl_def)
  next
    case 4
    have "cost (hd l) (set l) K = {{},{w}}"
      unfolding 4 cost_def powerset_def lv list.sel using vw by auto
    moreover have "link_ext (hd l) (set l) K = {}" 
      unfolding 4 link_ext_def powerset_def lv list.sel using vw by auto
    ultimately show ?thesis
      by (metis (no_types, lifting) collapsible_def insert_commute mem_Collect_eq singleton_collapsable)
  next
    case 5
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v, w]) {{}, {v}, {w}} = {{},{w}}"
      unfolding 5 cost_def powerset_def lv list.sel using vw by auto
    have l: "link_ext v (set [v, w]) {{}, {v}, {w}} = {{}}" 
      unfolding 5 link_ext_def powerset_def lv list.sel using vw by auto
    have False using "2.prems" (1)
      using ordered_zero_collapsible.simps (3) [OF l1, of K]
      unfolding 5 unfolding lv list.sel
      unfolding c l
      by (metis Diff_insert_absorb c cone_peak_cost_eq_link_ext insert_absorb insert_not_empty l 
          list.sel(1) list.set_intros(1) not_cone_peak_cc_empty the_elem_eq)
    thus ?thesis by (rule ccontr)
  next
    case 6
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}"
      unfolding 6 cost_def powerset_def lv list.sel using vw by auto
    have l: "link_ext v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}" 
      unfolding 6 link_ext_def powerset_def lv list.sel using vw by auto
    show ?thesis unfolding 6 lv list.sel unfolding c l
      using collapses_rtrancl_def by blast
  qed
next
  case (Suc n l)
  have l1: "1 < length l" using Suc.hyps(1,3) by auto
  have l2: "2 \<le> length l" using Suc.hyps(1,3) by auto
  from Suc.prems (1) 
  have "(cone_peak (set l) K (hd l) | 
          ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l)))" 
    using ordered_zero_collapsible.simps (3) [OF l1, of K] by simp
  then consider (cp) "cone_peak (set l) K (hd l)" |
          (oz) "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))" by auto
  then show ?case
  proof (cases)
    case cp
    have "cost (hd l) (set l) K = link_ext (hd l) (set l) K"
    proof (rule cone_peak_cost_eq_link_ext)
      show "hd l \<in> set l" using Suc.prems (3) by simp
      show "cone_peak (set l) K (hd l)" using cp .
    qed
    thus ?thesis by (simp add: collapses_rtrancl_def)
  next
    case oz
    hence ozccost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)"
      and cplink: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))" by simp_all
    have hyp: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
    proof (rule "Suc.hyps" (2))
      show "n = length (tl l)" by (metis Suc.hyps(3) diff_Suc_1 length_tl)
      show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using ozccost .
      show "distinct (tl l)" by (simp add: Suc.prems(2) distinct_tl)
      show "tl l \<noteq> []" using Suc.hyps(1) \<open>n = length (tl l)\<close> by force
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        using Suc.prems (2,3,4) unfolding cost_def powerset_def
        by (metis (no_types, lifting) list.exhaust_sel mem_Collect_eq remove1_head set_remove1_eq subsetI)
      show "closed_subset (cost (hd l) (set l) K)" 
        using Suc.prems (5) unfolding closed_subset_def cost_def powerset_def by auto
    qed
    have c: "cost (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
    proof (rule proposition_2 [of "cost (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using Suc.prems (2,3,4) unfolding powerset_def cost_def
        by (metis (no_types, lifting) list.exhaust_sel mem_Collect_eq remove1_head set_remove1_eq subsetI)
      show "closed_subset (cost (hd l) (set l) K)"
        using Suc.prems (5) unfolding closed_subset_def cost_def powerset_def by auto
    qed
    have le: "link_ext (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
    proof (rule proposition_2 [of "link_ext (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using Suc.prems (2,3,4) unfolding powerset_def link_ext_def
        by (metis (no_types, lifting) Pow_iff list.exhaust_sel list.simps(15) mem_Collect_eq subsetI subset_insert)
      show "closed_subset (link_ext (hd l) (set l) K)" by (rule link_ext_closed_subset, intro Suc.prems (5))
    qed
    have stl: "set l - {hd l} = set (tl l)" using Suc.prems (2,3)
      by (metis list.collapse remove1_head set_remove1_eq)
    (*have "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) = link_ext (hd l) (set l - {hd (tl l)}) (cost (hd (tl l)) (set l) K)"
      using link_ext_cost_commute_length_ge2 [symmetric, OF l2 "Suc.prems" (2) "Suc.prems" (4) "Suc.prems" (5)]
      unfolding stl .*)
    have hdtl: "hd (tl l) \<in> set (tl l)" using l2 using cplink not_cone_outer_vertex by blast
    have link_join: "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
        = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
      unfolding join_vertex_def join_def by auto
    show ?thesis
      apply (subst c, subst le) 
      unfolding cone_peak_cost_eq_link_ext [OF hdtl cplink]
      unfolding link_join
    proof (rule union_join_collapses_join [of "set (tl (tl l))"])
      show "finite (set (tl (tl l)))" by simp
      show "hd (tl l) \<notin> set (tl (tl l))" using Suc.prems (2) l2
        by (metis distinct.simps(2) empty_iff list.collapse list.set(1) tl_Nil)
      show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        using Suc.prems (4) unfolding cost_def powerset_def
        by auto (metis DiffD1 DiffD2 empty_set hd_Cons_tl insert_Diff insert_not_empty set_ConsD singleton_iff subsetD)
      show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        using Suc.prems (4) unfolding cost_def powerset_def link_ext_def apply auto
        by (metis One_nat_def Suc.hyps(3) diff_Suc_1 in_mono l1 length_tl list.collapse list.size(3) nless_le set_ConsD)
      show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
        using Suc.prems (5) unfolding cost_def link_ext_def closed_subset_def powerset_def
        by auto (meson insert_mono)
      show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        using Suc.prems (4) unfolding powerset_def link_ext_def
        by auto (metis empty_iff empty_set list.exhaust_sel set_ConsD subset_iff)
      show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
        using Suc.prems (5) unfolding closed_subset_def link_ext_def powerset_def
        by auto (meson insert_mono)
      show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
        using Suc.prems (5) unfolding link_ext_def cost_def powerset_def closed_subset_def 
        by auto (blast)
      show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
        using hyp .
    qed
  qed
qed

lemma ordered_one_collapsible_cost_collapses_link_ext:
  assumes ozc: "ordered_m_collapsible 1 l K" and d: "distinct l" 
    and lne: "l \<noteq> []"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
  shows "(cost (hd l) (set l) K, link_ext (hd l) (set l) K) \<in> collapses_rtrancl"
using ozc d lne K cs proof (induct "length l" arbitrary: l K rule: nat_induct_3)
  case 0
  from "0.prems" (3) and "0.hyps" have False by simp thus ?case by (rule ccontr)
next
  case (1 l)
  from "1.hyps" obtain v where lv: "l = [v]" by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "K = {} | K = {{}} | K = {{}, {v}}"
    using powerset_singleton_cases [of K "v"] using "1.prems" (4,5) unfolding closed_subset_def by auto
  then consider (Ke) "K = {}" | (Ks) "K = {{}}" | (Ks1) "K = {{}, {v}}" by auto
  then show ?case
  proof (cases)
    case Ke
    show ?thesis unfolding Ke unfolding link_ext_empty cost_empty
      using collapses_rtrancl_def by blast
  next
    case Ks hence False 
      using "1.prems" (1,3) unfolding Ks
      using not_ordered_m_collapsible_not_empty [of ] by blast
    thus ?thesis by (rule ccontr)
  next
    case Ks1
    have "cost (hd l) (set l) K = {{}}" unfolding Ks1 cost_def powerset_def lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" unfolding Ks1 link_ext_def powerset_def lv list.sel by auto
    ultimately show ?thesis by (simp add: collapses_rtrancl_def)
  qed
next
  case 2
  from "2.hyps" and "2.prems" (2) obtain v w where lv: "l = [v,w]" and vw: "v \<noteq> w"
    by (metis One_nat_def Suc_1 diff_Suc_1 distinct_length_2_or_more length_0_conv length_tl list.exhaust_sel nat.simps(3))
  have "K = {} | K = {{}} | K = {{}, {v}} | K = {{}, {w}} | K = {{}, {v}, {w}} | K = {{}, {v}, {w}, {v,w}}"
    using cs_card_leq_2 [OF "2.prems" (4) _ vw "2.prems" (5)] using lv by simp
  then consider "K = {}" | "K = {{}}" | "K = {{}, {v}}" | "K = {{}, {w}}" 
      | "K = {{}, {v}, {w}}" | "K = {{}, {v}, {w}, {v,w}}" by fastforce
  then show ?case proof (cases)
    case 1
    show ?thesis unfolding 1 unfolding link_ext_empty cost_empty
      using collapses_rtrancl_def by blast
  next
    case 2
(*    hence False using "2.prems" (1,3) unfolding 2
      using not_ordered_zero_collapsible_not_empty [of l] by simp
    thus ?thesis by (rule ccontr)
  next
    case 3
    have "cost (hd l) (set l) K = {{}}" unfolding 3 cost_def powerset_def lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" unfolding 3 link_ext_def powerset_def lv list.sel by auto
    ultimately show ?thesis by (simp add: collapses_rtrancl_def)
  next
    case 4
    have "cost (hd l) (set l) K = {{},{w}}"
      unfolding 4 cost_def powerset_def lv list.sel using vw by auto
    moreover have "link_ext (hd l) (set l) K = {}" 
      unfolding 4 link_ext_def powerset_def lv list.sel using vw by auto
    ultimately show ?thesis
      by (metis (no_types, lifting) collapsible_def insert_commute mem_Collect_eq singleton_collapsable)
  next
    case 5
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v, w]) {{}, {v}, {w}} = {{},{w}}"
      unfolding 5 cost_def powerset_def lv list.sel using vw by auto
    have l: "link_ext v (set [v, w]) {{}, {v}, {w}} = {{}}" 
      unfolding 5 link_ext_def powerset_def lv list.sel using vw by auto
    have False using "2.prems" (1)
      using ordered_zero_collapsible.simps (3) [OF l1, of K]
      unfolding 5 unfolding lv list.sel
      unfolding c l
      by (metis Diff_insert_absorb c cone_peak_cost_eq_link_ext insert_absorb insert_not_empty l 
          list.sel(1) list.set_intros(1) not_cone_peak_cc_empty the_elem_eq)
    thus ?thesis by (rule ccontr)
  next
    case 6
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}"
      unfolding 6 cost_def powerset_def lv list.sel using vw by auto
    have l: "link_ext v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}" 
      unfolding 6 link_ext_def powerset_def lv list.sel using vw by auto
    show ?thesis unfolding 6 lv list.sel unfolding c l
      using collapses_rtrancl_def by blast
  qed
next
  case (Suc n l)
  have l1: "1 < length l" using Suc.hyps(1,3) by auto
  have l2: "2 \<le> length l" using Suc.hyps(1,3) by auto
  from Suc.prems (1) 
  have "(cone_peak (set l) K (hd l) | 
          ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l)))" 
    using ordered_zero_collapsible.simps (3) [OF l1, of K] by simp
  then consider (cp) "cone_peak (set l) K (hd l)" |
          (oz) "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))" by auto
  then show ?case
  proof (cases)
    case cp
    have "cost (hd l) (set l) K = link_ext (hd l) (set l) K"
    proof (rule cone_peak_cost_eq_link_ext)
      show "hd l \<in> set l" using Suc.prems (3) by simp
      show "cone_peak (set l) K (hd l)" using cp .
    qed
    thus ?thesis by (simp add: collapses_rtrancl_def)
  next
    case oz
    hence ozccost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)"
      and cplink: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))" by simp_all
    have hyp: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
    proof (rule "Suc.hyps" (2))
      show "n = length (tl l)" by (metis Suc.hyps(3) diff_Suc_1 length_tl)
      show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using ozccost .
      show "distinct (tl l)" by (simp add: Suc.prems(2) distinct_tl)
      show "tl l \<noteq> []" using Suc.hyps(1) \<open>n = length (tl l)\<close> by force
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        using Suc.prems (2,3,4) unfolding cost_def powerset_def
        by (metis (no_types, lifting) list.exhaust_sel mem_Collect_eq remove1_head set_remove1_eq subsetI)
      show "closed_subset (cost (hd l) (set l) K)" 
        using Suc.prems (5) unfolding closed_subset_def cost_def powerset_def by auto
    qed
    have c: "cost (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
    proof (rule proposition_2 [of "cost (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using Suc.prems (2,3,4) unfolding powerset_def cost_def
        by (metis (no_types, lifting) list.exhaust_sel mem_Collect_eq remove1_head set_remove1_eq subsetI)
      show "closed_subset (cost (hd l) (set l) K)"
        using Suc.prems (5) unfolding closed_subset_def cost_def powerset_def by auto
    qed
    have le: "link_ext (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
    proof (rule proposition_2 [of "link_ext (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using Suc.prems (2,3,4) unfolding powerset_def link_ext_def
        by (metis (no_types, lifting) Pow_iff list.exhaust_sel list.simps(15) mem_Collect_eq subsetI subset_insert)
      show "closed_subset (link_ext (hd l) (set l) K)" by (rule link_ext_closed_subset, intro Suc.prems (5))
    qed
    have stl: "set l - {hd l} = set (tl l)" using Suc.prems (2,3)
      by (metis list.collapse remove1_head set_remove1_eq)
    (*have "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) = link_ext (hd l) (set l - {hd (tl l)}) (cost (hd (tl l)) (set l) K)"
      using link_ext_cost_commute_length_ge2 [symmetric, OF l2 "Suc.prems" (2) "Suc.prems" (4) "Suc.prems" (5)]
      unfolding stl .*)
    have hdtl: "hd (tl l) \<in> set (tl l)" using l2 using cplink not_cone_outer_vertex by blast
    have link_join: "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
        = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
      unfolding join_vertex_def join_def by auto
    show ?thesis
      apply (subst c, subst le) 
      unfolding cone_peak_cost_eq_link_ext [OF hdtl cplink]
      unfolding link_join
    proof (rule union_join_collapses_join [of "set (tl (tl l))"])
      show "finite (set (tl (tl l)))" by simp
      show "hd (tl l) \<notin> set (tl (tl l))" using Suc.prems (2) l2
        by (metis distinct.simps(2) empty_iff list.collapse list.set(1) tl_Nil)
      show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        using Suc.prems (4) unfolding cost_def powerset_def
        by auto (metis DiffD1 DiffD2 empty_set hd_Cons_tl insert_Diff insert_not_empty set_ConsD singleton_iff subsetD)
      show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        using Suc.prems (4) unfolding cost_def powerset_def link_ext_def apply auto
        by (metis One_nat_def Suc.hyps(3) diff_Suc_1 in_mono l1 length_tl list.collapse list.size(3) nless_le set_ConsD)
      show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
        using Suc.prems (5) unfolding cost_def link_ext_def closed_subset_def powerset_def
        by auto (meson insert_mono)
      show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        using Suc.prems (4) unfolding powerset_def link_ext_def
        by auto (metis empty_iff empty_set list.exhaust_sel set_ConsD subset_iff)
      show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
        using Suc.prems (5) unfolding closed_subset_def link_ext_def powerset_def
        by auto (meson insert_mono)
      show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
        using Suc.prems (5) unfolding link_ext_def cost_def powerset_def closed_subset_def 
        by auto (blast)
      show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
        using hyp .
    qed
  qed
qed*)


theorem
  assumes"ordered_m_collapsible m l K" and "distinct l" and "K \<subseteq> powerset (set l)" and "closed_subset K"
  shows "(cost (hd l) (set (tl l)) K, link_ext (hd l) (set (tl l)) K) \<in> collapses_rtrancl"
  sorry

section\<open>Consequences of the main theorem.\<close>

definition vertex_set :: "nat set set \<Rightarrow> nat set"
  where "vertex_set K = {v::nat. {v} \<in> K}"

lemma assumes c: "closed_subset K" 
  shows "K \<subseteq> powerset (vertex_set K)" 
  using c unfolding powerset_def vertex_set_def closed_subset_def by auto

definition facets :: "nat set set \<Rightarrow> nat set set"
  where "facets K = {a. facet a K}"

lemma shows "facet a K \<equiv> a \<in> facets K"
  unfolding facets_def by simp

definition pure_d :: "nat \<Rightarrow> nat set set \<Rightarrow> bool"
  where "pure_d d K = (\<forall>f\<in>facets K. card f = d)"

text\<open>Lemma 9 in our paper:\<close>

lemma assumes K: "K \<subseteq> powerset V" and c: "closed_subset K" and d: "0 < d" 
  and p: "pure_d d K" and v: "{v} \<in> K" shows "pure_d (d - 1) (link_ext v V K)"
proof (unfold pure_d_def, rule)
  fix f
  assume f: "f \<in> facets (link_ext v V K)" 
  hence "f \<in> link_ext v V K" 
    unfolding facets_def
    using facet_in_K by auto
  hence vnf: "v \<notin> f" unfolding link_ext_def powerset_def by simp
  have insf: "insert v f \<in> facets K"
  proof (unfold facets_def, rule, unfold facet_def, rule)
    show "insert v f \<in> K"
      using f unfolding facets_def link_ext_def facet_def by simp
    show "\<forall>b\<in>K. insert v f \<subseteq> b \<longrightarrow> insert v f = b"
    proof (rule, rule)
      fix b assume b: "b \<in> K" and i: "insert v f \<subseteq> b"
      show "insert v f = b"
      proof (rule ccontr)
        assume "insert v f \<noteq> b" hence ins: "insert v f \<subset> b" using i by auto
        have "b - {v} \<in> link_ext v V K" using b K i unfolding link_ext_def powerset_def
          by auto (simp add: insert_absorb)
        moreover have "f \<subset> b - {v}" using ins vnf by auto
        ultimately show False using f unfolding facets_def facet_def by auto
      qed
    qed
  qed
  show "card f = d - 1" using insf p vnf d unfolding pure_d_def
    by (metis (no_types, lifting) Diff_insert_absorb card_Diff_singleton insertCI)
qed

definition dim :: "nat set set \<Rightarrow> nat"
  where "dim K = Max {n. \<exists>k\<in>K. n = card k} - 1"

lemma "dim {{}} = 0" and "dim {{7}} = 0" and "dim {{3,7}} = 1" 
  unfolding dim_def by auto

lemma assumes n: "non_evasive (vertex_set K) K" and p: "pure_d 1 K"
  and f: "finite (vertex_set K)" and K: "K \<subseteq> powerset (vertex_set K)" shows "2 \<le> card {v. {v} \<in> K}"
proof (induct "card {v\<in>K. card v = 2}")
  case 0 with n
  show ?case sorry
next
  case (Suc x)
  then show ?case sorry
qed


lemma assumes n: "non_evasive (vertex_set K) K" and p: "pure_d d K" and d: "0 < d"
      and f: "finite (vertex_set K)" and K: "K \<subseteq> powerset (vertex_set K)" shows "2 \<le> card {f. free_face f K}"
proof (cases "K = {}")
  case True
  from n
  have False unfolding True vertex_set_def by simp thus ?thesis by (rule ccontr)
next
  case False note Kne = False
  show ?thesis
  proof (cases "K = {{}}")
    case True
    have False using n unfolding True vertex_set_def by simp
    thus ?thesis by (rule ccontr)
  next
    case False
    have "finite K" using f K unfolding vertex_set_def powerset_def
      by (simp add: finite_subset)
    show ?thesis
      using Kne False n p d proof (induct "dim K")
      case 0 note prems = "0.prems" and hyp = 0
      show ?case
      proof (induct "card (facets K)")
        case 0 with prems (4,5) and `finite K` have False unfolding pure_d_def
        show ?case sorry
      next
        case (Suc x)
        then show ?case sorry
      qed

        from "0.prems" and "0" have False unfolding pure_d_def facets_def facet_def dim_def apply auto
      then  sorry
    next
      case (Suc x)
      then show ?case sorry
    qed
    
  case 0
  
  then show ?case sorry
next
  case (Suc x)
  then show ?case sorry
qed

lemma
  assumes l: "2 \<le> length l" and K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and o: "ordered_zero_collapsible l K" 
    and nc_0: "\<not> cone_peak (set l) K (l!0)"
    and nc_1: "\<not> cone_peak (set l) K (l!1)"
  shows "ordered_zero_collapsible ((l!1) # (l!0) # tl (tl l)) K"
  using l d o nc_0 nc_1 proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  show ?case proof (cases "length l = 2")
    case True hence lcons: "l = [l ! 0, l ! 1]"
      by (metis One_nat_def add_diff_cancel_right' diff_is_0_eq' hd_conv_nth le_numeral_extra(4) length_0_conv length_greater_0_conv length_tl lessI list.exhaust_sel nth_Cons_Suc one_add_one zero_neq_numeral)
    hence lneq: "l ! 0 \<noteq> l ! 1" 
      using less.prems (2) by (metis distinct_length_2_or_more)
    from lcons have tl: "tl (tl l) = []" by (metis list.sel(3))
    from lcons have "ordered_zero_collapsible [l!0,l!1] K" using less.prems (3) by simp
    with less.prems (4) and ordered_zero_collapsible.simps (2) [of l K] and True
    have "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
     cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)"
      by (metis Suc_1 lcons list.sel(1) zero_less_Suc)
    thus ?thesis
      unfolding tl
      using less.prems (4,5) and ordered_zero_collapsible.simps (2) [of "[l!1,l!0]" K] and True
      by (metis cone_peak_def distinct.simps(2) lcons less.prems(2) list.sel(1) list.sel(3))
  next
    case False
    hence l2: "2 < length l" and l0: "0 < length l" using less.prems (1,3) by auto


lemma
  assumes l: "2 \<le> length l" and K: "K \<subseteq> powerset (set l)" and d: "distinct l" 
    and o: "ordered_m_collapsible m l K" 
    and nc_1: "\<not> cone_peak (set l) K (l!0)"
    and nc_cost: "\<not> cone_peak (set (tl l)) (cost (l!0) (set (tl l)) K) (l!1)"
    and nc_link: "\<not> cone_peak (set (tl l)) (link_ext (l!0) (set (tl l)) K) (l!1)"
  shows "ordered_m_collapsible m ((l!1) # (l!0) # tl (tl l)) K"
  using l d o nc_1 nc_cost nc_link proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  show ?case proof (cases "length l = 2")
    case True hence lcons: "l = [l ! 0, l ! 1]"
      by (metis One_nat_def add_diff_cancel_right' diff_is_0_eq' hd_conv_nth le_numeral_extra(4) length_0_conv length_greater_0_conv length_tl lessI list.exhaust_sel nth_Cons_Suc one_add_one zero_neq_numeral)
    hence lneq: "l ! 0 \<noteq> l ! 1" 
      using less.prems (2) by (metis distinct_length_2_or_more)
    from lcons have tl: "tl (tl l) = []" by (metis list.sel(3))
    from lcons have "ordered_m_collapsible m [l!0,l!1] K" using less.prems (3) by simp
    with less.prems (4) and ordered_m_collapsible.simps
    have "ordered_m_collapsible m [l!1,l!0] K"
    using ordered_m_collapsible.simps
    thus ?thesis using tl by simp


    qed



end