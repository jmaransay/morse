
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
      using K c v unfolding cost_def link_ext_def by auto
    show "K \<subseteq> cost v V K \<union> {s. \<exists>b\<in>cost v V K. s = insert v b}"
    proof (subst c, unfold cost_def link_ext_def, rule)
      fix xa
      assume xa: "xa \<in> K"
      show "xa \<in> {s \<in> Pow V. v \<notin> s \<and> insert v s \<in> K} \<union>
                {s. \<exists>t\<in>{s \<in> Pow (V - {v}). s \<in> K}. s = insert v t}"
      proof (cases "v \<in> xa")
        case False then show ?thesis using xa c K 
          unfolding cost_def link_ext_def by blast
      next
        case True
        have "xa - {v} \<in> {s \<in> Pow V. v \<notin> s \<and> insert v s \<in> K}"
          using xa K True mk_disjoint_insert by fastforce
        hence "xa - {v} \<in> {s \<in> Pow (V - {v}). s \<in> K}"
          using c unfolding cost_def link_ext_def  by simp
        hence "xa \<in> {s. \<exists>t\<in>{s \<in> Pow (V - {v}). s \<in> K}. s = insert v t}"
          using True by auto
        thus ?thesis by fast
      qed
    qed
  qed
  moreover have "cost v V K \<subseteq> powerset (V - {v})" 
    using K
    unfolding cost_def  by auto
  ultimately show "\<exists>B\<subseteq>powerset (V - {v}). K = B \<union> {s. \<exists>b\<in>B. s = insert v b}" by auto
qed

text\<open>Proposition 1 in our paper\<close>

corollary proposition_1:
  assumes v: "v \<in> V" and K: "K \<subseteq> powerset V" shows "cone_peak V K v \<equiv> (cost v V K = link_ext v V K)"
  using cone_peak_cost_eq_link_ext [OF v, of K]
  using cost_eq_link_ext_cone_peak [OF v K] by argo

text\<open>Proposition 2 in our paper\<close>

lemma proposition_2:
  assumes K: "K \<subseteq> powerset V" and c: "closed_subset K"
  shows "K = cost v V K \<union> join_vertex v (link_ext v V K)"
proof -
  have "K = cost v V K \<union> join_vertex v (link v V K)" using complex_decomposition [OF K c] .
  moreover have "link v V K = link_ext v V K"
    using K c 
    unfolding link_def link_ext_def  closed_subset_def by auto
  ultimately show ?thesis by simp
qed

section\<open>Definition of \<open>ordered-no-evasive\<close>\<close>

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
  have c: "cost (hd (a # l)) (set (a # l)) {{}} = {{}}" unfolding cost_def  by auto
  have l: "link_ext (hd (a # l)) (set (a # l)) {{}} = {}" unfolding link_ext_def  list.sel by auto
  have "\<not> cone_peak (set (a # l)) {{}} (hd (a # l))" by (rule not_cone_peak_cc_empty)
  moreover have "\<not> ordered_non_evasive (tl (a # l)) (cost (hd (a # l)) (set (a # l)) {{}})"
    unfolding c unfolding list.sel using one .
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
      using B unfolding cost_def  by auto
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
      using B unfolding link_ext_def  by auto
    show "link_ext y V K = link_ext y (V - {v}) B \<union> {s. \<exists>b\<in>link_ext y (V - {v}) B. s = insert v b}"
      by (rule ceq)
  qed
qed

text\<open>Relationship between @{term cone_peak} and @{term ordered_non_evasive}\<close>

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
        using less.prems (1) l unfolding  cost_def by (simp add: l subset_iff)
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
        using less.prems (1) l unfolding  link_ext_def by auto
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

section\<open>Ordered zero collapsible simplicial complexes\<close>

function ordered_zero_collapsible :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_zero_collapsible l K = False"
  | "1 = length l \<Longrightarrow> ordered_zero_collapsible l K = cone_peak (set l) K (hd l)"
  | "1 < length l \<Longrightarrow> ordered_zero_collapsible l K = ((cone_peak (set l) K (hd l))
      | (ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
          cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))))"
  by auto (metis One_nat_def length_0_conv less_one linorder_neqE_nat)
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

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
    have le: "link_ext (hd l) (set l) {{}} = {}" unfolding link_ext_def  by simp
    have ce: "cost (hd l) (set l) {{}} = {{}}" unfolding cost_def  by auto
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

section\<open>Ordered \<open>m\<close> collapsible simplicial complexes\<close>

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
  have le: "link_ext (hd l) (set l) {{}} = {}" using l0 unfolding link_ext_def  by auto
  have c: "cost (hd l) (set l) {{}} = {{}}" using l0 unfolding link_ext_def  by auto
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
  have pV: "powerset V = {{v1,v2},{v1},{v2},{}}" using c by auto
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
              using cost_closed [OF less.prems (1), of "hd l"] less.prems (3) l0
              by (metis length_greater_0_conv list.collapse remove1_head set_remove1_eq)
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
  from K and w and B and Kd have "B \<subseteq> powerset (V - {v})" by auto
  with nc and Kd and v show False unfolding cone_peak_def by auto
qed

section\<open>The set of vertexes that belong to the simplicial complex\<close>

definition vertex_of_simpl_complex :: "nat set set \<Rightarrow> nat set"
  where "vertex_of_simpl_complex K = {v. {v} \<in> K}"

lemma "vertex_of_simpl_complex {} = {}" unfolding vertex_of_simpl_complex_def by simp

lemma "vertex_of_simpl_complex {{}} = {}" unfolding vertex_of_simpl_complex_def by simp

lemma "vertex_of_simpl_complex {{v}} = {v}" unfolding vertex_of_simpl_complex_def by simp

(*definition vertex_of :: "nat set set \<Rightarrow> nat set set"
  where "vertex_of K = {v. v \<in> K \<and> card v = 1}"

definition map_v where "map_v v = {v}"

lemma assumes f: "finite K" shows "finite (vertex_of K)" using f unfolding vertex_of_def by simp

lemma "map_v \<circ> vertex_of_simpl_complex = vertex_of"
  unfolding map_v_def vertex_of_simpl_complex_def vertex_of_def apply (rule ext) apply auto try 

lemma "card (vertex_of K) = card (vertex_of_simpl_complex K)"
  using card_image [symmetric, of map_v]
lemma assumes f: "finite K" shows "finite (vertex_of_simpl_complex K)"
proof (cases "vertex_of_simpl_complex K = {}")
  case True
  then show ?thesis by simp
next
  case False then obtain v where "v \<in> vertex_of_simpl_complex K" by auto
  define g where "g k = {k}"
  then show ?thesis sorry
qed
  
  have "finite {V \<in> K. card V = 1}" using f by simp
  define f where "f v = {v}"
  thus ?thesis unfolding vertex_of_simpl_complex_def using card_image try
*)

lemma powerset_vertex_of_simpl_complex: assumes K: "K \<subseteq> powerset V" and cs: "closed_subset K" 
  shows "K \<subseteq> powerset (vertex_of_simpl_complex K)"
  using K cs unfolding vertex_of_simpl_complex_def closed_subset_def by auto

lemma vertex_of_simpl_complex_subset:
  assumes fV: "finite V" and KV: "K \<subseteq> powerset V"
  shows "vertex_of_simpl_complex K \<subseteq> V"
  unfolding vertex_of_simpl_complex_def using KV by auto

corollary card_vertex_of_simpl_complex:
  assumes fV: "finite V" and KV: "K \<subseteq> powerset V"
  shows "card (vertex_of_simpl_complex K) \<le> card V"
   by (rule card_mono [OF fV vertex_of_simpl_complex_subset [OF fV KV]])

lemma finite_vertex_of_simpl_complex: 
  assumes f: "finite V" and K: "K \<subseteq> powerset V" 
  shows "finite (vertex_of_simpl_complex K)"
proof -
  have "finite K" using K f by (simp add: finite_subset)
  hence f2: "finite {v. v \<in> V \<and> {v} \<in> K}" using f by simp
  have "{v. v \<in> V \<and> {v} \<in> K} = {v. {v} \<in> K}"
    using K by blast
  thus ?thesis using f2 unfolding vertex_of_simpl_complex_def by simp
qed

lemma closed_subset_vertex_of_simpl_complex:
  assumes f: "f \<in> K" and cs: "closed_subset K"
  shows "{v. {v} \<subseteq> f} \<subseteq> vertex_of_simpl_complex K"
  using f cs unfolding closed_subset_def vertex_of_simpl_complex_def by auto

text\<open>There is no assumption over the vertex for which we compute the @{term lin_ext} or the @{term cost}.\<close>

lemma link_ext_vertex_of_simpl_complex:
  assumes KV: "K \<subseteq> powerset V" and cs: "closed_subset K"
  shows "link_ext v V K = link_ext v (vertex_of_simpl_complex K) K"
  using KV cs unfolding vertex_of_simpl_complex_def link_ext_def closed_subset_def by auto

lemma cost_vertex_of_simpl_complex:
  assumes KV: "K \<subseteq> powerset V" and cs: "closed_subset K"
  shows "cost v V K = cost v (vertex_of_simpl_complex K) K"
  using KV cs unfolding vertex_of_simpl_complex_def cost_def closed_subset_def by auto

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
  hence "{v} \<in> K" 
    using Kne K cs unfolding  cone_peak_def closed_subset_def
    by (smt (verit, del_insts) Un_iff empty_subsetI ex_in_conv insert_mono mem_Collect_eq)
  thus False using v unfolding vertex_of_simpl_complex_def by simp
qed

lemma assumes ne: "non_evasive V K" and KV: "K \<subseteq> powerset V" and Kne: "K \<noteq> {}"
  shows "non_evasive (vertex_of_simpl_complex K) K"
proof (cases "(V, K)" rule: non_evasive.cases)
  case (1 V K)
  have False using non_evasive.simps (1) [OF "1" (1), of K] using ne "1" (2) by simp
  thus ?thesis by (rule ccontr)
next
  case (2 V x K)
  have False using Kne using 2 ne using non_evasive_empty_set [OF _ ] by simp
  thus ?thesis by (rule ccontr)
next
  case (3 V x K)
  hence "vertex_of_simpl_complex K = V" unfolding vertex_of_simpl_complex_def by simp
  thus ?thesis using ne 3 by simp
next
  case (4 V x K)
  from ne and 4 have False using non_evasive.simps (4) by simp
  thus ?thesis by (rule ccontr)
next
  case (5 V' K')
  hence v: "V = V'" and k: "K = K'" using 5 by simp_all
  from ne obtain x where x: "x \<in> V'" and nel: "non_evasive (V' - {x}) (link_ext x V' K')"
      and nec: "non_evasive (V' - {x}) (cost x V' K')"
    using non_evasive.simps (5) [OF "5" (1), of K'] 5 by auto
  show ?thesis unfolding v k
  proof (cases "2 \<le> card (vertex_of_simpl_complex K')")
    case True note c2 = True
    show "non_evasive (vertex_of_simpl_complex K') K'"
    proof (cases "x \<in> vertex_of_simpl_complex K'")
      case True
      show ?thesis
      using c2 ne unfolding v k proof (induct "card (vertex_of_simpl_complex K')" arbitrary: V' K')
        case 0
        then show ?case by presburger
      next
        case (Suc xa)
        have "non_evasive (vertex_of_simpl_complex K' - {x}) (link_ext x (vertex_of_simpl_complex K') K')"
           using Suc.hyps (1)
        show ?case using non_evasive.simps (5) [OF "Suc.prems" (1)]
    next
      case False
      then show ?thesis sorry
    qed
      
  next
    case False
    then show ?thesis sorry
  qed
  
next
  case (6 V K)
  then show ?thesis sorry
qed
  using ne c2 sb proof (induct "card V" arbitrary: V)
  case 0
  then show ?case by linarith
next
  case (Suc x)
  obtain x where "x \<in> V" and "non_evasive (V - {x}) (link_ext x V K)" and "non_evasive (V - {x}) (cost x V K)"
    using Suc.prems (1)
    unfolding non_evasive.simps (5) [OF Suc.prems (2)] by auto
  show ?case
  proof (cases "2 \<le> card W")
    case True
    obtain x where x: "x \<in> V"
      and nl: "non_evasive (V - {x}) (link_ext x V K)" and ne: "non_evasive (V - {x}) (cost x V K)"
      using Suc.prems (1) unfolding non_evasive.simps (5) [OF Suc.prems (2), of K] by auto
    then have "{x} \<in> K" using Suc.prems (1) unfolding non_evasive.simps (5) [OF Suc.prems (2), of K] try
    have l: "link_ext x V K = link_ext x W K" using link_ext_mono2 [OF Suc.prems (3) K, of x] .
    moreover have c: "cost x V K = cost x W K" using cost_mono2 [OF Suc.prems (3) K, of x] .
    
    show ?thesis
      using Suc.prems using non_evasive.simps (5) [OF Suc.prems (2), of K]
      using non_evasive.simps (5) [OF True, of K]
    
    sorry


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
      unfolding closed_subset_def
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
      unfolding kne list.sel (1,3) cone_peak_def 
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
      show "{{}} \<subseteq> powerset (set (v # l))" by simp
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
        show "K \<subseteq> powerset (set (v # l))" using K by auto
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
        unfolding cost_def  by auto
      from o and cnp have ozc_c: "ordered_m_collapsible m l (cost v (set (v # l)) K)"
        and cp_l: "ordered_m_collapsible (m - 1) (tl (v # l)) (link_ext (hd (v # l)) (set (v # l)) K)"
        using ordered_m_collapsible.simps (3) [OF lvl m, of K] by simp_all
      from ozc_c have ozc_K: "ordered_m_collapsible m l K" using clK by simp
      show ?thesis
      proof (cases "cone_peak (set l) K (hd l)")
        case True
        have "cone_peak (set (hd l # v # tl l)) K (hd l)"
        proof (unfold cone_peak_def , intro conjI)
          show "hd l \<in> set (hd l # v # tl l)" by simp
          from True obtain B where B_subset: "B \<subseteq> Pow (set l - {hd l})" and KB: "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}"
            unfolding cone_peak_def  by auto
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
              using vnl l tl K d unfolding cost_def  apply auto
               apply (metis in_mono list.exhaust_sel remove1_head set_remove1_eq)
              by (metis list.exhaust_sel remove1_head set_remove1_eq subset_iff)
          thus ?thesis using ozc_tl by simp
        qed
        moreover have "ordered_m_collapsible (m - 1) (tl (v # tl l)) (link_ext (hd (v # tl l)) (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K))"
        proof -
          have "(link_ext (hd (v # tl l)) (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K)) = {}"
            using vnl l tl K d unfolding link_ext_def  cost_def by auto
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
             unfolding cost_def link_ext_def  by auto
            show ?thesis
            proof -
             have ll: "(link_ext (hd l) (set l) K) = (link_ext (hd l) (set (hd l # v # tl l)) K)"
               using vnl K l
               unfolding link_ext_def 
               by auto (metis list.exhaust_sel set_ConsD subset_iff)
             show ?thesis using cp unfolding cl unfolding ll unfolding list.sel (1,3) by simp
           qed
         qed
         moreover have "ordered_m_collapsible (m - 1 - 1) (tl (v # tl l))
          (link_ext (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K))"
         proof -
           have "(link_ext (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) = {}"
             using vnl K unfolding link_ext_def  by auto
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
             unfolding cost_def link_ext_def  by auto
          have ll: "(link_ext (hd l) (set l) K) = (link_ext (hd l) (set (hd l # v # tl l)) K)"
            using vnl K l
            unfolding link_ext_def  by auto (metis list.exhaust_sel set_ConsD subset_iff)
          show ?thesis unfolding cl unfolding ll [symmetric] 
            using cp using ordered_m_collapsible.simps (2) [OF ltl m10] by simp
        qed
        moreover have "cone_peak (set (tl l)) (link_ext v (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) (hd (tl l))" 
        proof -
          have "(link_ext (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K)) = {}"
             using vnl K unfolding link_ext_def  by auto
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
      unfolding  closed_subset_def
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
      unfolding cost_def  using v unfolding vertex_of_simpl_complex_def using sl by auto
    have le: "link_ext (hd (v # l)) (set (v # l)) K = {}"
      using vnl unfolding kne
      unfolding link_ext_def  using v unfolding vertex_of_simpl_complex_def using sl by auto
    have cp: "cone_peak (set l) K (hd l)"
    proof (unfold kne cone_peak_def , intro conjI)
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
      show "{{}} \<subseteq> powerset (set (hd l # v # tl l))" by simp
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
          using K unfolding cost_def  using vnl by auto
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
            proof (rule ccontr, simp, unfold cone_peak_def )
              assume "hd l \<in> insert (hd l) (insert v (set (tl l))) \<and>
                (\<exists>B\<subseteq>Pow (insert (hd l) (insert v (set (tl l))) - {hd l}). K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}) "
              then obtain B where "B\<subseteq>Pow (set (hd l # v # tl l) - {hd (hd l # v # tl l)})"
                and "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd (hd l # v # tl l)) b}" by auto
              then have "B\<subseteq>Pow (set l - {hd l})" and "K = B \<union> {s. \<exists>b\<in>B. s = insert (hd l) b}" 
                using l vnl K by auto
              thus False using False l unfolding cone_peak_def  by auto
            qed
            have ncp_cost: "\<not> cone_peak (set (v # tl l)) (cost (hd l) (set (hd l # v # tl l)) K) v"
            proof (rule not_cone_outer_vertex_simpl_complex)
              show "v \<notin> vertex_of_simpl_complex (cost (hd l) (set (hd l # v # tl l)) K)" 
                using v vnl unfolding vertex_of_simpl_complex_def cost_def  by simp
              show "cost (hd l) (set (hd l # v # tl l)) K \<subseteq> powerset (set (v # tl l))" 
                using K unfolding cost_def  by auto
              show "closed_subset (cost (hd l) (set (hd l # v # tl l)) K)" 
                using cs unfolding cost_def  closed_subset_def by auto
              show "cost (hd l) (set (hd l # v # tl l)) K \<noteq> {}" 
                using Kne unfolding cost_def 
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
                unfolding cost_def  apply auto
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
                  using K v vnl unfolding vertex_of_simpl_complex_def link_ext_def  by auto
                show "link_ext (hd l) (set (hd l # v # tl l)) K \<subseteq> powerset (set (v # tl l))" 
                  using K unfolding link_ext_def  by auto
                show "closed_subset (link_ext (hd l) (set (hd l # v # tl l)) K)"
                  using cs K vnl unfolding link_ext_def  closed_subset_def 
                  by auto (meson insert_mono)
                show "link_ext (hd l) (set (hd l # v # tl l)) K \<noteq> {}" 
                  using Kne link_ne cs unfolding link_ext_def  closed_subset_def
                  by auto
              qed              
              have c_eq_l: "cost (hd (v # tl l)) (set (v # tl l)) (link_ext (hd l) (set (hd l # v # tl l)) K) = link_ext (hd l) (set (hd l # v # tl l)) K"
                using vnl K d l
                unfolding link_ext_def cost_def  by auto
              have l_eq_l: "link_ext (hd l) (set (hd l # v # tl l)) K = link_ext (hd l) (set l) K"
                using vnl K unfolding link_ext_def 
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
        using K unfolding link_ext_def  using vnl by auto
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
  using l d K cs unfolding  cost_def closed_subset_def by auto

lemma cost_link_ext_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" 
  shows "cost (hd l) (set l - {hd (tl l)}) (link_ext (hd (tl l)) (set l) K) = 
          link_ext (hd (tl l)) (set l - {hd l}) (cost (hd l) (set l) K)"
  using l d K cs unfolding  cost_def link_ext_def closed_subset_def
  by auto (metis Nitpick.size_list_simp(2) One_nat_def distinct_length_2_or_more list.exhaust_sel not_numeral_le_zero numeral_le_one_iff semiring_norm(69))

lemma link_ext_cost_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" 
  shows "link_ext (hd l) (set l - {hd (tl l)}) (cost (hd (tl l)) (set l) K) = 
          cost (hd (tl l)) (set l - {hd l}) (link_ext (hd l) (set l) K)"
  using l d K cs unfolding  cost_def link_ext_def closed_subset_def
  by auto (metis Nitpick.size_list_simp(2) One_nat_def distinct_length_2_or_more list.exhaust_sel not_numeral_le_zero numeral_le_one_iff semiring_norm(69))

lemma link_ext_link_ext_commute_length_ge2:
  assumes l: "2 \<le> length l" and d: "distinct l"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K" 
  shows "link_ext (hd l) (set l - {hd (tl l)}) (link_ext (hd (tl l)) (set l) K) = 
          link_ext (hd (tl l)) (set l - {hd l}) (link_ext (hd l) (set l) K)"
  using l d K cs unfolding  link_ext_def closed_subset_def
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
        unfolding link_ext_def vertex_of_simpl_complex_def  by auto
      show "hd l # tl (tl l) \<noteq> []" by simp
      show "distinct (hd l # tl (tl l))" using d
        by (metis distinct_length_2_or_more distinct_singleton list.collapse tl_Nil)
      show "hd (tl l) \<notin> set (hd l # tl (tl l))" using d l o_m_c
        by (metis distinct.simps(2) distinct_tl l_e l_ne list.collapse ordered_m_collapsible.simps(1) set_ConsD)
      show "K \<subseteq> powerset (set (hd l # tl (tl l)))" using K f cs
        unfolding  vertex_of_simpl_complex_def closed_subset_def
        by (smt (verit) Diff_insert_absorb \<open>hd (tl l) \<notin> set (hd l # tl (tl l))\<close> c_K cost_closed insert_commute list.exhaust_sel list.simps(15) o_m_c_c
            ordered_m_collapsible.simps(1)  tl_Nil)
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
            using K unfolding cost_def  by auto
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
                using Bp c unfolding cost_def  by auto
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

lemma nat_induct_2 [case_names 0 1 Suc, induct type: nat]:
  fixes n
  assumes p0: "P 0" and p1: "P 1" and f: "\<And>n. n \<ge> 1 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
proof (induct rule: nat_induct)
  case 0
  show ?case using p0 .
next
  case (Suc n)
  then show ?case using p1 f
    by (metis One_nat_def leI less_one)
qed

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

text\<open>Proposition 4.1 as stated in our paper in DML\<close>

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
    using closed_subset_singleton_cases [of K v] "1.prems" (4,5) unfolding closed_subset_def by auto
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
    have "cost (hd l) (set l) K = {{}}" 
      unfolding Ks1 cost_def  lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" 
      unfolding Ks1 link_ext_def  lv list.sel by auto
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
    have "cost (hd l) (set l) K = {{}}" 
      unfolding 3 cost_def  lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" 
      unfolding 3 link_ext_def  lv list.sel by auto
    ultimately show ?thesis by (simp add: collapses_rtrancl_def)
  next
    case 4
    have "cost (hd l) (set l) K = {{},{w}}" 
      unfolding 4 cost_def  lv list.sel using vw by auto
    moreover have "link_ext (hd l) (set l) K = {}" 
      unfolding 4 link_ext_def  lv list.sel using vw by auto
    ultimately show ?thesis
      by (metis (no_types, lifting) collapsible_def insert_commute mem_Collect_eq singleton_collapsable)
  next
    case 5
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v, w]) {{}, {v}, {w}} = {{},{w}}"
      unfolding 5 cost_def  lv list.sel using vw by auto
    have l: "link_ext v (set [v, w]) {{}, {v}, {w}} = {{}}"
      unfolding 5 link_ext_def  lv list.sel using vw by auto
    have False using "2.prems" (1)
      unfolding ordered_zero_collapsible.simps (3) [OF l1, of K]
      unfolding 5 unfolding lv list.sel
      unfolding c l
      by (metis Diff_insert_absorb c cone_peak_cost_eq_link_ext insert_absorb insert_not_empty l
          list.sel(1) list.set_intros(1) not_cone_peak_cc_empty the_elem_eq)
    thus ?thesis by (rule ccontr)
  next
    case 6
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}"
      unfolding 6 cost_def  lv list.sel using vw by auto
    have l: "link_ext v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}" 
      unfolding 6 link_ext_def  lv list.sel using vw by auto
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
          (oz) "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))" 
    by auto
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
    have stll: "set (tl l) = set l - {hd l}" using Suc.prems (2,3)
      by (metis list.exhaust_sel remove1_head set_remove1_eq)
    have hyp: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K),
                  link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
    proof (rule "Suc.hyps" (2))
      show "n = length (tl l)" by (metis Suc.hyps(3) diff_Suc_1 length_tl)
      show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using ozccost .
      show "distinct (tl l)" using distinct_tl [OF Suc.prems (2)] .
      show "tl l \<noteq> []" using Suc.hyps(1) \<open>n = length (tl l)\<close> by force
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        unfolding stll by (rule cost_closed [OF Suc.prems (4)])
      show "closed_subset (cost (hd l) (set l) K)"
        by (rule closed_subset_cost [OF Suc.prems (4) Suc.prems (5)])
    qed
    have c: "cost (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
    proof (rule proposition_2 [of "cost (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        unfolding stll by (rule cost_closed [OF Suc.prems (4)])
      show "closed_subset (cost (hd l) (set l) K)"
        by (rule closed_subset_cost [OF Suc.prems (4) Suc.prems (5)])
    qed
    have le: "link_ext (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
    proof (rule proposition_2 [of "link_ext (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        unfolding stll by (rule link_ext_closed [OF Suc.prems (4)])
      show "closed_subset (link_ext (hd l) (set l) K)" 
        by (rule link_ext_closed_subset [OF Suc.prems (5)])
    qed
    have hdtl: "hd (tl l) \<in> set (tl l)" using l2 using cplink not_cone_outer_vertex by blast
    have link_join: "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
        = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
      unfolding join_vertex_def join_def by auto
    show ?thesis
    proof (subst c, subst le, unfold cone_peak_cost_eq_link_ext [OF hdtl cplink], 
            unfold link_join, rule union_join_collapses_join [of "set (tl (tl l))"])
      show "finite (set (tl (tl l)))" by simp
      show "hd (tl l) \<notin> set (tl (tl l))" using Suc.prems (2) l2
        by (metis distinct.simps(2) empty_iff list.collapse list.set(1) tl_Nil)
      hence stltll: "set (tl (tl l)) = set (tl l) - {hd (tl l)}" using Suc.prems (2,3) hdtl
        by (metis Zero_neq_Suc distinct_tl gr0_conv_Suc length_pos_if_in_set list.exhaust_sel list.size(3) remove1_head set_remove1_eq)
      show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        by (subst stltll, rule cost_closed, subst stll, rule cost_closed [OF Suc.prems (4)])
      show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        by (subst stltll, rule link_ext_closed, subst stll, rule cost_closed [OF Suc.prems (4)])
      show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
        by (rule closed_subset_link_ext, subst stll, rule cost_closed [OF Suc.prems (4)],
                rule closed_subset_cost [OF Suc.prems (4,5)])
      show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set (tl (tl l)))"
        by (subst stltll, rule link_ext_closed, subst stll, rule link_ext_closed [OF Suc.prems (4)])
      show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
        by (rule closed_subset_link_ext, subst stll, rule link_ext_closed [OF Suc.prems (4)],
                rule closed_subset_link_ext [OF Suc.prems (4,5)])
      show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
        by (rule link_ext_mono, rule link_ext_subset_cost [OF Suc.prems (5)])
      show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
        using hyp .
    qed
  qed
qed

lemma not_cone_first_second:
  assumes d: "distinct l" and l: "l \<noteq> []" and tlne: "tl l \<noteq> []"
    and cl_ne_ll: "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<noteq> link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
    and ncp: "\<not> cone_peak (set l) K (hd l)"
  shows "\<not> cone_peak (set l) K (hd (tl l))"
proof (rule ccontr, unfold not_not)
  assume cp: "cone_peak (set l) K (hd (tl l))"
  have tl: "hd (tl l) \<in> set (tl l)" using tlne by simp
  have dhd: "hd (tl l) \<noteq> hd l" using d l tlne tl
    by (metis distinct.simps(2) list.collapse)
  have shdtl: "set (hd l # tl (tl l)) = set l - {hd (tl l)}" using l tl d
    by (metis (no_types, lifting) empty_iff empty_set list.exhaust_sel remove1.simps(2) set_remove1_eq)
  have stl: "set (tl l) = set l - {hd l}" using l d
    by (metis list.exhaust_sel remove1_head set_remove1_eq)
  have "cost (hd (tl l)) (set l) K = link_ext (hd (tl l)) (set l) K"
    using cone_peak_cost_eq_link_ext [OF _ cp] tl l by (simp add: list.set_sel(2))
  hence lc_eq_ll: "link_ext (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K) 
    = link_ext (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K)"
    by simp
  have lhs: "link_ext (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K) =
        cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
    by (subst shdtl, subst stl, rule link_ext_cost_commute, 
          rule list.set_sel (2) [OF l tl], rule list.set_sel (1) [OF l], intro dhd)
  have rhs: "link_ext (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K) 
    = link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
    by (subst shdtl, subst stl, rule link_ext_commute,
          rule list.set_sel (2) [OF l tl], rule list.set_sel (1) [OF l])
  from lc_eq_ll rhs lhs and cl_ne_ll show False by simp
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
    using closed_subset_singleton_cases [of K v] using "1.prems" (4,5) unfolding closed_subset_def by auto
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
    have "cost (hd l) (set l) K = {{}}" 
      unfolding Ks1 cost_def  lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" 
      unfolding Ks1 link_ext_def  lv list.sel by auto
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
    have False using "2.prems" (1,3) unfolding 2
      using not_ordered_m_collapsible_not_empty by blast
    thus ?thesis by (rule ccontr)
  next
    case 3
    have "cost (hd l) (set l) K = {{}}" 
      unfolding 3 cost_def  lv list.sel by auto
    moreover have "link_ext (hd l) (set l) K = {{}}" 
      unfolding 3 link_ext_def  lv list.sel by auto
    ultimately show ?thesis by (simp add: collapses_rtrancl_def)
  next
    case 4
    have "cost (hd l) (set l) K = {{},{w}}"
      unfolding 4 cost_def  lv list.sel using vw by auto
    moreover have "link_ext (hd l) (set l) K = {}" 
      unfolding 4 link_ext_def  lv list.sel using vw by auto
    ultimately show ?thesis
      by (metis (no_types, lifting) collapsible_def insert_commute mem_Collect_eq singleton_collapsable)
  next
    case 5
    have l0: "0 < length l" using lv by simp
    have c: "cost v (set [v, w]) {{}, {v}, {w}} = {{},{w}}"
      unfolding 5 cost_def  lv list.sel using vw by auto
    have l: "link_ext v (set [v, w]) {{}, {v}, {w}} = {{}}" 
      unfolding 5 link_ext_def  lv list.sel using vw by auto
    have not_cone: "\<not> cone_peak (set [v, w]) {{}, {v}, {w}} v"
      unfolding cone_peak_def using vw c l
      using cone_impl_cost_eq_link_ext  c l by force
    moreover have "\<not> ordered_m_collapsible (1 - 1) (tl l) (link_ext (hd l) (set l) K)"
      unfolding lv 5 list.sel unfolding l
      using not_ordered_m_collapsible_not_empty by blast
    ultimately have False
      using "2.prems" (1) unfolding ordered_m_collapsible.simps (3) [OF l0 zero_less_one]
      unfolding 5 unfolding lv list.sel by simp
    thus ?thesis by (rule ccontr)
  next
    case 6
    have l1: "1 < length l" using lv by simp
    have c: "cost v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}"
      unfolding 6 cost_def  lv list.sel using vw by auto
    have l: "link_ext v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}"
      unfolding 6 link_ext_def  lv list.sel using vw by auto
    show ?thesis unfolding 6 lv list.sel unfolding c l
      using collapses_rtrancl_def by blast
  qed
next
  case (Suc n l)
  have l0: "0 < length l" using Suc.hyps(1,3) by auto
  have ltl0: "0 < length (tl l)" using Suc.hyps(1,3) by auto
  have l1: "1 \<le> length l" using Suc.hyps(1,3) by auto
  show ?case
  proof (cases "cone_peak (set l) K (hd l)")
    case True
    have "cost (hd l) (set l) K = link_ext (hd l) (set l) K"
      by (rule cone_peak_cost_eq_link_ext, rule list.set_sel (1) [OF Suc.prems (3)], intro True)
    thus ?thesis by (simp add: collapses_rtrancl_def)
  next
    case False note ncp = False
    have stl: " set (tl l) = set l - {hd l}" 
      using Suc.prems (2,3) by (metis list.collapse remove1_head set_remove1_eq)
    have hdtl: "hd (tl l) \<in> set (tl l)" using ltl0 by fastforce
    have ozccost: "ordered_m_collapsible 1 (tl l) (cost (hd l) (set l) K)"
      and ozlink: "ordered_zero_collapsible (tl l) (link_ext (hd l) (set l) K)"
      using ordered_m_collapsible.simps (3) [OF l0 zero_less_one, of K]
      using ordered_m_collapsible.simps (2) [OF ltl0, of _ "link_ext (hd l) (set l) K"] 
      using Suc.prems (1) False by simp_all
    have hyp1: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
    proof (rule "Suc.hyps" (2))
      show "n = length (tl l)" by (metis Suc.hyps(3) diff_Suc_1 length_tl)
      show "ordered_m_collapsible 1 (tl l) (cost (hd l) (set l) K)" using ozccost .
      show "distinct (tl l)" by (simp add: Suc.prems(2) distinct_tl)
      show "tl l \<noteq> []" using Suc.hyps(1) \<open>n = length (tl l)\<close> by force
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        by (subst stl, rule cost_closed [OF Suc.prems (4)])
      show "closed_subset (cost (hd l) (set l) K)" by (rule closed_subset_cost [OF Suc.prems (4,5)])
    qed
    have hyp2: "(cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K), 
                  link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) \<in> collapses_rtrancl"
    proof (rule ozc_cost_collapses_link_ext)
      show "ordered_zero_collapsible (tl l) (link_ext (hd l) (set l) K)" using ozlink .
      show "distinct (tl l)" using distinct_tl [OF Suc.prems (2)] .
      show "tl l \<noteq> []" using ltl0 by blast
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        by (subst stl, rule link_ext_closed [OF Suc.prems (4)])
      show "closed_subset (link_ext (hd l) (set l) K)"
        by (rule closed_subset_link_ext [OF Suc.prems (4,5)])
    qed
    have c: "cost (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
    proof (rule proposition_2 [of "cost (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        by (subst stl, rule cost_closed [OF Suc.prems (4)])
      show "closed_subset (cost (hd l) (set l) K)" 
        by (rule closed_subset_cost [OF Suc.prems (4,5)])
    qed
    have le: "link_ext (hd l) (set l) K =
      cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
    proof (rule proposition_2 [of "link_ext (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        by (subst stl, rule link_ext_closed [OF Suc.prems (4)])
      show "closed_subset (link_ext (hd l) (set l) K)" 
        by (rule link_ext_closed_subset, intro Suc.prems (5))
    qed
    have link_link_join: "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
        = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
      by (rule join_vertex_union_sub)
    have link_cost_join: "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))
        = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
      by (rule join_vertex_union_sub)
    show ?thesis
    proof (cases "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) = link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)")
      case True note cl_eq_ll = True
      show ?thesis
      proof (cases "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) = link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)")
        case True
        show ?thesis
        proof (subst c, subst le, unfold True, unfold cl_eq_ll, unfold link_link_join, rule union_join_collapses_join [of "set l - {hd (tl l)}"])
          show "finite (set l - {hd (tl l)})"  by simp
          show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
          show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})" 
            unfolding  link_ext_def cost_def by auto
          thus "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})" .
          show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
            by (rule closed_subset_link_ext, subst stl,
                    rule cost_closed [OF Suc.prems (4), of "hd l"],
                      rule closed_subset_cost [OF Suc.prems (4,5)])
          show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            unfolding  link_ext_def by auto
          show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
            by (rule closed_subset_link_ext, subst stl,
                rule link_ext_closed [OF Suc.prems (4), of "hd l"],
                      rule closed_subset_link_ext [OF Suc.prems (4,5)])
          show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
            by (rule link_ext_mono, rule link_ext_subset_cost, intro Suc.prems (5)) 
          show "(link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))
            \<in> collapses_rtrancl"
            using collapses_rtrancl_def by blast
        qed
      next
        case False
        show ?thesis
        proof (subst c, subst le, unfold cl_eq_ll link_link_join, rule union_join_collapses_join [of "set l - {hd (tl l)}"])
          show "finite (set l - {hd (tl l)})" by simp
          show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
          show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            unfolding cost_def  by auto
          show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            unfolding cost_def link_ext_def  by auto
          show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))" 
            by (rule closed_subset_link_ext, subst stl,
                      rule cost_closed, intro Suc.prems (4), rule closed_subset_cost,
                        intro Suc.prems (4), intro Suc.prems (5))
          show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            unfolding link_ext_def  by auto     
          show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
            by (rule closed_subset_link_ext, subst stl,
                      rule link_ext_closed, intro Suc.prems (4), rule closed_subset_link_ext,
                        intro Suc.prems (4), intro Suc.prems (5))
          show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
            by (rule link_ext_mono, rule link_ext_subset_cost, intro Suc.prems (5))
          show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
            using hyp1 .
        qed
      qed
    next
      case False note cl_ne_ll = False
      show ?thesis
      proof (cases "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) = link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)")
        case True
        show ?thesis
        proof (subst c, subst le, unfold True link_cost_join, rule join_collapses_union [of "set l - {hd (tl l)}"])
          show "finite (set l - {hd (tl l)})" by simp
          show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
          show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            unfolding link_ext_def cost_def  by auto
          show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
            by (rule closed_subset_link_ext, subst stl,
                      rule cost_closed, intro Suc.prems (4), rule closed_subset_cost,
                        intro Suc.prems (4), intro Suc.prems (5))
          show "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            using Suc.prems (4) unfolding link_ext_def cost_def  by auto
          show "closed_subset (cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
            by (rule closed_subset_cost, subst stl,
                      rule link_ext_closed, intro Suc.prems (4), rule closed_subset_link_ext,
                        intro Suc.prems (4), intro Suc.prems (5))
          show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
            using Suc.prems (4) unfolding link_ext_def  by auto            
          show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
            by (rule closed_subset_link_ext, subst stl,
                      rule link_ext_closed, intro Suc.prems (4), rule closed_subset_link_ext,
                        intro Suc.prems (4), intro Suc.prems (5))
          show "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
            using link_ext_cost_commute [of "hd l" "set l" "hd (tl l)" K] Suc.prems(3,4,5) True
            by (metis closed_subset_link_eq_link_ext cost_mono link_subset_cost set_empty2)
         show "(cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
     \<in> collapses_rtrancl" using hyp2 .
       qed
     next
       case False
       have tlne: "tl l \<noteq> []" using ltl0 by fastforce
       have l_decom: "l = hd l # hd (tl l) # tl (tl l)"
         using Suc.hyps (1,3) Suc.prems (3) ltl0 by force
       have set_l_decom: "set l = set (hd (tl l) # hd l # tl (tl l))"
         using l_decom by (metis insert_commute list.simps(15))
       have hdtll: "hd (tl l) \<in> set l" using l_decom hdtl ltl0 stl by auto
       have hdl: "hd l \<in> set l" using ltl0 Suc.prems (3) by simp
       have hddistinct: "hd (tl l) \<noteq> hd l" using Suc.prems (2) l_decom
         by auto (metis distinct_length_2_or_more)
       have sltl: "set l - {hd (tl l)} = set (hd l # tl (tl l))" 
         using l_decom Suc.prems (2)
         by (metis remove1.simps(2) set_remove1_eq)
       have sl: "set (hd (tl l) # hd l # tl (tl l)) = set l"
         using Suc.hyps (1,3) Suc.prems (3) ltl0
         by (metis Suc.prems(3) insert_commute length_greater_0_conv list.collapse list.simps(15))
       have ncp_tl: "\<not> cone_peak (set (hd (tl l) # hd l # tl (tl l))) K (hd (tl l))"
         by (subst set_l_decom [symmetric], rule not_cone_first_second,
             rule Suc.prems (2), rule Suc.prems (3), rule tlne, rule cl_ne_ll, rule ncp)
       have "(cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K),
                link_ext (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K)) \<in> collapses_rtrancl"
       proof (rule Suc.hyps (2) [of "(hd l) # (tl (tl l))" "cost (hd (tl l)) (set l) K"])
         show "n = length (hd l # tl (tl l))" using Suc.hyps (3) using ltl0 by auto
         show "ordered_m_collapsible 1 (hd l # tl (tl l)) (cost (hd (tl l)) (set l) K)"
         proof -
           have l0: "0 < length ((hd (tl l)) # (hd l) # (tl (tl l)))" by simp
           have omc1: "ordered_m_collapsible 1 ((hd (tl l)) # (hd l) # (tl (tl l))) K"
           proof (rule ordered_m_collapsible_swap_main)
             show "2 \<le> length l" using Suc.hyps(1,3) by fastforce
             show "distinct l" using Suc.prems (2) .
             show "K \<subseteq> powerset (set l)" using Suc.prems (4) .
             show "closed_subset K" using Suc.prems (5) .
             show "0 < (1::nat)" using zero_less_one .
             show "ordered_m_collapsible 1 l K" using Suc.prems (1) .
             show "\<not> cone_peak (set l) K (hd l)" using ncp .
             show "\<not> cone_peak (set (tl l)) (cost (hd l) (set l) K) (hd (tl l))"
               using False cone_peak_cost_eq_link_ext [OF hdtl, of "cost (hd l) (set l) K"] by blast
             show "\<not> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
               using cl_ne_ll cone_peak_cost_eq_link_ext [OF hdtl, of "link_ext (hd l) (set l) K"] by blast
           qed
           show ?thesis
             using ncp_tl
             using ordered_m_collapsible.simps (3) [OF l0 zero_less_one, of K] 
             unfolding list.sel unfolding sl
             using omc1 by fastforce
         qed
         show "distinct (hd l # tl (tl l))" using Suc.prems (2,3) ltl0
           by (metis distinct_length_2_or_more hd_Cons_tl length_0_conv less_numeral_extra(3))
         show "hd l # tl (tl l) \<noteq> []" by simp
         show "cost (hd (tl l)) (set l) K \<subseteq> powerset (set (hd l # tl (tl l)))"
           using Suc.prems (2,3,4) ltl0 unfolding  cost_def
           by auto (metis DiffE in_mono insertCI length_greater_0_conv list.exhaust_sel ltl0 set_ConsD)
           show "closed_subset (cost (hd (tl l)) (set l) K)" 
             using Suc.prems (5)
             unfolding  cost_def closed_subset_def by auto
         qed
         hence cc_lc_cl: "(cost (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K),
                link_ext (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K)) \<in> collapses_rtrancl" 
           unfolding list.sel .
         hence cc_cl_cl: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
            \<in> collapses_rtrancl"
         proof -
           have hdtll: "hd (tl l) \<in> set l" using l_decom hdtl ltl0 stl by auto
           have hdl: "hd l \<in> set l" using ltl0 Suc.prems (3) by simp
           have hddistinct: "hd (tl l) \<noteq> hd l"
             using Suc.prems (2) l_decom
             by auto (metis distinct_length_2_or_more)
           have sltl: "set l - {hd (tl l)} = set (hd l # tl (tl l))" 
             using l_decom Suc.prems (2)
             by (metis remove1.simps(2) set_remove1_eq)
           have "link_ext (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K) 
                  = cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
             using link_ext_cost_commute [OF hdtll hdl hddistinct] unfolding sltl stl by simp
           thus ?thesis using cc_lc_cl hdl hdtll sltl stl by (metis cost_commute)
         qed
      have "(cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K),
                link_ext (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K)) \<in> collapses_rtrancl"
       proof (rule ozc_cost_collapses_link_ext)
         show "ordered_zero_collapsible (hd l # tl (tl l)) (link_ext (hd (tl l)) (set l) K)"
         proof -
           have l0: "0 < length ((hd (tl l)) # (hd l) # (tl (tl l)))" by simp
           have omc1: "ordered_m_collapsible 1 ((hd (tl l)) # (hd l) # (tl (tl l))) K"
           proof (rule ordered_m_collapsible_swap_main)
             show "2 \<le> length l" using Suc.hyps(1,3) by fastforce
             show "distinct l" using Suc.prems (2) .
             show "K \<subseteq> powerset (set l)" using Suc.prems (4) .
             show "closed_subset K" using Suc.prems (5) .
             show "0 < (1::nat)" using zero_less_one .
             show "ordered_m_collapsible 1 l K" using Suc.prems (1) .
             show "\<not> cone_peak (set l) K (hd l)" using ncp .
             show "\<not> cone_peak (set (tl l)) (cost (hd l) (set l) K) (hd (tl l))"
               using False cone_peak_cost_eq_link_ext [OF hdtl, of "cost (hd l) (set l) K"] by blast
             show "\<not> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
               using cl_ne_ll cone_peak_cost_eq_link_ext [OF hdtl, of "link_ext (hd l) (set l) K"] by blast
           qed
           show ?thesis 
             using ncp_tl
             using ordered_m_collapsible.simps (3) [OF l0 zero_less_one, of K]
             unfolding list.sel unfolding sl
             using omc1 by fastforce
         qed
         show "distinct (hd l # tl (tl l))" using Suc.prems (2,3) ltl0
           by (metis distinct_length_2_or_more hd_Cons_tl length_0_conv less_numeral_extra(3))
         show "hd l # tl (tl l) \<noteq> []" by simp
         show "link_ext (hd (tl l)) (set l) K \<subseteq> powerset (set (hd l # tl (tl l)))"
           using Suc.prems (2,3,4) ltl0 unfolding  link_ext_def
           by auto (metis in_mono length_greater_0_conv list.exhaust_sel ltl0 set_ConsD)
         show "closed_subset (link_ext (hd (tl l)) (set l) K)"
           by (rule closed_subset_link_ext [OF Suc.prems (4,5)])
       qed
       hence cl_ll_cl: "(cost (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K),
                link_ext (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K)) \<in> collapses_rtrancl" 
         unfolding list.sel .
       hence lc_ll_tl: "(link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
    \<in> collapses_rtrancl"
       proof -
         have hdtll: "hd (tl l) \<in> set l" using ltl0 hdtl stl by auto
         have hdl: "hd l \<in> set l" using ltl0 Suc.prems (3) by simp thm hddistinct
         have sltl: "set l - {hd (tl l)} = set (hd l # tl (tl l))"
         proof
           show "set l - {hd (tl l)} \<subseteq> set (hd l # tl (tl l))" 
             using l0 by auto (metis length_greater_0_conv list.exhaust_sel ltl0 set_ConsD)
           show "set (hd l # tl (tl l)) \<subseteq> set l - {hd (tl l)}"
             using ltl0 l0 Suc.prems (2) hddistinct length_greater_0_conv
             apply auto
              apply (metis less_irrefl_nat list.set_sel(2) list.size(3) ltl0)
             by (metis distinct.simps(2) length_greater_0_conv list.exhaust_sel ltl0)
         qed
         have "cost (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K) = 
            link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
           using link_ext_cost_commute [OF hdl hdtll hddistinct [symmetric]] unfolding sltl stl by simp
         thus ?thesis using cl_ll_cl hdl hdtll sltl stl by (metis link_ext_commute)
       qed
       show ?thesis
       proof (subst c, subst le, rule union_join_collapses_twice [of "set l - {hd (tl l)}"])
         show "finite (set l - {hd (tl l)})" by simp
         show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
         show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
           unfolding cost_def  by auto
         show "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
           unfolding cost_def link_ext_def  by auto
         show "closed_subset (cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
           by (rule closed_subset_cost, subst stl, rule link_ext_closed [OF Suc.prems (4)], 
                rule closed_subset_link_ext [OF Suc.prems (4,5)])
         show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
           unfolding cost_def link_ext_def  by auto
         show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
           by (rule closed_subset_link_ext, subst stl, rule cost_closed [OF Suc.prems (4)], 
                rule closed_subset_cost [OF Suc.prems (4,5)])
         show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
           unfolding cost_def link_ext_def  by auto
         show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
           by (rule closed_subset_link_ext, subst stl, rule link_ext_closed [OF Suc.prems (4)], 
                rule closed_subset_link_ext [OF Suc.prems (4,5)])
         show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
           by (rule link_ext_subset_cost, rule closed_subset_cost [OF Suc.prems (4,5)])
         show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
           by (rule link_ext_subset_cost, rule closed_subset_link_ext [OF Suc.prems (4,5)])
         show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                  cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) \<in> collapses_rtrancl"
           using cc_cl_cl .
         show "(link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                  link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) \<in> collapses_rtrancl"
            using lc_ll_tl .
        qed
      qed
    qed
  qed
qed

theorem ordered_m_collapsible_cost_collapses_link_ext:
  assumes ozc: "ordered_m_collapsible m l K" and d: "distinct l"
    and lne: "l \<noteq> []"
    and K: "K \<subseteq> powerset (set l)" and cs: "closed_subset K"
  shows "(cost (hd l) (set l) K, link_ext (hd l) (set l) K) \<in> collapses_rtrancl"
using ozc d lne K cs proof (induct m arbitrary: l K rule: nat_less_induct)
  case (1 m)
  then show ?case
  proof (cases "m = 0")
    case True
    have l0: "0 < length l" using "1.prems" (3) by simp
    show ?thesis
    proof (rule ozc_cost_collapses_link_ext)
    show "ordered_zero_collapsible l K"
      using "1.prems" (1) unfolding True
      using ordered_m_collapsible.simps (2) [OF l0, of 0] by simp
    show "distinct l" using "1.prems" (2) .
    show "l \<noteq> []" using "1.prems" (3) .
    show "K \<subseteq> powerset (set l)" using "1.prems" (4) .
    show "closed_subset K" using "1.prems" (5) .
  qed
  next
    case False
    note mn0 = False
    show ?thesis
    proof (cases "m = 1")
      case True
      have l0: "0 < length l" using "1.prems" (3) by simp
      show ?thesis
      proof (rule ordered_one_collapsible_cost_collapses_link_ext)
        show "ordered_m_collapsible 1 l K"
          using "1.prems" (1) unfolding True
          using ordered_m_collapsible.simps (2) [OF l0, of 0] by simp
        show "distinct l" using "1.prems" (2) .
        show "l \<noteq> []" using "1.prems" (3) .
        show "K \<subseteq> powerset (set l)"  using "1.prems" (4) .
        show "closed_subset K"  using "1.prems" (5) .
      qed
    next
      case False
      have m2: "2 \<le> m" using False mn0 by auto
      show ?thesis
        using "1.hyps" (1) "1.prems" (1,2,3,4,5) m2 proof (induct "length l" arbitrary: l m K rule: nat_induct_3)
        case 0
        from "0.prems" (4) and "0.hyps" have False by simp thus ?case by (rule ccontr)
      next
        case (1 l)
        from "1.hyps" obtain v where lv: "l = [v]" by (metis One_nat_def length_0_conv length_Suc_conv)
        have "K = {} | K = {{}} | K = {{}, {v}}"
          using closed_subset_singleton_cases [of K "v"] using "1.prems" (5,6) 
          unfolding lv by auto
        then consider (Ke) "K = {}" | (Ks) "K = {{}}" | (Ks1) "K = {{}, {v}}" by auto
        then show ?case
        proof (cases)
          case Ke
          show ?thesis unfolding Ke unfolding link_ext_empty cost_empty
            using collapses_rtrancl_def by blast
        next
          case Ks hence False 
            using "1.prems" (2,4) unfolding Ks
            using not_ordered_m_collapsible_not_empty by blast
          thus ?thesis by (rule ccontr)
        next
          case Ks1
          have "cost (hd l) (set l) K = {{}}" 
            unfolding Ks1 cost_def  lv list.sel by auto
          moreover have "link_ext (hd l) (set l) K = {{}}" 
            unfolding Ks1 link_ext_def  lv list.sel by auto
          ultimately show ?thesis by (simp add: collapses_rtrancl_def)
        qed
      next
        case 2
        from "2.hyps" and "2.prems" (3) obtain v w where lv: "l = [v,w]" and vw: "v \<noteq> w"
          by (metis One_nat_def Suc_1 diff_Suc_1 distinct_length_2_or_more 
              length_0_conv length_tl list.exhaust_sel nat.simps(3))
        have "K = {} | K = {{}} | K = {{}, {v}} | K = {{}, {w}} | K = {{}, {v}, {w}} | K = {{}, {v}, {w}, {v,w}}"
          using cs_card_leq_2 [OF "2.prems" (5) _ vw "2.prems" (6)] using lv by simp
        then consider "K = {}" | "K = {{}}" | "K = {{}, {v}}" | "K = {{}, {w}}" 
          | "K = {{}, {v}, {w}}" | "K = {{}, {v}, {w}, {v,w}}" by fastforce
        then show ?case proof (cases)
          case 1
          show ?thesis unfolding 1 unfolding link_ext_empty cost_empty
            using collapses_rtrancl_def by blast
        next
          case 2
          have False 
            using "2.prems" (2,4) not_ordered_m_collapsible_not_empty unfolding 2
            by blast
          thus ?thesis by (rule ccontr)
        next
          case 3
          have "cost (hd l) (set l) K = {{}}" unfolding 3 cost_def  lv list.sel by auto
          moreover have "link_ext (hd l) (set l) K = {{}}" unfolding 3 link_ext_def  lv list.sel by auto
          ultimately show ?thesis by (simp add: collapses_rtrancl_def)
        next
          case 4
          have "cost (hd l) (set l) K = {{},{w}}"
            unfolding 4 cost_def  lv list.sel using vw by auto
          moreover have "link_ext (hd l) (set l) K = {}" 
            unfolding 4 link_ext_def  lv list.sel using vw by auto
          ultimately show ?thesis
            by (metis (no_types, lifting) collapsible_def insert_commute mem_Collect_eq singleton_collapsable)
        next
          case 5
          have l0: "0 < length l" using lv by simp
          have c: "cost v (set [v, w]) {{}, {v}, {w}} = {{},{w}}"
            unfolding 5 cost_def  lv list.sel using vw by auto
          have l: "link_ext v (set [v, w]) {{}, {v}, {w}} = {{}}" 
            unfolding 5 link_ext_def  lv list.sel using vw by auto
          have not_cone: "\<not> cone_peak (set [v, w]) {{}, {v}, {w}} v"
            unfolding cone_peak_def using vw c l
            using cone_impl_cost_eq_link_ext  c l by force
          moreover have "\<not> ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
            unfolding lv 5 list.sel unfolding l
            using not_ordered_m_collapsible_not_empty by blast
          ultimately have False
            using "2.prems" (2)
            unfolding ordered_m_collapsible.simps (3) [OF ]
            unfolding 5 lv list.sel using "2.prems" (7) by simp
          thus ?thesis by (rule ccontr)
        next
          case 6
          have l1: "1 < length l" using lv by simp
          have c: "cost v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}"
            unfolding 6 cost_def  lv list.sel using vw by auto
          have l: "link_ext v (set [v,w]) {{}, {v}, {w}, {v,w}} = {{},{w}}" 
            unfolding 6 link_ext_def  lv list.sel using vw by auto
          show ?thesis unfolding 6 lv list.sel unfolding c l
            using collapses_rtrancl_def by blast
        qed
      next
        case (Suc n l)
        have m0: "0 < m" using Suc.prems (7) by simp
        have l0: "0 < length l" using Suc.hyps(1,3) by auto
        have ltl0: "0 < length (tl l)" using Suc.hyps(1,3) by auto
        have l1: "1 \<le> length l" using Suc.hyps(1,3) by auto
        have stl: "set (tl l) = set l - {hd l}" using Suc.prems (3,4)
          by (metis list.exhaust_sel remove1_head set_remove1_eq)
        show ?case
        proof (cases "cone_peak (set l) K (hd l)")
          case True
          have "cost (hd l) (set l) K = link_ext (hd l) (set l) K"
          proof (rule cone_peak_cost_eq_link_ext)
            show "hd l \<in> set l" using Suc.prems (4) by simp
            show "cone_peak (set l) K (hd l)" using True .
          qed
          thus ?thesis by (simp add: collapses_rtrancl_def)
        next
          case False note ncp = False
          then have omccost: "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)"
            and om1clink: "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)"
            using ordered_m_collapsible.simps (3) [OF l0, of _ K] 
            using Suc.prems (2) Suc.prems (7) by simp_all
          have hyp1: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                        link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
          proof (rule "Suc.hyps" (2) [of _ m])
            show "n = length (tl l)" by (metis Suc.hyps(3) diff_Suc_1 length_tl)
            show "\<forall>k<m. \<forall>x xa.
             ordered_m_collapsible k x xa \<longrightarrow>
             distinct x \<longrightarrow>
             x \<noteq> [] \<longrightarrow>
             xa \<subseteq> powerset (set x) \<longrightarrow> closed_subset xa \<longrightarrow> (cost (hd x) (set x) xa, link_ext (hd x) (set x) xa) \<in> collapses_rtrancl" 
              using Suc.prems (1) .
            show "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" using omccost .
            show "distinct (tl l)" by (simp add: Suc.prems(3) distinct_tl)
            show "tl l \<noteq> []" using Suc.hyps(1) \<open>n = length (tl l)\<close> by force
            show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
              by (subst stl, rule cost_closed [OF Suc.prems (5)])
            show "closed_subset (cost (hd l) (set l) K)"
              by (rule closed_subset_cost [OF Suc.prems (5,6)])
            show "2 \<le> m" using Suc.prems (7) .
          qed
          have hyp2: "(cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) \<in> collapses_rtrancl"
          proof (cases "1 = m - 1")
            case True
            show ?thesis
            proof (rule ordered_one_collapsible_cost_collapses_link_ext)
              show "ordered_m_collapsible 1 (tl l) (link_ext (hd l) (set l) K)"
                using ordered_m_collapsible.simps (3) [OF l0 m0, of K]
                using False using True using Suc.prems (2) by simp
              show "distinct (tl l)" using distinct_tl [OF Suc.prems (3)] .
              show "tl l \<noteq> []" using Suc.prems (4) ltl0 by force
              show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
                by (subst stl, rule link_ext_closed [OF Suc.prems (5)])
              show "closed_subset (link_ext (hd l) (set l) K)"
                by (rule closed_subset_link_ext [OF Suc.prems (5,6)])
            qed
          next
            case False
            show ?thesis
            proof (rule Suc.hyps (2) [of _ "m - 1"])
              show "n = length (tl l)" by (metis Suc.hyps(3) diff_Suc_1 length_tl)
              show "\<forall>k<m-1. \<forall>x xa.
              ordered_m_collapsible k x xa \<longrightarrow>
              distinct x \<longrightarrow>
              x \<noteq> [] \<longrightarrow>
              xa \<subseteq> powerset (set x) \<longrightarrow> closed_subset xa \<longrightarrow> (cost (hd x) (set x) xa, link_ext (hd x) (set x) xa) \<in> collapses_rtrancl" 
                using Suc.prems (1)
                using less_diff_conv ordered_m_collapsible_suc by presburger
              show "ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)" using om1clink .
              show "distinct (tl l)" by (simp add: Suc.prems(3) distinct_tl)
              show "tl l \<noteq> []" using Suc.hyps(1) \<open>n = length (tl l)\<close> by force
              show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
                by (subst stl, rule link_ext_closed [OF Suc.prems (5)])
              show "closed_subset (link_ext (hd l) (set l) K)"
                by (rule closed_subset_link_ext [OF Suc.prems (5,6)])
              show "2 \<le> m - 1" using Suc.prems (7) using False by simp
            qed
          qed
          have c: "cost (hd l) (set l) K =
            cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
          proof (rule proposition_2 [of "cost (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
            show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
              by (subst stl, rule cost_closed [OF Suc.prems (5)])
            show "closed_subset (cost (hd l) (set l) K)"
              by (rule closed_subset_cost [OF Suc.prems (5,6)])
          qed
          have le: "link_ext (hd l) (set l) K =
            cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
          proof (rule proposition_2 [of "link_ext (hd l) (set l) K" "set (tl l)" "hd (tl l)"])
            show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
              by (subst stl, rule link_ext_closed [OF Suc.prems (5)])
            show "closed_subset (link_ext (hd l) (set l) K)" 
              by (rule link_ext_closed_subset, intro Suc.prems (6))
          qed
          have hdtl: "hd (tl l) \<in> set (tl l)" using ltl0 by fastforce
          have link_link_join: "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
            = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
            by (rule join_vertex_union_sub)
          have link_cost_join: "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<union> join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))
            = join_vertex (hd (tl l)) (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
            by (rule join_vertex_union_sub)
          show ?thesis
          proof (cases "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) = link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)")
            case True note cl_eq_ll = True
            show ?thesis
            proof (cases "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) = link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)")
              case True
              show ?thesis
              proof (subst c, subst le, unfold True cl_eq_ll link_link_join, rule union_join_collapses_join [of "set l - {hd (tl l)}"])
                show "finite (set l - {hd (tl l)})"  by simp
                show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
                show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding  link_ext_def cost_def by auto
                show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding  link_ext_def cost_def by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule cost_closed [OF Suc.prems (5)], 
                        rule closed_subset_cost [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding  link_ext_def by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule link_ext_closed [OF Suc.prems (5)], 
                        rule closed_subset_link_ext [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
                  by (rule link_ext_mono, rule link_ext_subset_cost [OF Suc.prems (6)])
                show "(link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                        link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
                  using collapses_rtrancl_def by blast
              qed
            next
              case False
              show ?thesis
              proof (subst c, subst le, unfold cl_eq_ll link_link_join, rule union_join_collapses_join [of "set l - {hd (tl l)}"])
                show "finite (set l - {hd (tl l)})" by simp
                show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
                show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding cost_def  by auto
                show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding cost_def link_ext_def  by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule cost_closed [OF Suc.prems (5)], 
                        rule closed_subset_cost [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding link_ext_def  by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule link_ext_closed [OF Suc.prems (5)], 
                        rule closed_subset_link_ext [OF Suc.prems (5,6)])   
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
                  by (rule link_ext_mono, rule link_ext_subset_cost [OF Suc.prems (6)])
                show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                        link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)) \<in> collapses_rtrancl"
                  using hyp1 .
              qed
            qed
          next
            case False note cl_ne_ll = False
            show ?thesis
            proof (cases "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) = link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)")
              case True
              show ?thesis
              proof (subst c, subst le, unfold True link_cost_join, rule join_collapses_union [of "set l - {hd (tl l)}"])
                show "finite (set l - {hd (tl l)})" by simp
                show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
                show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding link_ext_def cost_def  by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule cost_closed [OF Suc.prems (5)], 
                        rule closed_subset_cost [OF Suc.prems (5,6)])
                show "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding link_ext_def cost_def  by auto
                show "closed_subset (cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
                  by (rule closed_subset_cost, subst stl, rule link_ext_closed [OF Suc.prems (5)], 
                        rule closed_subset_link_ext [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding link_ext_def  by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule link_ext_closed [OF Suc.prems (5)], 
                        rule closed_subset_link_ext [OF Suc.prems (5,6)])
                show "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
                  using link_ext_cost_commute [of "hd l" "set l" "hd (tl l)" K] Suc.prems(4,5,6) True
                  by (metis closed_subset_link_eq_link_ext cost_mono link_subset_cost set_empty2)
                show "(cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
                    \<in> collapses_rtrancl" using hyp2 .
              qed
            next
              case False
              note cc_ne_lc = False
              have l_decom: "l = hd l # hd (tl l) # tl (tl l)"
                using Suc.hyps (1,3) Suc.prems (4) ltl0 by fastforce
              have set_l_decom: "set l = set (hd (tl l) # hd l # tl (tl l))"
                using l_decom by (metis insert_commute list.simps(15))
              have hdtll: "hd (tl l) \<in> set l" using l_decom hdtl ltl0 stl by auto
              have hdl: "hd l \<in> set l" using ltl0 Suc.prems (4) by simp
              have hddistinct: "hd (tl l) \<noteq> hd l"
                using Suc.prems (3) l_decom
                by auto (metis distinct_length_2_or_more)
              have tlne: "tl l \<noteq> []" using ltl0 by force
              have sltl: "set l - {hd (tl l)} = set (hd l # tl (tl l))" 
                using l_decom Suc.prems (3)
                by (metis remove1.simps(2) set_remove1_eq)
              have sl: "set (hd (tl l) # hd l # tl (tl l)) = set l"
                using Suc.hyps (1,3) Suc.prems (4) ltl0
                by (metis insert_commute length_greater_0_conv list.collapse list.simps(15))
              have ncp_tl: "\<not> cone_peak (set (hd (tl l) # hd l # tl (tl l))) K (hd (tl l))"
                by (subst set_l_decom [symmetric], rule not_cone_first_second,
                    rule Suc.prems (3), rule Suc.prems (4), rule tlne, rule cl_ne_ll, rule ncp)
              have "(cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K),
                link_ext (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K)) \<in> collapses_rtrancl"
              proof (rule Suc.hyps (2) [of "(hd l) # (tl (tl l))" m "cost (hd (tl l)) (set l) K"])
                show "n = length (hd l # tl (tl l))" using Suc.hyps (3) using ltl0 by auto
                show "\<forall>k<m. \<forall>x xa.
                  ordered_m_collapsible k x xa \<longrightarrow>
                  distinct x \<longrightarrow>
                  x \<noteq> [] \<longrightarrow>
                  xa \<subseteq> powerset (set x) \<longrightarrow> closed_subset xa \<longrightarrow> (cost (hd x) (set x) xa, link_ext (hd x) (set x) xa) \<in> collapses_rtrancl"
                  using Suc.prems (1) .
                show "ordered_m_collapsible m (hd l # tl (tl l)) (cost (hd (tl l)) (set l) K)"
                proof -
                  have l0: "0 < length ((hd (tl l)) # (hd l) # (tl (tl l)))" by simp
                  have omc1: "ordered_m_collapsible m ((hd (tl l)) # (hd l) # (tl (tl l))) K"
                  proof (rule ordered_m_collapsible_swap_main)
                    show "2 \<le> length l" using Suc.hyps(1,3) by fastforce
                    show "distinct l" using Suc.prems (3) .
                    show "K \<subseteq> powerset (set l)" using Suc.prems (5) .
                    show "closed_subset K" using Suc.prems (6) .
                    show "0 < (m::nat)" using m0 .
                    show "ordered_m_collapsible m l K" using Suc.prems (2) .
                    show "\<not> cone_peak (set l) K (hd l)" using ncp .
                    show "\<not> cone_peak (set (tl l)) (cost (hd l) (set l) K) (hd (tl l))"
                      using False cone_peak_cost_eq_link_ext [OF hdtl, of "cost (hd l) (set l) K"] by blast
                    show "\<not> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
                      using cl_ne_ll cone_peak_cost_eq_link_ext [OF hdtl, of "link_ext (hd l) (set l) K"] by blast
                  qed
                  show ?thesis
                    using omc1 unfolding ordered_m_collapsible.simps (3) [OF l0 m0, of K] 
                    using ncp_tl unfolding list.sel sl
                    by fastforce
                qed
                show "distinct (hd l # tl (tl l))" using Suc.prems (3,4) ltl0
                  by (metis distinct_length_2_or_more hd_Cons_tl length_0_conv less_numeral_extra(3))
                show "hd l # tl (tl l) \<noteq> []" by simp
                show "cost (hd (tl l)) (set l) K \<subseteq> powerset (set (hd l # tl (tl l)))"
                  using Suc.prems (3,4) ltl0 unfolding  cost_def
                  by auto (metis DiffE in_mono insertCI length_greater_0_conv list.exhaust_sel ltl0 set_ConsD)
                show "closed_subset (cost (hd (tl l)) (set l) K)" 
                  by (rule closed_subset_cost [OF Suc.prems (5,6)])
                show "2 \<le> m" using Suc.prems (7) .
                qed
                hence cc_lc_cl: "(cost (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K),
                  link_ext (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K)) \<in> collapses_rtrancl" 
                  unfolding list.sel .
                hence cc_cl_cl: "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
                  \<in> collapses_rtrancl"
                proof -
                  have "link_ext (hd l) (set (hd l # tl (tl l))) (cost (hd (tl l)) (set l) K)
                    = cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
                    using link_ext_cost_commute [OF hdtll hdl hddistinct] unfolding sltl stl by simp
                  thus ?thesis
                    using cc_lc_cl hdl hdtll sltl stl by (metis cost_commute)
                qed
                have "(cost (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K),
                  link_ext (hd (hd l # tl (tl l))) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K)) \<in> collapses_rtrancl"
                proof (cases "1 = m - 1")
                  case True
                  have l0: "0 < length ((hd (tl l)) # (hd l) # (tl (tl l)))" by simp
                  show ?thesis
                  proof (rule ordered_one_collapsible_cost_collapses_link_ext)
                    have omc2: "ordered_m_collapsible 2 ((hd (tl l)) # (hd l) # (tl (tl l))) K"
                    proof (rule ordered_m_collapsible_swap_main)
                      show "2 \<le> length l" using Suc.hyps(1,3) by fastforce
                      show "distinct l" using Suc.prems (3) .
                      show "K \<subseteq> powerset (set l)" using Suc.prems (5) .
                      show "closed_subset K" using Suc.prems (6) .
                      show "0 < (2::nat)" by simp
                      show "ordered_m_collapsible 2 l K" using Suc.prems (2) using True m0
                        by (metis Suc_1 Suc_diff_1)
                      show "\<not> cone_peak (set l) K (hd l)" using ncp .
                      show "\<not> cone_peak (set (tl l)) (cost (hd l) (set l) K) (hd (tl l))"
                        using False cone_peak_cost_eq_link_ext [OF hdtl, of "cost (hd l) (set l) K"] by blast
                      show "\<not> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
                        using cl_ne_ll cone_peak_cost_eq_link_ext [OF hdtl, of "link_ext (hd l) (set l) K"] by blast
                    qed
                    thus "ordered_m_collapsible 1 (hd l # tl (tl l)) (link_ext (hd (tl l)) (set l) K)"
                      using ordered_m_collapsible.simps (3) [OF l0, of 2 K] ncp_tl
                      unfolding list.sel sl by fastforce
                    show "distinct (hd l # tl (tl l))"
                      using Suc.prems (3) l_decom by (metis distinct_length_2_or_more)
                    show "hd l # tl (tl l) \<noteq> []" by simp
                    show "link_ext (hd (tl l)) (set l) K \<subseteq> powerset (set (hd l # tl (tl l)))"
                      using Suc.prems (5) sl unfolding  link_ext_def by auto (force)
                    show "closed_subset (link_ext (hd (tl l)) (set l) K)"
                      by (rule closed_subset_link_ext [OF Suc.prems (5,6)])
                   qed
                next
                  case False
                  show ?thesis
                  proof (rule Suc.hyps (2) [of _ "m - 1"])
                    show "n = length (hd l # tl (tl l))"
                      using Suc.hyps (3) l_decom by (metis Suc_length_conv diff_Suc_1)
                    show "\<forall>k<m - 1.
                      \<forall>x xa.
                        ordered_m_collapsible k x xa \<longrightarrow>
                        distinct x \<longrightarrow>
                        x \<noteq> [] \<longrightarrow> xa \<subseteq> powerset (set x) \<longrightarrow> closed_subset xa \<longrightarrow> (cost (hd x) (set x) xa, link_ext (hd x) (set x) xa) \<in> collapses_rtrancl"
                      using Suc.prems (1)
                      using less_diff_conv ordered_m_collapsible_suc by presburger
                    show "ordered_m_collapsible (m - 1) (hd l # tl (tl l)) (link_ext (hd (tl l)) (set l) K)"
                    proof -
                      have l0: "0 < length ((hd (tl l)) # (hd l) # (tl (tl l)))" by simp
                      have omc1: "ordered_m_collapsible m ((hd (tl l)) # (hd l) # (tl (tl l))) K"
                      proof (rule ordered_m_collapsible_swap_main)
                        show "2 \<le> length l" using Suc.hyps(1,3) by fastforce
                        show "distinct l" using Suc.prems (3) .
                        show "K \<subseteq> powerset (set l)" using Suc.prems (5) .
                        show "closed_subset K" using Suc.prems (6) .
                        show "0 < (m::nat)" using m0 .
                        show "ordered_m_collapsible m l K" using Suc.prems (2) .
                        show "\<not> cone_peak (set l) K (hd l)" using ncp .
                        show "\<not> cone_peak (set (tl l)) (cost (hd l) (set l) K) (hd (tl l))"
                          using cc_ne_lc cone_peak_cost_eq_link_ext [OF hdtl, of "cost (hd l) (set l) K"] by blast
                        show "\<not> cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
                          using cl_ne_ll cone_peak_cost_eq_link_ext [OF hdtl, of "link_ext (hd l) (set l) K"] by blast
                    qed
                    show ?thesis
                      using ncp_tl
                      using ordered_m_collapsible.simps (3) [OF l0 m0, of K]
                      unfolding list.sel unfolding sl
                      using omc1 by fastforce
                  qed
                  show "distinct (hd l # tl (tl l))" using Suc.prems (3,4) ltl0
                    by (metis distinct_length_2_or_more hd_Cons_tl length_0_conv less_numeral_extra(3))
                  show "hd l # tl (tl l) \<noteq> []" by simp
                  show "link_ext (hd (tl l)) (set l) K \<subseteq> powerset (set (hd l # tl (tl l)))"
                    by (subst sltl [symmetric], rule link_ext_closed [OF Suc.prems (5)])
                  show "closed_subset (link_ext (hd (tl l)) (set l) K)"
                    by (rule closed_subset_link_ext [OF Suc.prems (5,6)])
                  show " 2 \<le> m - 1" using False m0 Suc.prems (7) by simp
                qed
              qed
              hence cl_ll_cl: "(cost (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K),
                  link_ext (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K)) \<in> collapses_rtrancl" 
                unfolding list.sel .
              hence lc_ll_tl: "(link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))
                  \<in> collapses_rtrancl"
              proof -
                have cl_lc: "cost (hd l) (set (hd l # tl (tl l))) (link_ext (hd (tl l)) (set l) K) =
                       link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)" 
                  by (subst sltl [symmetric], subst stl,
                        rule link_ext_cost_commute [OF hdl hdtll hddistinct [symmetric], symmetric])
                show ?thesis using cl_ll_cl unfolding cl_lc
                  using hdl hdtll sltl stl by (metis link_ext_commute)
              qed
              show ?thesis
              proof (subst c, subst le, rule union_join_collapses_twice [of "set l - {hd (tl l)}"])
                show "finite (set l - {hd (tl l)})" by simp
                show "hd (tl l) \<notin> set l - {hd (tl l)}" by simp
                show "cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding cost_def  by auto
                show "cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding cost_def link_ext_def  by auto
                show "closed_subset (cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
                  by (rule closed_subset_cost, subst stl, rule link_ext_closed [OF Suc.prems (5)],
                        rule closed_subset_link_ext [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding cost_def link_ext_def  by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule cost_closed [OF Suc.prems (5)],
                        rule closed_subset_cost [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> powerset (set l - {hd (tl l)})"
                  unfolding cost_def link_ext_def  by auto
                show "closed_subset (link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K))"
                  by (rule closed_subset_link_ext, subst stl, rule link_ext_closed [OF Suc.prems (5)],
                        rule closed_subset_link_ext [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K) \<subseteq> cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K)"
                  by (rule link_ext_subset_cost, rule closed_subset_cost [OF Suc.prems (5,6)])
                show "link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K) \<subseteq> cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)"
                  by (rule link_ext_subset_cost, rule closed_subset_link_ext [OF Suc.prems (5,6)])
                show "(cost (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                        cost (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) \<in> collapses_rtrancl"
                  using cc_cl_cl .
                show "(link_ext (hd (tl l)) (set (tl l)) (cost (hd l) (set l) K), 
                        link_ext (hd (tl l)) (set (tl l)) (link_ext (hd l) (set l) K)) \<in> collapses_rtrancl"
            using lc_ll_tl .
            qed
          qed
        qed
      qed
    qed
    qed
  qed
qed

section\<open>Consequences of the main theorem.\<close>

(*definition vertex_set :: "nat set set \<Rightarrow> nat set"
  where "vertex_set K = {v::nat. {v} \<in> K}"*)

lemma assumes c: "closed_subset K" shows "K \<subseteq> powerset (vertex_of_simpl_complex K)" 
  using c unfolding  vertex_of_simpl_complex_def closed_subset_def by auto

definition facets :: "nat set set \<Rightarrow> nat set set"
  where "facets K = {a. facet a K}"

lemma shows "facet a K \<equiv> a \<in> facets K"
  unfolding facets_def by simp

lemma facets_not_empty: assumes K: "K \<noteq> {}" and f: "finite K" 
  shows "facets K \<noteq> {}"
proof -
  from K obtain v where vK: "v \<in> K" by auto
  show ?thesis
  proof (cases "facet v K")
    case True
    then show ?thesis using vK unfolding facets_def by auto
  next
    case False
    define vs where "vs = {w\<in>K. v \<subseteq> w}"
    have fvs: "finite vs" and vsne: "vs \<noteq> {}" unfolding vs_def using f vK by auto
    obtain w where wmax: "\<forall>b\<in>vs. w \<subseteq> b \<longrightarrow> w = b" and win: "w \<in> vs"
      using finite_has_maximal [OF fvs vsne] by auto
    have "facet w K" using wmax win unfolding facet_def vs_def by auto
    thus ?thesis unfolding facets_def by auto
  qed
qed

definition pure_d :: "nat \<Rightarrow> nat set set \<Rightarrow> bool"
  where "pure_d d K = (\<forall>f\<in>facets K. card f = d + 1)"

lemma shows "pure_d d {}"
  unfolding pure_d_def facets_def facet_def by simp

lemma pure_d_facet:
  assumes Kne: "K \<noteq> {}" and f: "finite K" and p: "pure_d d K"
  obtains f where "f \<in> facets K" and "card f = d + 1"
  using facets_not_empty [OF Kne f]
  using p pure_d_def by auto

lemma pure_d_card_facets: assumes p: "pure_d d K"
  shows "\<nexists>f. f \<in> facets K \<and> d + 1 < card f"
proof (rule ccontr, simp)
  assume "\<exists>f. f \<in> facets K \<and> Suc d < card f"
  then obtain f where fK: "f \<in> facets K" and cf: "d + 1 < card f" by auto
  with p show False unfolding pure_d_def facets_def facet_def by simp
qed

lemma pure_d_card: assumes p: "pure_d d K" and f: "finite K"
  shows "\<nexists>f. f \<in> K \<and> d + 1 < card f"
proof (rule ccontr, simp)
  assume "\<exists>f. f \<in> K \<and> Suc d < card f"
  then obtain f where fK: "f \<in> K" and cf: "d + 1 < card f" by auto  
  show False 
  proof (cases "f \<in> facets K")
    case True
    then show ?thesis using pure_d_card_facets [OF p] cf by simp
  next
    case False
    then obtain g where fg: "f \<subseteq> g" and gK: "g \<in> facets K" 
      using facet_exists [OF f fK] unfolding facets_def by auto
    from fg have cgg: "d + 1 < card g"
      using cf gK p
      by (metis Suc_eq_plus1 Suc_lessD card.infinite less_trans_Suc nat.simps(3) psubsetI psubset_card_mono pure_d_def)
    from pure_d_card_facets [OF p] and gK and cgg have False by simp
    thus ?thesis by (rule ccontr)
  qed
qed

text\<open>Lemma 5.1 in our paper in DML:\<close>

lemma pure_d_minus_one_link_ext: assumes K: "K \<subseteq> powerset V" and c: "closed_subset K" and d: "0 < d" 
  and p: "pure_d d K" and v: "{v} \<in> K" shows "pure_d (d - 1) (link_ext v V K)"
proof (unfold pure_d_def, rule)
  fix f
  assume f: "f \<in> facets (link_ext v V K)"
  hence "f \<in> link_ext v V K"
    unfolding facets_def
    using facet_in_K by auto
  hence vnf: "v \<notin> f" unfolding link_ext_def by simp
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
        have "b - {v} \<in> link_ext v V K" using b K i unfolding link_ext_def 
          by auto (simp add: insert_absorb)
        moreover have "f \<subset> b - {v}" using ins vnf by auto
        ultimately show False using f unfolding facets_def facet_def by auto
      qed
    qed
  qed
  show "card f = d - 1 + 1" using insf p vnf d unfolding pure_d_def
    by (metis Suc_diff_1 Suc_eq_plus1 card_Diff_singleton_if diff_Suc_1 insertI1 insert_Diff1)
qed

definition dim :: "nat set set \<Rightarrow> nat"
  where "dim K = Max {n. \<exists>k\<in>K. n = card k} - 1"

lemma "dim {{}} = 0" and "dim {{7}} = 0" and "dim {{3,7}} = 1"
  unfolding dim_def by auto

lemma pure_d_0_one_vertex:
  assumes p: "pure_d 0 K" and cs: "closed_subset K" and Kne: "K \<noteq> {}"
  and fV: "finite V" and KV: "K \<subseteq> powerset V"
  shows "1 \<le> card (vertex_of_simpl_complex K)"
proof -
  have f: "finite K" using cs fV KV by (simp add: finite_subset)
  obtain f where f: "f \<in> facets K" and cf: "card f = 1"
    using pure_d_facet [OF Kne f p] by auto
  hence fK :"f \<in> K" unfolding facets_def facet_def by simp
  have sv: "f \<subseteq> vertex_of_simpl_complex K"
    using closed_subset_vertex_of_simpl_complex [OF fK cs] by simp
  thus ?thesis
    using KV fV finite_vertex_of_simpl_complex [OF fV KV] cf
    by (metis card_mono)
qed

corollary pure_d_0_at_least_one_vertex:
  assumes p: "pure_d 0 K" and cs: "closed_subset K" and Kne: "K \<noteq> {}"
  and fV: "finite V" and KV: "K \<subseteq> powerset V"
shows "1 \<le> card V"
  using card_vertex_of_simpl_complex [OF fV KV]
  using pure_d_0_one_vertex [OF p cs Kne fV KV] by simp

lemma pure_d_n_two_vertexes:
  assumes p: "pure_d n K" and cs: "closed_subset K" and Kne: "K \<noteq> {}" 
  and fV: "finite V" and KV: "K \<subseteq> powerset V" and n: "0 < n"
  shows "2 \<le> card (vertex_of_simpl_complex K)"
proof -
  have f: "finite K" using cs fV KV by (simp add: finite_subset)
  obtain f where f: "f \<in> facets K" and cf: "card f = n + 1"
    using pure_d_facet [OF Kne f p] by auto
  hence fK :"f \<in> K" unfolding facets_def facet_def by simp
  have cf2: "2 \<le> card f" using n cf by simp
  have sv: "{v. {v} \<subseteq> f} \<subseteq> vertex_of_simpl_complex K" 
    using closed_subset_vertex_of_simpl_complex [OF fK cs] .
  have "2 \<le> card {v. {v} \<subseteq> f}" using cf2 by simp
  thus ?thesis using sv KV fV finite_vertex_of_simpl_complex [OF fV KV]
    by (meson card_mono order_trans)
qed

corollary pure_d_n_at_least_two_vertexes:
  assumes p: "pure_d n K" and cs: "closed_subset K" and Kne: "K \<noteq> {}" 
  and fV: "finite V" and KV: "K \<subseteq> powerset V" and n: "0 < n"
  shows "2 \<le> card V"
    using card_vertex_of_simpl_complex [OF fV KV]
    using pure_d_n_two_vertexes [OF p cs Kne fV KV n] by simp

lemma pure_d_0_collection_vertexes:
  assumes p: "pure_d 0 K" and cs: "closed_subset K" and Kne: "K \<noteq> {}"
  and fV: "finite V" and KV: "K \<subseteq> powerset V"
shows "K = {k.\<exists>v. k = {v} \<and> v \<in> vertex_of_simpl_complex K} \<union> {{}}"
proof
  have fK : "finite K" using fV KV by (simp add: finite_subset)
  show "K \<subseteq> {k.\<exists>v. k = {v} \<and> v \<in> vertex_of_simpl_complex K} \<union> {{}}"
  proof
    fix x assume x: "x \<in> K"
    consider (c0) "card x = 0" | (c1) "card x = 1" using pure_d_card [OF p fK] x by fastforce
    then show "x \<in> {k.\<exists>v. k = {v} \<and> v \<in> vertex_of_simpl_complex K} \<union> {{}}"
    proof (cases)
      case c0 hence "x = {}" using x KV cs fV unfolding closed_subset_def
        by (meson PowD card_0_eq infinite_super subset_eq)
      then show ?thesis by simp
    next
      case c1 then obtain v where xv: "x = {v}" and vV: "v \<in> V" using x KV
        by (metis PowD card_1_singletonE in_mono singletonI)
      then show ?thesis using x KV unfolding vertex_of_simpl_complex_def by simp
    qed
  qed
next
  show "{{v} |v. v \<in> vertex_of_simpl_complex K} \<union> {{}} \<subseteq> K"
    using Kne cs unfolding closed_subset_def vertex_of_simpl_complex_def by auto
qed

lemma pure_d_0_link_ext_evasive: assumes K: "K = {k.\<exists>v. k = {v} \<and> v \<in> vertex_of_simpl_complex K} \<union> {{}}"
 and c: "2 \<le> card (vertex_of_simpl_complex K)"
shows "\<forall>x\<in>(vertex_of_simpl_complex K). link_ext x V K = {{}}"
proof
  fix x
  assume x: "x \<in> vertex_of_simpl_complex K"
  show "link_ext x V K = {{}}"
  proof
    show "link_ext x V K \<subseteq> {{}}"
      apply (subst K) unfolding vertex_of_simpl_complex_def link_ext_def by auto
    show "{{}} \<subseteq> link_ext x V K"
      apply (subst K) unfolding vertex_of_simpl_complex_def link_ext_def
      using vertex_of_simpl_complex_def x by force
  qed
qed

lemma pure_d_0_singleton:
  assumes K: "K \<subseteq> powerset V" and cs: "closed_subset K" and f: "finite V" and Kne: "K \<noteq> {}"
    and p: "pure_d 0 K" and ne: "non_evasive (vertex_of_simpl_complex K) K"
  shows "card (vertex_of_simpl_complex K) = 1"
proof (rule ccontr)
  assume c: "card (vertex_of_simpl_complex K) \<noteq> 1"
  show False
  proof (cases "card (vertex_of_simpl_complex K) = 0")
    case True
    thus ?thesis using pure_d_0_one_vertex [OF p cs Kne f K] by simp
  next
    case False
    have "\<not> (non_evasive (vertex_of_simpl_complex K) K)"
    proof -
      have c2: "2 \<le> card (vertex_of_simpl_complex K)"
        using pure_d_0_one_vertex [OF p cs Kne f K] using False c by simp
      have le: "\<forall>x\<in>(vertex_of_simpl_complex K). link_ext x (vertex_of_simpl_complex K) K = {{}}"
        by (rule pure_d_0_link_ext_evasive [OF _ c2], rule pure_d_0_collection_vertexes [OF p cs Kne f K])
      have "\<forall>x\<in>(vertex_of_simpl_complex K). \<not> (non_evasive ((vertex_of_simpl_complex K) - {x}) K)"
        using non_evasive.simps (5) [OF c2, of K] le evasive_empty_set
        by (metis ne non_evasive.simps(1,6))
      thus ?thesis by (metis c2 evasive_empty_set le non_evasive.simps(1,5,6))
    qed
    hence False using ne by (rule notE)
    thus ?thesis by (rule ccontr)
  qed
qed

corollary pure_d_0_singleton2:
  assumes K: "K \<subseteq> powerset V" and cs: "closed_subset K" and f: "finite V" and Kne: "K \<noteq> {}"
    and p: "pure_d 0 K" and ne: "non_evasive (vertex_of_simpl_complex K) K"
  obtains v where "K = {{}, {v}}"
  using pure_d_0_singleton [OF K cs f Kne p ne]
  using pure_d_0_collection_vertexes [OF p cs Kne f K]
  using card_1_singletonE by force

lemma non_evasive_dim_1_two_free_faces: assumes n: "non_evasive (vertex_of_simpl_complex K) K" 
  and p: "pure_d 1 K" and f: "finite V" and K: "K \<subseteq> powerset V" and Kne: "K \<noteq> {}" and cs: "closed_subset K"
  shows "2 \<le> card {f. free_face f K}"
using n p f K Kne cs proof (induct "card {v\<in>K. card v = 2}" arbitrary: K rule: nat_induct_2)
  case (0 K)
  have fK: "finite K" using "0.prems" (3,4) by (simp add: finite_subset)
  obtain f where ff: "f \<in> facets K" and cf: "card f = 2" 
    using pure_d_facet [OF "0.prems" (5) fK "0.prems" (2)] by (metis nat_1_add_1)
  with "0.hyps" (1) and fK have False unfolding facets_def facet_def by simp
  thus ?case by (rule ccontr)
next
  case 1
  have fK: "finite K" using "1.prems" (3,4) by (simp add: finite_subset)
  obtain f where ff: "f \<in> facets K" and cf: "card f = 2" 
    using pure_d_facet [OF "1.prems" (5) fK "1.prems" (2)] by (metis nat_1_add_1)
  then obtain v1 v2 where fv1v2: "f = {v1,v2}" and neq: "v1 \<noteq> v2" by (meson card_2_iff)
  have v1K: "{v1} \<in> K" and v2K: "{v2} \<in> K" 
    using ff fv1v2 unfolding facets_def facet_def 
    using "1.prems" (6) unfolding closed_subset_def by fastforce+
  have "{v1} \<in> {f. free_face f K}"
  proof (rule, unfold free_face_def, rule ex1I [of _ f], rule conjI)
    show finK: "f \<in> K" using ff by (simp add: facet_in_K facets_def)
    show "face {v1} f" unfolding face_def using fv1v2 neq by auto
    show "\<And>b. b \<in> K \<and> face {v1} b \<Longrightarrow> b = f"
    proof -
      fix b
      assume "b \<in> K \<and> face {v1} b"
      hence bK: "b \<in> K" and fv1b: "face {v1} b" by simp_all
      have "card {v1} = 1" by simp
      then have "1 < card b"
        using fv1b "1.prems" (3,4) bK unfolding face_def
        by (metis Pow_iff finite_subset psubset_card_mono subset_iff)
      then have "card b = 2"
        using pure_d_card [OF "1.prems" (2) fK] fv1b bK unfolding face_def by auto
      with 1 bK cf finK show "b = f"
        by (smt (verit) card_1_singletonE mem_Collect_eq singletonD)
    qed
  qed
  moreover have "{v2} \<in> {f. free_face f K}"
  proof (rule, unfold free_face_def, rule ex1I [of _ f], rule conjI)
    show finK: "f \<in> K" using ff by (simp add: facet_in_K facets_def)
    show "face {v2} f" unfolding face_def using fv1v2 neq by auto
    show "\<And>b. b \<in> K \<and> face {v2} b \<Longrightarrow> b = f"
    proof -
      fix b
      assume "b \<in> K \<and> face {v2} b"
      hence bK: "b \<in> K" and fv2b: "face {v2} b" by simp_all
      have "card {v2} = 1" by simp
      then have "1 < card b" using fv2b "1.prems" (3,4) unfolding face_def
        by (metis K Pow_iff bK f finite_subset psubset_card_mono subset_iff)
      then have "card b = 2"
        using pure_d_card [OF "1.prems" (2) fK] fv2b bK unfolding face_def by auto
      with 1 bK cf finK show "b = f"
        by (smt (verit) card_1_singletonE mem_Collect_eq singletonD)
    qed
  qed
  moreover have "finite {f. free_face f K}" using finite_free_faces [OF fK "1.prems" (6)] .
  moreover have "{v1} \<noteq> {v2}" using neq by simp
  ultimately show ?case
    by (metis (no_types, lifting) One_nat_def card_0_eq card_1_singletonE empty_iff less_2_cases linorder_not_le singletonD)
next
  case (Suc n K)
  have cardvK: "2 \<le> card (vertex_of_simpl_complex K)" 
    using p pure_d_n_two_vertexes [OF "Suc.prems" (2,6,5,3,4)] by simp
  obtain r where "r \<in> K" and "card r = 2" using Suc.hyps(3) unfolding pure_d_def facets_def facet_def
    by (metis (mono_tags, lifting) Collect_empty_eq Zero_not_Suc card.empty)
  obtain v where v: "v \<in> vertex_of_simpl_complex K"
        and nl: "non_evasive (vertex_of_simpl_complex K - {v}) (link_ext v (vertex_of_simpl_complex K) K)"
        and nc: "non_evasive (vertex_of_simpl_complex K - {v}) (cost v (vertex_of_simpl_complex K) K)"
    using Suc.prems (1) unfolding non_evasive.simps (5) [OF cardvK, of K] by auto
  have pwv: "K \<subseteq> powerset (vertex_of_simpl_complex K)"
    by (rule powerset_vertex_of_simpl_complex [OF Suc.prems (4,6)])
  have "pure_d 0 (link_ext v (vertex_of_simpl_complex K) K)"
    using pure_d_minus_one_link_ext [OF pwv Suc.prems (6) _ Suc.prems (2), of v]
    using v unfolding vertex_of_simpl_complex_def by simp
  have "card (vertex_of_simpl_complex (link_ext v (vertex_of_simpl_complex K) K)) = 1"
    unfolding link_ext_vertex_of_simpl_complex [OF Suc.prems (4) Suc.prems (6), symmetric]
  proof (rule pure_d_0_singleton [of _ "vertex_of_simpl_complex K - {v}"])
    show lepw: "link_ext v V K \<subseteq> powerset (vertex_of_simpl_complex K - {v})"
      using link_ext_closed pwv
      using link_ext_vertex_of_simpl_complex [OF Suc.prems (4) Suc.prems (6)]
      by presburger
    show csle: "closed_subset (link_ext v V K)"
      using Suc.prems(6) link_ext_closed_subset by auto
    show "finite (vertex_of_simpl_complex K - {v})"
      using Suc.prems(1) non_evasive.simps(6) by blast
    show "link_ext v V K \<noteq> {}"
      using singleton_in_link_ext v vertex_of_simpl_complex_def by fastforce
    show "pure_d 0 (link_ext v V K)"
      using \<open>\<And>v. link_ext v (vertex_of_simpl_complex K) K = link_ext v V K\<close> \<open>pure_d 0 (link_ext v (vertex_of_simpl_complex K) K)\<close>
      by presburger
    show "non_evasive (vertex_of_simpl_complex (link_ext v V K)) (link_ext v V K)"
      using nl
      unfolding link_ext_vertex_of_simpl_complex [OF Suc.prems (4) Suc.prems (6), symmetric]
      using nl unfolding vertex_of_simpl_complex_def unfolding link_ext_def

      have "link_ext v (vertex_of_simpl_complex K) K \<subseteq> powerset (vertex_of_simpl_complex (link_ext v (vertex_of_simpl_complex K) K))"
      by (rule powerset_vertex_of_simpl_complex [of _ "vertex_of_simpl_complex K - {v}"], rule lepw, rule csle)


    qed
    then obtain w where "link_ext v (vertex_of_simpl_complex K) K = {{},{w}}"
    apply (rule pure_d_0_singleton2 [of "link_ext v (vertex_of_simpl_complex K) K" "V - {v}"])
    using pure_d_0_singleton2 [OF Suc.prems (4,6) f Suc.prems (5)]
    have "free_face {v} K"
  proof (unfold free_face_def, rule ex1I)
  from Suc.hyps






lemma pure_d_1_free_faces:
  assumes K: "K \<subseteq> powerset V" and cs: "closed_subset K" and f: "finite V" and Kne: "K \<noteq> {}"
    and p: "pure_d 1 K" and ne: "non_evasive (vertex_of_simpl_complex K) K"
  shows " "

lemma assumes K: "K \<subseteq> powerset V" and c: "closed_subset K" and d: "0 < d" and f: "finite K"
  and p: "pure_d d K" and v: "{v} \<in> K" and nc: "\<not> (cone_peak V K v)" shows "pure_d d (cost v V K)"
proof (unfold pure_d_def, rule)

  from v have Kne: "K \<noteq> {}" by auto
  from p obtain f where "f \<in> facets K" and "card f = d + 1" using pure_d_facet [OF Kne f p] by auto
  
  (*obtain f where "f \<in> cost v V K" and "f \<notin> link_ext v V K"
    using nc K c v proposition_1 [OF _ K, of v]
    by (metis Pow_iff closed_subset_link_eq_link_ext insert_not_empty insert_subset link_subset_cost subsetI subset_antisym)*)
  fix f
  assume f: "f \<in> facets (cost v V K)"
  hence fc: "f \<in> cost v V K"
    unfolding facets_def
    using facet_in_K by auto
  hence vnf: "v \<notin> f" unfolding cost_def by auto
  have insf: "f \<in> facets K" 
  proof (cases "f \<in> facets (link_ext v V K)")
    case True
    hence "f \<in> link_ext v V K" unfolding facets_def using facet_in_K by auto
    hence "insert v f \<in> K" unfolding link_ext_def by simp
    hence False using f vnf unfolding facets_def facet_def cost_def try
    then show ?thesis sorry
  next
    case Farop
lse
    then show ?thesis sorry
  qed
  

  proof (unfold facets_def, rule, unfold facet_def, rule)
    show "f \<in> K" using fc by (metis K Un_iff cost_union_closed_star)
    show "\<forall>b\<in>K. f \<subseteq> b \<longrightarrow> f = b"
    proof (rule, rule)
      fix b assume b: "b \<in> K" and i: "insert v f \<subseteq> b"
      show "insert v f = b"
      proof (rule ccontr)
        assume "insert v f \<noteq> b" hence ins: "insert v f \<subset> b" using i by auto
        have "b - {v} \<in> link_ext v V K" using b K i unfolding link_ext_def 
          by auto (simp add: insert_absorb)
        moreover have "f \<subset> b - {v}" using ins vnf by auto
        ultimately show False using f unfolding facets_def facet_def by auto
      qed
    qed
  qed
  show "card f = d - 1 + 1" using insf p vnf d unfolding pure_d_def
    by (metis Suc_diff_1 Suc_eq_plus1 card_Diff_singleton_if diff_Suc_1 insertI1 insert_Diff1)
qed


lemma assumes K: "K \<subseteq> powerset V" and cs: "closed_subset K"
  shows "facets K = facets (cost v V K) \<union> join_vertex v (facets (link_ext v V K))"
proof
  show "facets K \<subseteq> facets (cost v V K) \<union> join_vertex v (facets (link_ext v V K))"
  proof
    fix x
    assume xf: "x \<in> facets K"
    show "x \<in> facets (cost v V K) \<union> join_vertex v (facets (link_ext v V K))"
    proof (cases "v \<in> x")
      case True
      have "x - {v} \<in> (facets (link_ext v V K))"
        unfolding facets_def facet_def link_ext_def 
      proof (rule,rule,rule,intro conjI)
        show "x - {v} \<in> powerset V" 
          using xf K cs unfolding facets_def facet_def closed_subset_def by auto
        show "v \<notin> x - {v}" by simp
        show "insert v (x - {v}) \<in> K" 
          using xf True insert_Diff unfolding facets_def facet_def by fastforce
        show "\<forall>b\<in>{s \<in> powerset V. v \<notin> s \<and> insert v s \<in> K}. x - {v} \<subseteq> b \<longrightarrow> x - {v} = b"
        proof
          fix b
          assume b: "b \<in> {s \<in> powerset V. v \<notin> s \<and> insert v s \<in> K}"
          show "x - {v} \<subseteq> b \<longrightarrow> x - {v} = b" using xf b unfolding facets_def facet_def by auto
        qed
      qed
      hence "{v} \<union> (x - {v}) \<in> join_vertex v (facets (link_ext v V K))" by (rule union_in_join_vertex)
      thus ?thesis using True insert_Diff unfolding join_vertex_def join_def by force
    next
      case False
      have "x \<in> facets (cost v V K)" 
        unfolding facets_def facet_def cost_def
      proof (rule, rule, rule, intro conjI)
        show "x \<in> powerset (V - {v})" using xf False K unfolding facets_def facet_def by auto
        show "x \<in> K" using xf unfolding facets_def facet_def by simp 
        show "\<forall>b\<in>{s \<in> powerset (V - {v}). s \<in> K}. x \<subseteq> b \<longrightarrow> x = b"
        proof (rule)
          fix b
          assume b: "b \<in> {s \<in> powerset (V - {v}). s \<in> K}" 
          show "x \<subseteq> b \<longrightarrow> x = b" using xf b unfolding facets_def facet_def by auto
        qed
      qed
      thus ?thesis by simp
    qed
  qed
  show "facets (cost v V K) \<union> join_vertex v (facets (link_ext v V K)) \<subseteq> facets K"
  proof
    fix x
    assume x: "x \<in> facets (cost v V K) \<union> join_vertex v (facets (link_ext v V K))"
    consider (xint) "x \<in> facets (cost v V K) \<inter> join_vertex v (facets (link_ext v V K))" | 
                (xcost) "x \<in> facets (cost v V K) - (join_vertex v (facets (link_ext v V K)))" | 
                    (xlink) "x \<in> (join_vertex v (facets (link_ext v V K))) - (facets (cost v V K))" using x by auto
  then 
    show "x \<in> facets K"
    proof (cases)
      case xcost
      show ?thesis
        unfolding facets_def facet_def
      proof (rule, intro conjI)
        show "x \<in> K" using xcost unfolding facets_def facet_def cost_def by simp
        show "\<forall>b\<in>K. x \<subseteq> b \<longrightarrow> x = b" 
        proof (rule)
          fix b
          assume b: "b \<in> K"
          show "x \<subseteq> b \<longrightarrow> x = b"
          proof (cases "v \<in> b")
            case False
            hence "b \<in> powerset (V - {v})" using K xcost b by blast
            thus ?thesis using xcost b unfolding facets_def facet_def cost_def by simp
          next
            case True
            show ?thesis
            proof
              assume xb: "x \<subseteq> b"
              have vnx: "v \<notin> x" using xcost unfolding cost_def facets_def facet_def  by auto
              hence "x \<in> link_ext v V K"
                using xb b True cs xcost
                unfolding link_ext_def cost_def facets_def facet_def closed_subset_def by auto
              with True have "insert v x \<in> join_vertex v (link_ext v V K)" by simp
              thus "x = b" 
                using vnx b xcost True cs
                unfolding link_ext_def cost_def facets_def facet_def closed_subset_def
                try



        unfolding facets_def facet_def cost_def
    next
      case False
      then show ?thesis sorry
    qed

  show ?case
qed

lemma assumes n: "non_evasive (vertex_of_simpl_complex K) K" and p: "pure_d (dim K) K" and d: "0 < (dim K)"
      and f: "finite (vertex_of_simpl_complex K)" and cs: "closed_subset K" and K: "K \<subseteq> powerset (vertex_of_simpl_complex K)" 
    shows "2 \<le> card {f. free_face f K}"
  using n p d f cs K proof (induct "dim K" rule: nat_induct)
  case 0 from "0.prems" (3) and "0.hyps" have False by linarith
  thus ?thesis by (rule ccontr)
next
  case (Suc n)
  show ?thesis
  proof (cases "dim K = 1")
    case True hence p: "pure_d 1 K" using "Suc.prems" (2) by simp
    show ?thesis
      using non_evasive_dim_1_two_free_faces [OF "Suc.prems" (1) p Suc.prems (4,6)] 
      using free_face_def face_def by simp
  next
    case False
    have "2 \<le> card (vertex_of_simpl_complex K)" 
      using Suc.prems (2,3,5) 
      unfolding pure_d_def closed_subset_def vertex_of_simpl_complex_def facets_def facet_def 
      try
    from "Suc.prems" (1) have False using non_evasive.simps
    then show ?thesis sorry
  qed


proof (cases "K = {}")
  case True
  from n
  have False unfolding True vertex_of_simpl_complex_def by simp thus ?thesis by (rule ccontr)
next
  case False note Kne = False
  show ?thesis
  proof (cases "K = {{}}")
    case True
    have False using n unfolding True vertex_of_simpl_complex_def by simp
    thus ?thesis by (rule ccontr)
  next
    case False
    have "finite K" using f K unfolding vertex_of_simpl_complex_def
      by (simp add: finite_subset)
    show ?thesis
      using Kne False n p d proof (induct "dim K" rule: nat_induct)
      case 0 from "0.prems" (5) and "0.hyps" have False by linarith
      thus ?thesis by (rule ccontr)
    next
      show ?case
      proof (induct "card (facets K)" rule: nat_induct)
        case 0 with prems (4,5) and `finite K` have False unfolding pure_d_def
        show ?case sorry
      next
        case (Suc x)
        then show ?case sorry
      qed
    qed
  qed
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