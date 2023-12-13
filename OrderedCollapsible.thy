
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
  using cone_peak_cost_eq_link_ext [OF v] 
  using cost_eq_link_ext_cone_peak [OF v K] by (smt (verit))

text\<open>Proposition 2 in our paper.\<close>

lemma assumes K: "K \<subseteq> powerset V" and c: "closed_subset K"
  shows "K = cost v V K \<union> join_vertex v (link_ext v V K)"
  using complex_decomposition [OF K c] 
  using cc_s_link_eq_link_ext [of V K v] using K c using cc_s.intros
  by (smt (verit, best) CollectD Diff_empty Diff_insert0 Diff_insert_absorb bot.extremum_uniqueI insert_Diff_single link_ext_def link_ext_empty_vertex link_intro link_subset_link_ext singletonI subsetD)

section\<open>Definition of \emph{ordered-no-evasive}\<close>

function ordered_non_evasive :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_non_evasive l K = False"
  | "0 < length l \<Longrightarrow> ordered_non_evasive l K = ((cone_peak (set l) K (hd l))
      | (ordered_non_evasive (tl l) (cost (hd l) (set l) K) \<and>
          ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

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
  | "0 < length l \<Longrightarrow> ordered_zero_collapsible l K = ((cone_peak (set l) K (hd l))
      | (ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
          cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(l,K). length l)", auto)

function ordered_m_collapsible :: "nat \<Rightarrow> nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_m_collapsible m l K = False"
  | "0 < length l \<Longrightarrow> 0 = m \<Longrightarrow> ordered_m_collapsible m l K = ordered_zero_collapsible l K"
  | "0 < length l \<Longrightarrow> 0 < m \<Longrightarrow> ordered_m_collapsible m l K = ((cone_peak (set l) K (hd l))
      | (ordered_m_collapsible m (tl l) (cost (hd l) (set l) K) \<and>
         ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)))"
  by (auto+)
termination by (relation "Wellfounded.measure (\<lambda>(m,l,K). length l)", auto)

(*function ordered_m_collapsible :: "nat \<Rightarrow> nat list \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "l = [] \<Longrightarrow> ordered_m_collapsible m l K = False"
  | "0 < length l \<Longrightarrow> ordered_m_collapsible m l K = ((cone_peak (set l) K (hd l))
      | (ordered_m_collapsible m (tl l) (cost (hd l) (set l) K) \<and>
         ordered_m_collapsible (m - 1) (tl l) (link_ext (hd l) (set l) K)))"
  by (auto+)
termination by (relation "Wellfounded.measure (\<lambda>(m,l,K). length l)", auto)*)

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


(*lemma cone_is_one:
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
*)

lemma ordered_zero_collapsible_ordered_one_collapsible:
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
  proof (cases "length l \<le> 2")
    case False note l2 = False
    show ?thesis
    proof (cases "cone_peak (set l) K (hd l)")
      case True
      show ?thesis using ordered_m_collapsible.simps (3) [OF l0, of "1"] using True by simp
      next
      case False
      hence cost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" 
        and link: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)" 
        using ei False by simp_all
      have "ordered_m_collapsible 1 (tl l) (cost (hd l) (set l) K)"
      proof (rule less.hyps)
        show "length (tl l) < length l" using l0 by simp
        show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
          using less.prems (1) l0 unfolding powerset_def cost_def
          by (smt (verit, del_insts) Diff_insert_absorb insert_absorb length_greater_0_conv list.exhaust_sel list.simps(15) mem_Collect_eq subset_iff)
        show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using cost by simp
        show "distinct (tl l)" by (simp add: distinct_tl less.prems(3))
      qed
      moreover have "ordered_m_collapsible 0 (tl l) (link_ext (hd l) (set l) K)"
      proof (rule cone_is_ordered_m_collapsible [of _ _ "hd (tl l)" "tl (tl l)"])
        show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
          using less.prems(2) less.prems(3) link
          unfolding link_ext_def powerset_def cone_peak_def by auto
        show "tl l = hd (tl l) # tl (tl l)" using l2
          by (metis False ei list.exhaust_sel ordered_zero_collapsible.simps(1))
        show "distinct (tl l)" using less.prems (3) by (rule distinct_tl)
        show "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
          using link less.prems (3)
          by (metis Nil_tl cone_peak_def distinct.simps(2) list.exhaust_sel)
      qed
      ultimately show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0] using l0 by fastforce
    qed
  next
    case True note le2 = True
    show ?thesis
    proof (cases "length l = 1")
      case True
      show ?thesis
        using ei True
        unfolding cone_peak_def using l0 ei
        by (metis diff_is_0_eq' le_numeral_extra(4) length_tl less_numeral_extra(3) ordered_m_collapsible.simps(3) ordered_non_evasive.elims(1) ordered_zero_collapsible.simps(1))
    next
      case False hence l2: "length l = 2" using le2 l0 by linarith
      show ?thesis using l2 ei
        by (metis cone_peak_def distinct.simps(2) l0 less.prems(2) less.prems(3) less_numeral_extra(1) list.exhaust_sel ordered_m_collapsible.simps(3) ordered_zero_collapsible.simps(1))
    qed
  qed
qed

lemma ordered_m_collapsible_0_ordered_m_collapsible_one:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_m_collapsible 0 l K"
  shows "ordered_m_collapsible 1 l K"
proof (cases "l = []")
  case True with c have False by simp
  thus ?thesis by (rule ccontr)
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
    from less.prems (3) have l0: "0 < length l" by auto
    show ?case
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
          show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
            using less.prems (1) l0 unfolding cost_def powerset_def
            by (smt (verit, del_insts) Diff_insert_absorb insert_absorb length_greater_0_conv list.exhaust_sel list.simps(15) mem_Collect_eq subset_iff)
          show "distinct (tl l)" using distinct_tl [OF less.prems (2)] .
          show "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" using cost .
        qed
        moreover have "ordered_m_collapsible (m - 1 + 1) (tl l) (link_ext (hd l) (set l) K)"
        proof (rule less.hyps)
          show "length (tl l) < length l" using l0 by simp
          show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
            using l0 less.prems unfolding link_ext_def powerset_def cone_peak_def
            apply auto using notcone
            by (metis in_mono list.exhaust_sel set_ConsD)
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

lemma ordered_zero_collapsible_ordered_non_evasive:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_zero_collapsible l K"
  shows "ordered_non_evasive l K"
using K c d proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  from less.prems (2) have l0: "0 < length l" by auto
  from less.prems (2) and ordered_zero_collapsible.simps (2) [OF l0, of K]
  have ei: "(cone_peak (set l) K (hd l) \<or>
     ordered_zero_collapsible (tl l) (cost (hd l) (set l) K) \<and>
    cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l))" by simp
  show ?case
  proof (cases "length l \<le> 2")
    case False note l2 = False
    show ?thesis
    proof (cases "cone_peak (set l) K (hd l)")
      case True
      show ?thesis using ordered_non_evasive.simps (2) [OF l0] using True by simp
      next
      case False
      hence cost: "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" 
        and link: "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd l)" 
        using ei False by simp_all
      have "ordered_non_evasive (tl l) (cost (hd l) (set l) K)"
      proof (rule less.hyps)
        show "length (tl l) < length l" using l0 by simp
        show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
          using less.prems (1) l0 unfolding powerset_def cost_def
          by (smt (verit, del_insts) Diff_insert_absorb insert_absorb length_greater_0_conv list.exhaust_sel list.simps(15) mem_Collect_eq subset_iff)
        show "ordered_zero_collapsible (tl l) (cost (hd l) (set l) K)" using cost by simp
        show "distinct (tl l)" by (simp add: distinct_tl less.prems(3))
      qed
      moreover have "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)"
      proof (rule cone_is_one [of _ _ "hd (tl l)"])
        show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
          using less.prems(2) less.prems(3) link
          unfolding link_ext_def powerset_def cone_peak_def by auto
        show "hd (tl l) \<in> set (tl l)" using l2
          using cost list.set_sel(1) ordered_zero_collapsible.simps(1) by blast
        show "distinct (tl l)" using less.prems (3) by (rule distinct_tl)
        show "cone_peak (set (tl l)) (link_ext (hd l) (set l) K) (hd (tl l))"
          using link less.prems (3)
          by (metis Nil_tl cone_peak_def distinct.simps(2) list.exhaust_sel)
      qed
      ultimately show ?thesis unfolding ordered_m_collapsible.simps (2) [OF l0] using l0 by fastforce
    qed
  next
    case True note le2 = True
    show ?thesis
    proof (cases "length l = 1")
      case True
      show ?thesis
        using ei True
        unfolding cone_peak_def using l0 ei
        by (metis diff_is_0_eq' le_numeral_extra(4) length_tl less_numeral_extra(3) ordered_non_evasive.elims(1) ordered_zero_collapsible.simps(1))
    next
      case False hence l2: "length l = 2" using le2 l0 by linarith
      show ?thesis using l2 ei
        by (metis cone_peak_def distinct.simps(2) l0 less.prems(2) less.prems(3) list.exhaust_sel ordered_non_evasive.simps(2) ordered_zero_collapsible.simps(1))
    qed
  qed
qed

lemma ordered_m_collapsible_ordered_non_evasive:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_m_collapsible m l K" 
  shows "ordered_non_evasive l K"
  using c proof (induct m rule: less_induct)
  case (less m)
  note f = less.prems (1)
  show ?case using K d f proof (induct "length l" arbitrary: l K m rule: less_induct)
    case less
    from less.prems (3) have l0: "0 < length l" by auto
    show ?case
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
          show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
            using less.prems (1) l0 unfolding cost_def powerset_def
            by (smt (verit, del_insts) Diff_insert_absorb insert_absorb length_greater_0_conv list.exhaust_sel list.simps(15) mem_Collect_eq subset_iff)
          show "distinct (tl l)" using distinct_tl [OF less.prems (2)] .
          show "ordered_m_collapsible m (tl l) (cost (hd l) (set l) K)" using cost .
        qed
        moreover have "ordered_non_evasive (tl l) (link_ext (hd l) (set l) K)"
        proof (rule less.hyps)
          show "length (tl l) < length l" using l0 by simp
          show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
            using l0 less.prems unfolding link_ext_def powerset_def cone_peak_def
            apply auto using notcone
            by (metis in_mono list.exhaust_sel set_ConsD)
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

lemma ordered_non_evasive_ordered_m_collapsible:
  assumes K: "K \<subseteq> powerset (set l)" and d: "distinct l"
    and c: "ordered_non_evasive l K"
  shows "\<exists>m. ordered_m_collapsible m l K"
proof (rule exI [of _ "length l"])
  show "ordered_m_collapsible (length l) l K"
  using K d c proof (induct "length l" arbitrary: l K rule: less_induct)
  case less
  have l0: "0 < length l" using less.prems(3) by auto
  show ?case
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
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using less.prems (1) l0 unfolding cost_def powerset_def
        by (metis (full_types) Collect_subset Diff_cancel Diff_eq_empty_iff Diff_insert2 Pow_mono hd_Cons_tl link list.sel(2) list.simps(15) ordered_non_evasive.simps(1) subset_trans)
      show "distinct (tl l)"
        using distinct_tl less.prems(2) by auto
      show "ordered_non_evasive (tl l) (cost (hd l) (set l) K)"
        using less.prems (3) ordered_non_evasive.simps (2) [OF l0, of K] False by simp
    qed
    have cost: "ordered_m_collapsible (length (tl l) + 1) (tl l) (cost (hd l) (set l) K)"
    proof (rule ordered_m_collapsible_suc)
      show "cost (hd l) (set l) K \<subseteq> powerset (set (tl l))" 
        using less.prems (1,2,3)
        by (metis Diff_insert_absorb cost_closed distinct.simps(2) list.exhaust_sel list.simps(15) ordered_non_evasive.simps(1))
      show "distinct (tl l)"
        using distinct_tl less.prems(2) by auto
      show "ordered_m_collapsible (length (tl l)) (tl l) (cost (hd l) (set l) K)"
        using cost_minus_one .
    qed
    moreover have link: "ordered_m_collapsible (length (tl l)) (tl l) (link_ext (hd l) (set l) K)"
    proof (rule less.hyps)
      show "length (tl l) < length l" using l0 by simp
      show "link_ext (hd l) (set l) K \<subseteq> powerset (set (tl l))"
        using less.prems (1,2,3) l0 unfolding link_def powerset_def
        by (metis Diff_insert_absorb distinct.simps(2) link_ext_closed list.exhaust_sel list.simps(15) ordered_non_evasive.simps(1) powerset_def)
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

section\<open>Main Theorem.\<close>

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
term facet

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