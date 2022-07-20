
theory BDT
  imports
    "HOL-Library.Tree"
    Simplicial_complex
begin

section\<open>BDT\<close>

inductive_set bdt :: "(nat set \<times> nat tree) set"
  where "({}, Leaf) \<in> bdt"
  | "({x}, (Node Leaf x Leaf)) \<in> bdt"
  | "(A, L) \<in> bdt \<and> (A, R) \<in> bdt \<Longrightarrow> (insert x A, (Node L x R)) \<in> bdt"

lemma "({}, Leaf) \<in> bdt" using bdt.intros (1) .

inductive_set bdt_s :: "(nat set \<times> nat tree) set"
  where "({}, Leaf) \<in> bdt_s"
  | "(A, L) \<in> bdt \<and> (A, R) \<in> bdt \<Longrightarrow> (insert x A, (Node L x R)) \<in> bdt_s"

lemma "bdt \<subseteq> bdt_s"
proof (auto simp add:  bdt.intros)
  fix a b
  assume bdt: "(a, b) \<in> bdt"
  then show "(a, b) \<in> bdt_s" 
  proof (cases "a = {}")
    case True
    then show ?thesis
      using bdt bdt.cases bdt_s.simps by auto
  next
    case False
    then show ?thesis
      by (smt (verit, best) bdt bdt.cases bdt.intros(1) bdt_s.intros(2))
  qed
qed

lemma "bdt_s \<subseteq> bdt"
proof (auto simp add:  bdt.intros)
  fix a b
  assume bdt: "(a, b) \<in> bdt_s"
  then show "(a, b) \<in> bdt" 
  proof (cases "a = {}")
    case True
    then show ?thesis
      by (metis bdt bdt.simps bdt_s.simps)
  next
    case False
    then show ?thesis
      by (smt (verit, ccfv_threshold) bdt bdt.simps bdt_s.cases)
  qed
qed

inductive_set obdt :: "(nat set \<times> nat tree) set"
  where "({}, Leaf) \<in> obdt"
  | "(A, L) \<in> obdt \<Longrightarrow> (insert x A, (Node L x L)) \<in> obdt"

inductive_set obdt_list :: "(nat set \<times> nat list) set"
  where "({}, []) \<in> obdt_list"
  | "(A, l) \<in> obdt_list \<Longrightarrow> x \<notin> A \<Longrightarrow> (insert x A, Cons x l) \<in> obdt_list"

lemma "({1}, [1]) \<in> obdt_list"
  by (simp add: obdt_list.intros(1) obdt_list.intros(2))

lemma "({1}, [1,1]) \<notin> obdt_list"
  by (metis (no_types, lifting) insert_absorb insert_eq_iff insert_not_empty not_Cons_self2 obdt_list.cases)

lemma "({1,2,3},[3,2,1]) \<in> obdt_list"
  using obdt_list.intros (1)
  using obdt_list.intros (2) [of "{}" "[]" "1"]
  using obdt_list.intros (2) [of "{1}" "[1]" "2"]
  using obdt_list.intros (2) [of "{1,2}" "[2,1]" "3"]
  by (simp add: insert_commute obdt_list.intros(2))

inductive_set obdt_set :: "(nat set) set"
  where "{} \<in> obdt_set"
  | "A \<in> obdt_set \<Longrightarrow> x \<notin> A \<Longrightarrow> (insert x A) \<in> obdt_set"

lemma "{1} \<in> obdt_set"
  by (simp add: obdt_set.intros(1) obdt_set.intros(2))

lemma "{1,2,3,4,5,6} \<in> obdt_set"
  by (simp add: obdt_set.intros(1) obdt_set.intros(2))

definition powerset :: "nat set \<Rightarrow> nat set set"
  where "powerset A = Pow A"

lemma "powerset {} = {{}}"
  by (simp add: powerset_def)

lemma "powerset {x} = {{},{x}}"
  by (simp add: Pow_singleton powerset_def)

inductive_set cc :: "(nat set \<times> nat set set) set"
  where "({}, {}) \<in> cc"
  | "({x}, {}) \<in> cc"
  | "({x}, {{}}) \<in> cc"
  | "({x}, {{},{x}}) \<in> cc"
  | "(A, {}) \<in> cc"
  | "A \<noteq> {} \<Longrightarrow> k \<subseteq> powerset A \<Longrightarrow> (A, k) \<in> cc"

lemma "({}, {}) \<in> cc"
  by (simp add: cc.intros(1) powerset_def)

lemma "({}, {{}}) \<notin> cc"
  by (simp add: cc.simps)

lemma "({0}, {}) \<in> cc"
  by (rule cc.intros(2))

lemma "({0,1,2}, {}) \<in> cc" 
  by (rule cc.intros(5))

lemma "({0,1,2}, {{1,2}}) \<in> cc" 
  by (simp add: cc.intros(6) powerset_def)

lemma "({0,1,2}, {{1},{2}}) \<in> cc"
  by (simp add: cc.intros(6) powerset_def)

definition pow_closed :: "'a set set \<Rightarrow> bool"
  where "pow_closed S \<equiv> (\<forall>s\<in>S. \<forall>s'\<subseteq>s. s'\<in> S)"

value "pow_closed {{True, False},{True},{False},{}}"

lemma
  assumes "pow_closed S" and "s \<in> S" and "s' \<subseteq> s"
  shows "s' \<in> S"
  using assms(1,2,3) pow_closed_def by blast
  

inductive_set cc_s :: "(nat set \<times> nat set set) set"
  where "({}, {}) \<in> cc_s"
  | "(A, {}) \<in> cc_s"
  | "A \<noteq> {} \<Longrightarrow> K \<subseteq> powerset A \<Longrightarrow> pow_closed K \<Longrightarrow> (A, K) \<in> cc_s"

lemma cc_s_simplices:
  assumes cc_s: "(V, K) \<in> cc_s" and x: "x \<in> K"
  shows "x \<in> powerset V"
proof (cases "V = {}")
  case True hence k: "K = {}" using cc_s
    by (simp add: cc_s.simps)
  show ?thesis unfolding True powerset_def using x k
    by simp
next
  case False note V = False
  show ?thesis
  proof (cases "K = {}")
    case True
    then show ?thesis using V x by simp
  next
    case False
    then show ?thesis 
      using V False  
      using cc_s.simps [of V K]
      unfolding powerset_def pow_closed_def
      using cc_s x by blast
  qed
qed

corollary cc_s_subset:
  assumes cc_s: "(V, K) \<in> cc_s"
  shows "K \<subseteq> powerset V" using cc_s_simplices [OF cc_s] by auto

corollary cc_s_finite_simplices:
  assumes cc_s: "(V, K) \<in> cc_s" 
    and x: "x \<in> K" and f: "finite V"
  shows "finite x"
  using cc_s_simplices [OF cc_s x] 
  unfolding powerset_def using f using finite_subset [of x V] by auto

lemma
  cc_s_closed:
  assumes "s \<subseteq> s'" and "(A, K) \<in> cc_s" and "s' \<in> K"
  shows "s \<in> K"
proof (cases "A = {}")
  case True show ?thesis
    using True assms(2) assms(3) cc_s.simps by force
next
  case False note A = False
  show ?thesis
  proof (cases "K = {}")
    case True
    then show ?thesis using assms by blast
  next
    case False
    from cc_s.simps [of A K]
    have "pow_closed K" using False A
      using assms(2) by presburger
    then show ?thesis using assms (1,3) unfolding pow_closed_def by auto
  qed
qed

lemma "({0}, {}) \<in> cc_s" 
  by (rule cc_s.intros(2))

lemma "({0,1,2}, {}) \<in> cc_s" 
  by (rule cc_s.intros(2))

lemma "({0,1,2}, {{1},{}}) \<in> cc_s" 
  by (rule cc_s.intros(3) [of "{0,1,2}" "{{1},{}}"], simp, unfold powerset_def, auto,
      unfold pow_closed_def, auto)

lemma "({0,1,2}, {{1},{2},{}}) \<in> cc_s"
  by (rule cc_s.intros(3) [of "{0,1,2}" "{{1},{2},{}}"], simp, unfold powerset_def, auto,
      unfold pow_closed_def, auto)

lemma "({0,1,2}, {{1,2},{1},{2},{}}) \<in> cc_s"
  by (rule cc_s.intros(3) [of "{0,1,2}" "{{1,2},{1},{2},{}}"], simp, unfold powerset_def, auto,
      unfold pow_closed_def, auto)

definition link_ext :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link_ext x V K = {s. s \<in> powerset V \<and> x \<notin> s \<and> insert x s \<in> K}"

(*definition link_ext :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link_ext x V K = {s. s \<in> powerset (V - {x}) \<and> s \<union> {x} \<in> K}"*)

lemma link_ext_empty [simp]: "link_ext x V {} = {}"
  by (simp add: link_ext_def)

lemma link_ext_mono:
  assumes "K \<subseteq> L"
  shows "link_ext x V K \<subseteq> link_ext x V L"
  using assms unfolding link_ext_def powerset_def by auto

lemma
  link_ext_cc:
  assumes v: "(V, K) \<in> cc_s"
  shows "(V, {s. insert x s \<in> K}) \<in> cc_s"
proof (cases "x \<in> V")
  case False
  have "{s. insert x s \<in> K} = {}" 
  proof (rule cc_s.cases [OF v])
    assume "V = {}" and "K = {}"
    thus "{s. insert x s \<in> K} = {}" by simp
  next
    fix A assume "V = A" and "K = {}"
    thus "{s. insert x s \<in> K} = {}" by simp
  next
    fix A L
    assume v: "V = A" and k: "K = L" and "A \<noteq> {}" and l: "L \<subseteq> powerset A"
      and "pow_closed L" 
    show "{s. insert x s \<in> K} = {}" 
      using False v k l unfolding powerset_def by auto
  qed
  thus ?thesis using cc_s.intros (1,2) by simp
next
  case True
  show ?thesis
  proof (rule cc_s.intros (3))
    show "V \<noteq> {}" using True by fast
    show "{s. insert x s \<in> K} \<subseteq> powerset V" 
      using v True cc_s.intros (3) [of V K]
      using cc_s_simplices powerset_def by auto
    show "pow_closed {s. insert x s \<in> K}"
    proof -  
      have "pow_closed K" 
        using v True cc_s.intros (3) [of V K]
        by (simp add: cc_s_closed pow_closed_def)
      thus ?thesis unfolding pow_closed_def
        by auto (meson insert_mono)
    qed
  qed
qed

corollary
  link_ext_cc_s:
  assumes v: "(V, K) \<in> cc_s"
  shows "(V, link_ext x V K) \<in> cc_s"
proof (cases "V = {}")
  case True
  show ?thesis using v unfolding True link_ext_def powerset_def
    by (simp add: cc_s.simps)
next
  case False note vne = False
  show ?thesis
  proof (cases "x \<in> V")
    case False
    show ?thesis 
      using False cc_s_subset [OF v] 
      unfolding link_ext_def powerset_def
      using cc_s.simps by auto
  next
    case True
    show ?thesis unfolding link_ext_def
    proof (rule cc_s.intros (3))
      show "V \<noteq> {}" using True by fast
      show "{s \<in> powerset V. x \<notin> s \<and> insert x s \<in> K} \<subseteq> powerset V"
        using True unfolding powerset_def by auto
      from v have pcK: "pow_closed K" 
        using cc_s.simps True
        by (meson cc_s_closed pow_closed_def)
      show "pow_closed {s \<in> powerset V. x \<notin> s \<and> insert x s \<in> K}"
        using pcK
        unfolding pow_closed_def powerset_def
        by auto (meson insert_mono)
    qed
  qed
qed

(*definition link :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K \<and> s \<union> {x} \<in> K}"*)

definition link :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K \<and> insert x s \<in> K}"

lemma link_intro [intro]: 
  "y \<in> powerset (V - {x}) \<Longrightarrow> y \<in> K \<Longrightarrow> insert x y \<in> K \<Longrightarrow> y \<in> link x V K"
  using link_def by simp

lemma link_mono:
  assumes "K \<subseteq> L"
  shows "link x V K \<subseteq> link x V L"
  using assms unfolding link_def powerset_def by auto

lemma link_subset_link_ext:
  "link x V K \<subseteq> link_ext x V K"
  unfolding link_def link_ext_def powerset_def by auto

lemma
  cc_s_link_eq_link_ext:
  assumes cc: "(V, K) \<in> cc_s" 
  shows "link x V K = link_ext x V K"
proof
  show "link x V K \<subseteq> link_ext x V K" using link_subset_link_ext .
  show "link_ext x V K \<subseteq> link x V K"
  proof
    fix y assume y: "y \<in> link_ext x V K"
    from y have y: "y \<in> powerset (V - {x})" and yu: "insert x y \<in> K"
      unfolding link_ext_def powerset_def by auto
    show "y \<in> link x V K"
    proof (intro link_intro)
      show "y \<in> powerset (V - {x})" using y .
      show "insert x y \<in> K" using yu .
      show "y \<in> K" 
      proof (rule cc_s_closed [of _ "insert x y" V])
        show "y \<subseteq> insert x y" by auto
        show "(V, K) \<in> cc_s" by (rule assms (1))
        show "insert x y \<in> K" using yu .
      qed
    qed
  qed
qed

lemma
  assumes v: "(V,K) \<in> cc_s" and x: "x \<in> V"
  shows "(V, {s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K}) \<in> cc_s"
proof (cases "V = {}")
  case True then have False using x by fast
  thus ?thesis by fast
next
  case False
  show ?thesis
  proof (rule cc_s.intros (3))
    show "V \<noteq> {}" using False by fast
    have "K \<subseteq> powerset V" using cc_s_subset [OF v] .
    thus "{s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K} \<subseteq> powerset V" by auto
    have "pow_closed K" using v
      by (simp add: cc_s_closed pow_closed_def)
    then show "pow_closed {s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K}"
      unfolding pow_closed_def by auto (meson insert_mono)
  qed
qed

definition closed_remove_element :: "nat set set \<Rightarrow> bool"
  where "closed_remove_element K = (\<forall>c\<in>K. \<forall>x\<in>c. c - {x} \<in> K)"

lemma
  cc_s_closed_remove_element:
  assumes cc_s: "(V, K) \<in> cc_s"
  shows "closed_remove_element K"
proof (unfold closed_remove_element_def, rule, rule)
  fix c x
  assume c: "c \<in> K" and x: "x \<in> c"
  then have v: "V \<noteq> {}" using cc_s
    using cc_s.cases by blast
  have "pow_closed K" 
    using cc_s c cc_s.cases by blast
  then show "c - {x} \<in> K" using c unfolding pow_closed_def by simp
qed

lemma
  closed_remove_element_cc_s:
  assumes v: "V \<noteq> {}"
    and f: "finite V"
    and k: "K \<subseteq> powerset V" 
    and cre: "closed_remove_element K"
  shows "(V, K) \<in> cc_s"
proof
  show "V \<noteq> {}" using v .
  show "K \<subseteq> powerset V" using k .
  show "pow_closed K"
  proof (unfold pow_closed_def, safe)
    fix s s'
    assume s: "s \<in> K" and s's: "s' \<subseteq> s"
    have fs: "finite s" using s f k unfolding powerset_def
      by (meson PowD finite_subset in_mono)
    have fs': "finite s'" by (rule finite_subset [OF s's fs])
    show "s' \<in> K"
    using s's fs' fs s proof (induct "card (s - s')" arbitrary: s s')
      case 0 fix s :: "nat set" and s' :: "nat set"
      assume eq: "0 = card (s - s')" and subset: "s' \<subseteq> s" 
        and fs': "finite s'" and fs: "finite s" and s: "s \<in> K"
      have "s' = s" using eq subset fs by simp 
      thus "s' \<in> K" using s by fast
    next
      case (Suc n)
      fix s'
      assume hyp: "\<And>s s'. n = card (s - s') \<Longrightarrow> s' \<subseteq> s \<Longrightarrow> finite s' \<Longrightarrow> finite s \<Longrightarrow> s \<in> K \<Longrightarrow> s' \<in> K"
        and suc: "Suc n = card (s - s')" and subset: "s' \<subseteq> s" and fs': "finite s'"
        and fs: "finite s" and s: "s \<in> K" 
      from suc obtain x where xs: "x \<in> s" and xs': "x \<notin> s'"
        by (metis Diff_eq_empty_iff card_0_eq finite_Diff fs old.nat.distinct(2) subsetI)
      have s's: "s - s' = insert x ((s - {x}) - s')" using xs xs' by auto
      have card: "card ((s - {x}) - s') = n"
         using suc fs' fs xs xs'
        by (metis Diff_insert2 card_Diff_insert diff_Suc_1)
      show "s' \<in> K"
      proof (rule hyp [of "s - {x}"])
       show "n = card (s - {x} - s')" using card by safe
       show "s' \<subseteq> s - {x}" using subset xs xs' by auto
       show "finite s'" using fs' .
       show "finite (s - {x})" using fs by simp
       show "s - {x} \<in> K" using cre s xs unfolding closed_remove_element_def by simp
     qed
   qed
 qed
qed

lemma 
  assumes "K \<subseteq> powerset V"
  shows "closed_remove_element K"

lemma
  assumes v: "(V, {s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K}) \<in> cc_s"
    and x: "x \<notin> V"
  shows "(insert x V,K) \<in> cc_s" 
proof (rule cc_s.intros (3))
  show "insert x V \<noteq> {}" by fast
  have "{s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K} \<subseteq> powerset V" using cc_s_subset [OF v] .
  thus " K \<subseteq> powerset (insert x V)" using x unfolding powerset_def apply auto try
proof (cases "V = {}")
  case True then have False using x by fast
  thus ?thesis by fast
next
  case False
  show ?thesis
  proof (rule cc_s.intros (3))
    show "V \<noteq> {}" using False by fast
    have "K \<subseteq> powerset V" using cc_s_subset [OF v] .
    thus "{s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K} \<subseteq> powerset V" by auto
    have "pow_closed K" using v
      by (simp add: cc_s_closed pow_closed_def)
    then show "pow_closed {s. x \<notin> s \<and> s \<in> K \<and> insert x s \<in> K}"
      unfolding pow_closed_def by auto (meson insert_mono)
  qed
qed

   
lemma
  link_eq_link_ext_cc_s:
  assumes link_eq: "\<forall>x\<in>V. link x V K = link_ext x V K" 
    and finite: "finite V" and K: "K \<subseteq> powerset V"
  shows "(V, K) \<in> cc_s"
proof (intro cc_s.intros)
  show "V \<noteq> {}" using x by fast
  show "K \<subseteq> powerset V" using K .
  show "pow_closed K"
  proof (unfold pow_closed_def, safe)
    fix s s'
    assume s: "s \<in> K" and s': "s' \<subseteq> s"
    hence finite_s: "finite s" and finite_s': "finite s'" 
      using K finite unfolding powerset_def
      by (meson Pow_iff finite_subset in_mono)+
    from s' finite_s  finite_s' obtain s''
      where s'_dif: "s' = s - s''" and s_inter: "s' \<inter> s'' = {}" 
        and finite_s'': "finite s''"
      by auto
    show "s' \<in> K"
      using s s'_dif s_inter finite_s''
    proof (induct "card (s'')" arbitrary: s'' s' s)
      case 0 hence "s'' = {}" by simp
      then show ?case using s "0.prems" by simp
    next
      case (Suc xa)
      then obtain A x
        where s''_def: "s'' = A \<union> {x}" and card_A: "card A = xa"
          and "s' = s - s''" and "s' \<inter> s'' = {}" and "finite s''"
        by (metis Un_commute Un_insert_right card_Suc_eq sup_bot.left_neutral)



      from Suc.hyps (1) [of A s "s' \<union> {x}"] have "s' \<union> {x} \<in> K"
        apply auto try
      have ""
      then show ?case sorry
    qed
      case True
      hence "s - {x} \<in> link_ext x V K" 
        unfolding link_ext_def powerset_def using s
        using K in_mono insert_Diff powerset_def by fastforce
      hence "s - {x} \<in> link x V K" using link_eq by fast
      then have "s' - {x} \<in> link x V K" unfolding link_def powerset_def
        using s' try
        show ?thesis unfolding link_def
      using link_eq unfolding link_def
  show ?thesis
    sorry
qed
qed

lemma link_empty [simp]: "link x V {} = {}" unfolding link_def powerset_def by simp

lemma link_empty_singleton [simp]: "link x {} {{}} = {}" 
  unfolding link_def powerset_def try by auto

lemma link_nempty_singleton [simp]: 
  "V \<noteq> {} \<Longrightarrow> link x V {{}} = {}" 
  unfolding link_def powerset_def by simp

definition cost :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K}"

lemma cost_empty [simp]: "cost x V {} = {}" unfolding cost_def powerset_def by simp

lemma cost_singleton [simp]: "cost x V {{}} = {{}}" unfolding cost_def powerset_def by auto

function evaluation :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool list"
  where
  "evaluation [] {} = [False]"
  | "A \<noteq> {} \<Longrightarrow> evaluation [] A = [True]"
  (*| "evaluation (Cons x []) {} = [False, False]"
  | "evaluation (Cons x []) {{}} = [True, False]"
  | "evaluation (Cons x []) {{},{x}} = [True, True]"*)
  | "evaluation (Cons x l) K = 
        append (evaluation l (cost x (set l) K)) (evaluation l (link x (set l) K))"
  unfolding cost_def link_def powerset_def 
  by (auto) (meson neq_Nil_conv)
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). length V)", simp_all)
qed

lemma length_evaluation_empty_list [simp]: "length (evaluation [] K) = 1" 
  by (cases "K = {}", simp_all)

instantiation list :: (ord) ord  
begin

definition "less_eq l m \<equiv> (length l \<le> length m) \<and> (\<forall>i<length l. l!i \<le> m!i)"

definition "less l m \<equiv> (length l \<le> length m) \<and> (\<forall>i<length l. l!i < m!i)"

instance
proof

qed

end

lemma "powerset {} = {{}}" unfolding powerset_def by simp

lemma "powerset {x} = {{},{x}}" unfolding powerset_def by auto

lemma
  powerset_singleton_cases:
  assumes K: "K \<subseteq> powerset {x}"
  shows "K = {} \<or> K = {{}} \<or> K = {{x}} \<or> K = {{},{x}}" 
  using K
  unfolding powerset_def
  by (smt (verit, del_insts) Pow_singleton empty_subsetI insert_commute insert_subsetI subset_antisym subset_insert)

lemma
  assumes "finite X" and "K \<subseteq> powerset (X)" and "L \<subseteq> powerset (X)" 
    and "K \<subseteq> L"
   and "(X, l) \<in> obdt_list"
 shows "evaluation l K \<le> evaluation l L"
proof (cases "card X")
  case 0
  then have x: "X = {}" by (simp add: assms(1))
  have l: "l = []"
    using assms (5)
    using obdt_list.cases x by auto
  then have K: "K = {} \<or> K = {{}}" and L: "L = {} \<or> L = {{}}" 
    using assms(2,3) unfolding x unfolding powerset_def by auto
  show ?thesis
  proof (cases "K = {}")
    case True
    show ?thesis unfolding l unfolding True using L
      unfolding less_eq_list_def by auto
  next
    case False
    hence "K = {{}}" and "L = {{}}" using L K assms (4) by blast+
    thus ?thesis unfolding BDT.less_eq_list_def by simp
  qed
next
  case Suc
  fix n :: nat
  assume card: "card X = Suc n"
  show "evaluation l K \<le> evaluation l L"
  proof (cases "n = 0")
    case True
    then obtain x where x: "X = {x}" using card
      by (meson card_1_singleton_iff)
    have l: "l = [x]" using assms (5) unfolding x
      by (metis assms(5) insert_absorb insert_eq_iff insert_not_empty obdt_list.cases x)
    from x have K_cases: "K = {} \<or> K = {{}} \<or> K = {{x}} \<or> K = {{}, {x}}"
      using powerset_singleton_cases [of K x] assms(2) by simp
    from x have L_cases: "L = {} \<or> L = {{}} \<or> L = {{x}} \<or> L = {{}, {x}}" 
      using powerset_singleton_cases [of L x] assms(3) by simp
    show ?thesis
    proof (cases "K = {}")
      case True note K = True
      have lhs: "evaluation l K = [False, False]" 
        unfolding l True evaluation.simps by simp
      show ?thesis
      proof (cases "L = {}")
        case True show ?thesis unfolding l K True
          by (simp add: less_eq_list_def)
      next
        case False note L = False
        show ?thesis 
        proof (cases "L = {{}}")
          case True show ?thesis unfolding l True K less_eq_list_def
            by (simp add: nth_Cons')
        next
          case False note L' = False
          show ?thesis
          proof (cases "L = {{x}}")
            case True show ?thesis 
              unfolding l True K less_eq_list_def evaluation.simps 
                cost_def link_def powerset_def 
              by auto (metis diff_Suc_1 less_Suc0 less_SucE nth_Cons')
          next
            case False hence L: "L = {{},{x}}" using L L' L_cases by simp
            show ?thesis 
              unfolding l L K
              unfolding evaluation.simps less_eq_list_def
              by auto (metis diff_Suc_1 less_Suc0 less_SucE nth_Cons')
          qed
        qed
      qed
    next
    case False note K_nempty = False
    show ?thesis
    proof (cases "K = {{}}")
      case True note K = True 
      hence L_cases: "L = {{}} \<or> L = {{x}} \<or> L = {{},{x}}" 
        using assms (4) using L_cases by auto 
      show ?thesis
      proof (cases "L = {{}}")
        case True
        show ?thesis unfolding K True less_eq_list_def by simp
      next
        case False note L = False
        hence L_cases: "L = {{x}} \<or> L = {{},{x}}" using L_cases by simp
        show ?thesis
        proof (cases "L = {{x}}")
          case True
          show ?thesis unfolding True K l evaluation.simps 
            apply auto
            using K True assms(4) by blast
        next
          case False hence L: "L = {{},{x}}" using L_cases by simp
          show ?thesis 
            unfolding L K l evaluation.simps less_eq_list_def 
            unfolding cost_def link_def powerset_def
            by auto (simp add: nth_Cons')
        qed
      qed
    next
      case False note K_nsingleton = False
      hence "K = {{x}} \<or> K = {{},{x}}" using K_cases K_nempty by simp
      show ?thesis
      proof (cases "K = {{x}}")
        case True note K = True
        hence L_cases: "L = {{x}} \<or> L = {{},{x}}" using L_cases assms (4)
          by auto
        show ?thesis 
        proof (cases "L = {{x}}")
          case True
          show ?thesis unfolding K True l
            by (meson less_eq_list_def linorder_linear)
        next
          case False hence L: "L = {{},{x}}" using L_cases by simp
          show ?thesis 
            unfolding l K L less_eq_list_def evaluation.simps
            unfolding link_def cost_def powerset_def
            using evaluation.simps
            by auto (simp add: nth_Cons')
        qed
      next
        case False
        hence K: "K = {{},{x}}" using K_cases K_nempty K_nsingleton by simp
        hence L: "L = {{},{x}}" using assms (4) L_cases by auto
        show ?thesis unfolding K L l less_eq_list_def by auto
      qed
    qed
  qed
next
  case False note n = False
  show ?thesis



lemma
  assumes "finite X" and "(X, K) \<in> cc_s" and "(X, L) \<in> cc_s" and "K \<subseteq> L"
   and "(X, l) \<in> obdt_list"
 shows "evaluation l K \<le> evaluation l L"
proof (cases "card X")
  case 0
  then have x: "X = {}" by (simp add: assms(1))
  have l: "l = []"
    using assms (5)
    using obdt_list.cases x by auto
  moreover have k: "K = {}" and L: "L = {}"
    using assms(2,3) cc_s.cases x by blast+
  ultimately show ?thesis unfolding l k L using BDT.less_eq_list_def by fast
  proof (cases "K = {}")
    case True note K = True
    show ?thesis
    proof (cases "L = {}")
      case True
      show ?thesis 
        unfolding l K True evaluation.simps(1) 
        using BDT.less_eq_list_def by fast
    next
      case False hence L: "L = {{}}" using L by fast
      show ?thesis 
        unfolding l K L evaluation.simps(1) 
          using evaluation.simps(2) [of "{{}}"]
          by (simp add: BDT.less_eq_list_def)
      qed
    next
      case False hence K: "K = {{}}" using cc_s_empty assms(2) unfolding x by auto
      hence L: "L = {{}}" using assms(4) using cc_s_empty assms(3) unfolding x by auto
      show ?thesis unfolding l K L unfolding BDT.less_eq_list_def by simp
    qed
 next
  case (Suc nat)
  then show ?thesis sorry
qed

lemma "evaluation (Cons x []) {} = [False, False]" 
  unfolding evaluation.simps cost_def link_def by simp

lemma "evaluation (Cons x []) {{}} = [True, False]" 
  unfolding evaluation.simps cost_def link_def powerset_def by simp

lemma "evaluation (Cons x []) {{},{x}} = [True, True]" 
  unfolding evaluation.simps cost_def link_def powerset_def by simp



function evaluation :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool list"
  where "evaluation [] {} = [False]"
  | "evaluation (Cons x []) {} = [False, False]"
  | "evaluation (Cons x []) {{}} = [True, False]"
  | "evaluation (Cons x []) {{},{x}} = [True, True]"
  | "evaluation (Cons x l) K = 
        append (evaluation l (cost x (set l) K)) (evaluation l (link x (set l) K))"
  unfolding cost_def link_def powerset_def
                 apply (auto) try
  apply auto[1]
proof
"
  unfolding link_def cost_def powerset_def
                 apply auto prefer 2
      apply (metis card_insert_le linorder_not_less) prefer 2
         apply (metis card_insert_le linorder_not_less)
  prefer 2 apply (metis card_insert_le linorder_not_less) try
  apply (simp_all add: card_gt_0_iff le_simps(3)) prefer 2 try


partial_function (tailrec) evaluation
  where "evaluation X A K = (if X = {} \<and> A = [] \<and> K = {} then [False] 
                            else if card X = 1 \<and> K = {} then [False, False]
                            else if card X = 1 \<and> K = {{}} then [True, False]
                            else if card X = 1 \<and> K = {{},set A} then [True, True]
          else if card X > 1 \<and> (A = Cons x A') then
             (evaluation X A K) else undefined)"

partial_function (tailrec) evaluation
  where "evaluation X A K = (if X = {} \<and> A = [] \<and> K = {} then [False] 
                            else if card X = 1 \<and> K = {} then [False, False]
                            else if card X = 1 \<and> K = {{}} then [True, False]
                            else if card X = 1 \<and> K = {{},set A} then [True, True]
          else if card X > 1 \<and> (A = Cons x A') then
            append (evaluation (X - {x}) A' (cost x X K))
                    (evaluation (X - {x}) A' (link x X K)) else undefined)"



partial_function (tailrec) evaluation
  where "evaluation A K = (if A = [] \<and> K = {} then [False] 
                            else if length A = 1 \<and> K = {} then [False, False]
                            else if length A = 1 \<and> K = {{}} then [True, False]
                            else if length A = 1 \<and> K = {{},set A} then [True, True]
          else if length A > 1 \<and> x \<in> A then
                append (evaluation (A - x) (cost x (set A) K)) (evaluation (A - x) (link x A K)) else undefined)"

inductive_set evaluation :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool list set"
  where "evaluation {} {} = [False]"
  | "evaluation {x} {} = [False, False]"
  | "evaluation {x} {{}} = [True, False]"
  | "evaluation {x} {{},{x}} = [True, True]"
  | "A \<noteq> {} \<Longrightarrow> evaluation (insert x A) K = 
                  append (evaluation A (cost x A K)) (evaluation A (link x A K))"
  unfolding link_def cost_def powerset_def
                 apply auto prefer 3 try



function evaluation :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> bool list"
  where "evaluation {} {} {} = [False]"
  | "card X = 1 \<Longrightarrow> evaluation X A {} = [False, False]"
  | "card X = 1 \<Longrightarrow> evaluation X A {{}} = [True, False]"
  | "card X = 1 \<Longrightarrow> evaluation X A {{},A} = [True, True]"
  | "card X > 1 \<Longrightarrow> x \<in> A \<Longrightarrow> evaluation X (insert x A) K =
                  append (evaluation X (A - {x}) (cost x A K)) 
                          (evaluation X (A - {x}) (link x A K))"
  unfolding link_def cost_def powerset_def
                 apply auto prefer 2
      apply (metis card_insert_le linorder_not_less) prefer 2
         apply (metis card_insert_le linorder_not_less)
  prefer 2 apply (metis card_insert_le linorder_not_less) try
  apply (simp_all add: card_gt_0_iff le_simps(3)) prefer 2 try









function bdt :: "nat set \<Rightarrow> nat tree \<Rightarrow> bool"
  where "bdt {} Leaf = True"
  | "bdt {} (Node l e r) = False"
  (*| "bdt {k} (Node Leaf e Leaf) = (k = e)"*)
  | "bdt A (Node l e r) = (e \<in> A \<and> bdt (A - {e}) l \<and> bdt (A - {e}) r)"
                 prefer 2 apply simp prefer 2 apply simp prefer 2 apply simp prefer 2 apply simp
    prefer 2 apply simp prefer 2 apply simp apply simp_all try

function obdt :: "nat set \<Rightarrow> nat set \<Rightarrow> bool"
  where "obdt {} {} = True"
  | "obdt (insert x A) B = (x \<in> B \<and> obdt A B)"

  apply simp_all
  apply auto[1] try


  
function bdt :: "nat set \<Rightarrow> nat tree \<Rightarrow> bool"
  where "bdt {} \<langle>\<rangle> = True"
  | "bdt {} (Node l k r) = False"
  | "bdt (insert k A) \<langle>l, k, r\<rangle> = (bdt A l \<and> bdt A r)"
apply auto prefer 3 try sledgehammer


function bdt :: "nat set \<Rightarrow> nat tree \<Rightarrow> bool"
  where "bdt {} \<langle>\<rangle> = True"
  | "bdt {} (Node l k r) = False"
  | "bdt (insert i {}) Leaf = False"
  | "bdt (insert i {}) \<langle>\<langle>\<rangle>, i, \<langle>\<rangle>\<rangle> = True"
  | "bdt (insert i {}) \<langle>Node l k r, i, \<langle>\<rangle>\<rangle> = False"
  | "bdt (insert i {}) \<langle>\<langle>\<rangle>, i, Node l k r\<rangle> = False"
  | "bdt (insert i {}) \<langle>Node l1 k1 r1, i, Node l2 k2 r2\<rangle> = False"
  | "bdt (insert k A) \<langle>l, k, r\<rangle> = (bdt A l \<and> bdt A r)"
apply auto prefer 3 try sledgehammer

termination




context simplicial_complex
begin



end

end