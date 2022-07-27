
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

lemma
  obdt_list_length_coherent:
  assumes al: "(A, l) \<in> obdt_list" (*and f: "finite A"*)
  shows "card A = length l"
using al proof (induct)
  case 1
  then show ?case by simp
next
  case (2 A l x)
  then show ?case
    by (metis card_Suc_eq length_0_conv length_Cons neq_Nil_conv obdt_list.simps)
qed

lemma obdt_list_coherent:
  assumes al: "(A, l) \<in> obdt_list" (*and f: "finite A"*)
  shows "A = set l" using al by (induct, simp_all)

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
  link_eq_link_ext_cc_s:
  assumes v: "V \<noteq> {}"
    and f: "finite V"
    and k: "K \<subseteq> powerset V"
    and l: "\<forall>x\<in>V. link x V K = link_ext x V K"
  shows cc: "(V, K) \<in> cc_s"
proof (rule closed_remove_element_cc_s)
  show "V \<noteq> {}" using v .
  show "finite V" using f .
  show "K \<subseteq> powerset V" using k .
  show "closed_remove_element K"
  proof (unfold closed_remove_element_def, rule, rule)
    fix c x
    assume c: "c \<in> K" and x: "x \<in> c"
    have xn: "x \<notin> c - {x}" and xv: "x \<in> V"
      using c k powerset_def x by auto
    have "c - {x} \<in> link_ext x V K"
      using c x xn k 
      unfolding link_ext_def powerset_def 
      using insert_absorb [OF x] by auto
    hence "c - {x} \<in> link x V K" using l xv by simp
    thus "c - {x} \<in> K" unfolding link_def by simp
  qed
qed

lemma link_empty [simp]: "link x V {} = {}" 
  unfolding link_def powerset_def by simp

lemma link_empty_singleton [simp]: "link x {} {{}} = {}" 
  unfolding link_def powerset_def try by auto

lemma link_nempty_singleton [simp]: 
  "V \<noteq> {} \<Longrightarrow> link x V {{}} = {}" 
  unfolding link_def powerset_def by simp

definition cost :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K}"

lemma cost_empty [simp]: "cost x V {} = {}" 
  unfolding cost_def powerset_def by simp

lemma cost_singleton [simp]: "cost x V {{}} = {{}}" 
  unfolding cost_def powerset_def by auto

lemma cost_mono:
  assumes "K \<subseteq> L"
  shows "cost x V K \<subseteq> cost x V L"
  using assms unfolding cost_def powerset_def by auto

lemma link_subset_cost:
  shows "link x V K \<subseteq> cost x V K"
  unfolding link_def cost_def powerset_def by auto

function evaluation :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool list"
  where
  "evaluation [] {} = [False]"
  | "A \<noteq> {} \<Longrightarrow> evaluation [] A = [True]"
  (*| "evaluation (Cons x []) {} = [False, False]"
  | "evaluation (Cons x []) {{}} = [True, False]"
  | "evaluation (Cons x []) {{},{x}} = [True, True]"*)
  | "evaluation (x # l) K =
          (evaluation l (link x (set (x # l)) K)) @ 
          (evaluation l (cost x (set (x # l)) K))"
  unfolding cost_def link_def powerset_def 
  by (auto) (meson neq_Nil_conv)
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). length V)", simp_all)
qed

lemma length_evaluation_empty_list [simp]: 
  shows "length (evaluation [] K) = 1" 
  by (cases "K = {}", simp_all)

lemma length_evaluation_eq:
  shows "length (evaluation l K) = length (evaluation l L)"
proof (induct l arbitrary: K L)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  show ?case unfolding evaluation.simps
    using Cons.hyps [of "(cost a (set (a # l)) K)" "(cost a (set (a # l)) L)"]
    using Cons.hyps [of "(link a (set (a # l)) K)" "(link a (set (a # l)) L)"] 
    by simp
qed

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
  less_eq_list_append:
  assumes le1: "length l1 = length l2" and le2: "length l3 = length l4"
    and leq1: "l1 \<le> l2" and leq2: "l3 \<le> l4"
  shows "l1 @ l3 \<le> l2 @ l4"
proof (unfold less_eq_list_def, rule)
  show "length (l1 @ l3) \<le> length (l2 @ l4)" using le1 le2 by simp
  show "\<forall>i<length (l1 @ l3). (l1 @ l3) ! i \<le> (l2 @ l4) ! i" 
  proof (safe)
    fix i assume i: "i < length (l1 @ l3)"
    show "(l1 @ l3) ! i \<le> (l2 @ l4) ! i"
    proof (cases "i < length l1")
      case True 
      thus ?thesis using leq1 le1
        by (simp add: less_eq_list_def nth_append)
    next
      case False hence "length l1 \<le> i" by simp
      thus ?thesis 
        unfolding nth_append 
        using le1
        using leq2 le2 i unfolding less_eq_list_def by auto
    qed
  qed
qed

lemma
  evaluation_mono:
  assumes k: "K \<subseteq> powerset V" and l: "L \<subseteq> powerset V" 
    and kl: "K \<subseteq> L"
    (*and "(V, l) \<in> obdt_list"*)
 shows "evaluation l K \<le> evaluation l L"
using kl proof (induction l arbitrary: K L)
  case Nil
  then show ?case 
    using kl using evaluation.simps (1,2)
    unfolding less_eq_list_def
    by (metis One_nat_def bot.extremum_uniqueI le_boolE length_evaluation_empty_list less_Suc0 linorder_linear nth_Cons_0)
next
  case (Cons a l K L)
  note kl = Cons.prems
  show ?case
  proof (unfold evaluation.simps, rule less_eq_list_append)
  show "length (evaluation l (link a (set (a # l)) K)) = length (evaluation l (link a (set (a # l)) L))"
    and "length (evaluation l (cost a (set (a # l)) K)) = length (evaluation l (cost a (set (a # l)) L))"
    using length_evaluation_eq by simp_all
  show "evaluation l (cost a (set (a # l)) K) \<le> evaluation l (cost a (set (a # l)) L)"
    using Cons.IH [OF cost_mono [OF kl, of a "set (a # l)"]] .
  show "evaluation l (link a (set (a # l)) K) \<le> evaluation l (link a (set (a # l)) L)"
    using Cons.IH [OF link_mono [OF kl, of a "set (a # l)"]] .
  qed
qed

lemma
  append_eq_same_length:
  assumes mleq: "m1 @ m2 = l1 @ l2" 
    and lm: "length m1 = length m2" and ll: "length l1 = length l2"
  shows "m1 = l1" and "m2 = l2"
  using append_eq_conv_conj [of "m1" "m2" "l1 @ l2"]
  using mleq lm ll by force+

corollary evaluation_cost_link:
  assumes e: "evaluation l K = l1 @ l2" 
    and l :"length l1 = length l2"  
  shows "l1 \<le> l2"
proof (cases l)
  case Nil 
  have False
  proof (cases "K = {}")
    case True show False
      using e unfolding Nil True
      unfolding evaluation.simps (1) 
      using l
      by (metis Nil_is_append_conv append_eq_Cons_conv length_0_conv list.discI)
  next
    case False show False
    using e False unfolding Nil
    unfolding evaluation.simps (2) [OF False]
    using l
    by (metis Nil_is_append_conv append_eq_Cons_conv length_0_conv list.discI)
  qed
  thus ?thesis by fast
next
  case (Cons a l') note la = Cons
  have l1: "l1 = evaluation l' (link a (set (a # l')) K)"
  proof (rule append_eq_same_length [of "l1" "l2" "evaluation l' (link a (set (a # l')) K)" "evaluation l' (cost a (set (a # l')) K)"])
    show "l1 @ l2 = evaluation l' (link a (set (a # l')) K) @ evaluation l' (cost a (set (a # l')) K)"
      using e [symmetric] unfolding la unfolding evaluation.simps (3) .
    show "length l1 = length l2" using l .
    show "length (evaluation l' (link a (set (a # l')) K)) = length (evaluation l' (cost a (set (a # l')) K))"
      using length_evaluation_eq [of "l'" "link a (set (a # l')) K" "cost a (set (a # l')) K"] .
  qed
  have l2: "l2 = evaluation l' (cost a (set (a # l')) K)"
  proof (rule append_eq_same_length [of "l1" "l2" "evaluation l' (link a (set (a # l')) K)" "evaluation l' (cost a (set (a # l')) K)"])
    show "l1 @ l2 = evaluation l' (link a (set (a # l')) K) @ evaluation l' (cost a (set (a # l')) K)"
      using e [symmetric] unfolding la unfolding evaluation.simps (3) .
    show "length l1 = length l2" using l .
    show "length (evaluation l' (link a (set (a # l')) K)) = length (evaluation l' (cost a (set (a # l')) K))"
      using length_evaluation_eq [of "l'" "(link a (set (a # l')) K)" "(cost a (set (a # l')) K)"] .
  qed
  show ?thesis
    unfolding l1 l2
  proof (rule evaluation_mono [of _ "set (a # l')"])
    show "cost a (set (a # l')) K \<subseteq> powerset (set (a # l'))" unfolding cost_def powerset_def by auto
    show "link a (set (a # l')) K \<subseteq> powerset (set (a # l'))" unfolding link_def powerset_def by auto
    show "link a (set (a # l')) K \<subseteq> cost a (set (a # l')) K" by (rule link_subset_cost)
  qed
qed

inductive_set not_evaders :: "(bool list) set"
  where (*"[False, False] \<in> not_evaders"
  | "[True, True] \<in> not_evaders"
  |*) "l1 = l2 \<Longrightarrow> l1 @ l2 \<in> not_evaders"
  | "l1 \<in> not_evaders \<Longrightarrow> l2 \<in> not_evaders \<Longrightarrow> length l1 = length l2 \<Longrightarrow> l1 @ l2 \<in> not_evaders"

lemma "[] \<in> not_evaders"
  by (metis eq_Nil_appendI not_evaders.simps)

lemma "[False, False] \<in> not_evaders"
  by (metis append_eq_Cons_conv not_evaders.simps)

lemma "[True, True] \<in> not_evaders"
  by (metis append_eq_Cons_conv not_evaders.simps)

lemma true_evader: "[True] \<notin> not_evaders"
  by (smt (verit, best) Cons_eq_append_conv append_is_Nil_conv length_0_conv not_Cons_self2 not_evaders.cases)

lemma false_evader: "[False] \<notin> not_evaders"
  by (smt (verit, best) Cons_eq_append_conv append_is_Nil_conv length_0_conv not_Cons_self2 not_evaders.cases)

lemma "[True, False] \<notin> not_evaders"
proof (rule ccontr, safe)
  assume "[True, False] \<in> not_evaders"
  show False
    using not_evaders.cases [of "[True, False]"] true_evader false_evader
    by (smt (verit, ccfv_threshold) \<open>[True, False] \<in> not_evaders\<close> append_butlast_last_id append_eq_same_length(1) butlast.simps(2) last.simps list.distinct(1) list.size(4))
qed

lemma "[False, True] \<notin> not_evaders"
proof (rule ccontr, safe)
  assume "[False, True] \<in> not_evaders"
  show False
    using not_evaders.cases [of "[False, True]"] true_evader false_evader
    by (smt (verit, ccfv_threshold) \<open>[False, True] \<in> not_evaders\<close> append_butlast_last_id append_eq_same_length(1) butlast.simps(2) last.simps list.distinct(1) list.size(4))
qed

definition cone :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where "cone X K = (\<exists>x\<in>X. \<exists>T. T \<subseteq> powerset (X - {x}) \<and> K = T \<union> {s. \<exists>t\<in>T. s = insert x t})"

lemma 
  cone_disjoint:
  assumes "cone X K" and "x \<in> X" and t: "T \<subseteq> powerset (X - {x})"
   and "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "T \<inter> {s. \<exists>t\<in>T. s = insert x t} = {}"
  using t unfolding powerset_def by auto

(*definition cone :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where "cone X K = (\<exists>x\<in>X. \<exists>T. (X - {x}, T) \<in> cc_s \<and> K = T \<union> {s. \<exists>k\<in>K. s = insert x k})"
*)

lemma
  cone_cost_eq_link:
  assumes x: "x \<in> X" 
    and cs: "T \<subseteq> powerset (X - {x})" 
    and kt: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "cost x V K = link x V K"
proof
  show "link x V K \<subseteq> cost x V K" by (rule link_subset_cost) 
  show "cost x V K \<subseteq> link x V K"
    unfolding kt
    unfolding cost_def link_def powerset_def by auto
qed

(*The following property only holds assuming that K is a simplicial complex*)
(*lemma
  assumes x: "x \<in> X"
    and cs: "T \<subseteq> powerset (X - {x})" 
    and kt: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "cost x V K = T"
proof
  show "cost x V K \<subseteq> T" using cs unfolding cost_def powerset_def kt by auto
  show "T \<subseteq> cost x V K"
    unfolding kt
    unfolding cost_def powerset_def try by auto
qed*)

lemma
  cost_cone_eq:
  assumes x: "x \<in> V" (*and y: "y \<in> V"*) and xy: "x \<noteq> y"
    and cs: "T \<subseteq> powerset (V - {x})" 
    and kt: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "cost y V K = (cost y (V - {x}) T) \<union> {s. \<exists>t\<in>(cost y (V - {x}) T). s = insert x t}"
proof
  show "cost y V K \<subseteq> cost y (V - {x}) T \<union> {s. \<exists>t\<in>cost y (V - {x}) T. s = insert x t}"
  proof
    fix xa
    assume xa: "xa \<in> cost y V K"
    show "xa \<in> cost y (V - {x}) T \<union> {s. \<exists>t\<in>cost y (V - {x}) T. s = insert x t}"
    proof (cases "x \<in> xa")
      case False
      from xa and False have "xa \<in> T" and "xa \<in> Pow (V - {x} - {y})" 
        unfolding kt cost_def powerset_def by auto
      thus ?thesis unfolding cost_def powerset_def  by simp
    next
      case True note xxa = True
      show ?thesis
      proof (cases "xa \<in> T")
        case True
        obtain xa'
          where "xa' \<in> Pow (V - {x} - {y})" and "xa' \<in> T" and "xa = insert x xa'"
          using cs True xxa unfolding powerset_def by auto
        thus ?thesis unfolding cost_def powerset_def by auto
      next
        case False
        with xxa and xa and cs obtain t
          where xapow: "xa \<in> Pow (V - {y})" and xainsert: "xa = insert x t" 
            and tT: "t \<in> T" and tpow: "t \<in> Pow (V - {x} - {y})"
          unfolding kt cost_def powerset_def by blast
        thus ?thesis unfolding cost_def powerset_def by auto
      qed
    qed
  qed
  show "cost y (V - {x}) T \<union> {s. \<exists>t\<in>cost y (V - {x}) T. s = insert x t} \<subseteq> cost y V K"
    unfolding kt cost_def powerset_def using x xy by auto
qed

lemma
  link_cone_eq:
  assumes x: "x \<in> V" (*and y: "y \<in> V"*) and xy: "x \<noteq> y"
    (*and c: "cone V K"*)
    and cs: "T \<subseteq> powerset (V - {x})" 
    and kt: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "link y V K = (link y (V - {x}) T) \<union> {s. \<exists>t\<in>(link y (V - {x}) T). s = insert x t}"
proof
  show "link y (V - {x}) T \<union> {s. \<exists>t\<in>link y (V - {x}) T. s = insert x t} \<subseteq> link y V K"
    unfolding kt link_def powerset_def using x xy by auto
  show "link y V K \<subseteq> link y (V - {x}) T \<union> {s. \<exists>t\<in>link y (V - {x}) T. s = insert x t}"
  unfolding link_def [of y V K]
  unfolding link_def [of y "V - {x}" T]
  proof
    fix xa
    assume "xa \<in> {s \<in> powerset (V - {y}). s \<in> K \<and> insert y s \<in> K}"
    hence xap: "xa \<in> powerset (V - {y})" and xak: "xa \<in> K" and iyxa: "insert y xa \<in> K" by auto
    show "xa \<in> {s \<in> powerset (V - {x} - {y}). s \<in> T \<and> insert y s \<in> T} \<union>
           {s. \<exists>t\<in>{s \<in> powerset (V - {x} - {y}). s \<in> T \<and> insert y s \<in> T}. s = insert x t}"
    proof (cases "x \<in> xa")
      case False note xnxa = False
      hence xapxy: "xa \<in> powerset (V - {x} - {y})" using xap xy unfolding powerset_def by auto
      moreover have "xa \<in> T" using xak kt False by auto
      moreover have "insert y xa \<in> T"
      proof (cases "insert y xa \<in> T")
        case True then show ?thesis by simp
      next
        case False with iyxa and kt have "insert y xa \<in> {s. \<exists>t\<in>T. s = insert x t}"
          by simp
        then have "False" using xnxa
          using xy by blast
        thus ?thesis by (rule ccontr)
      qed
      ultimately have "xa \<in> {s \<in> powerset (V - {x} - {y}). s \<in> T \<and> insert y s \<in> T}"
        by auto
      thus ?thesis by fast
    next
      case True note xxa = True
      then obtain t where xai: "xa = insert x t" and xnt: "x \<notin> t" 
        using Set.set_insert [OF True] by auto
      have "t \<in> powerset (V - {x} - {y})" 
        using xap xai xnt unfolding powerset_def by auto
      moreover have t: "t \<in> T"
      proof (cases "xa \<in> T")
        case True
        have "xa \<notin> {s. \<exists>t\<in>T. s = insert x t}" 
          using x cs kt True unfolding powerset_def by auto
        then have False using xai True by auto
        then show ?thesis by (rule ccontr)
      next
        case False
        with cs kt xak have "xa \<in> {s. \<exists>t\<in>T. s = insert x t}" by simp
        with xai xnt False show ?thesis
          by auto (metis insert_absorb insert_ident)
      qed
      moreover have "insert y t \<in> T"
      proof (cases "insert y xa \<in> T")
        case True then have False
          using cs xxa unfolding powerset_def by auto
        thus ?thesis by (rule ccontr)
      next
        case False
        (*with xai iyxa kt have "insert y xa \<in> {s. \<exists>t\<in>T. s = insert x t}" by simp
        with xai xap xnt show ?thesis
          unfolding powerset_def try*)
        then show ?thesis
          using xai xap xnt kt iyxa unfolding powerset_def
          by (smt (verit, del_insts) Diff_insert_absorb PowD UnE Un_insert_right insert_absorb insert_is_Un iyxa kt mem_Collect_eq powerset_def singletonD subset_Diff_insert xai xap xnt)
      qed
      ultimately show ?thesis using xai by auto
    qed
  qed
qed

lemma
  assumes k: "K \<subseteq> powerset X"
    and c: "cone X K" and X: "X \<noteq> {}" and f: "finite X" and xl: "(X, l) \<in> obdt_list"
  shows "evaluation l K \<in> not_evaders"
proof -
  from c obtain x :: nat and T :: "nat set set"
    where x: "x \<in> X" and cs: "T \<subseteq> powerset (X - {x})" and kt: "K = T \<union> {s. \<exists>k\<in>T. s = insert x k}"
    unfolding cone_def by auto
  show ?thesis
  using X f xl c proof (induct "card X" arbitrary: X l K)
    case 0 with f have x: "X = {}" by simp
    hence False using "0.prems" (1) by blast
    thus ?case by (rule ccontr)
  next
    case (Suc n)
    obtain x :: nat and T :: "nat set set"
      where x: "x \<in> X" and cs: "T \<subseteq> powerset (X - {x})"
        and kt: "K = T \<union> {s. \<exists>k\<in>T. s = insert x k}"
      using Suc.prems (4) unfolding cone_def by auto
    obtain y l' where l: "l = y # l'" and y: "y \<in> X"
      using Suc.prems Suc.hyps (2) obdt_list_length_coherent [OF Suc.prems (3)]
      by (metis insert_iff obdt_list.cases)
    show ?case
      unfolding l 
      unfolding evaluation.simps (3) 
      unfolding l [symmetric] 
      unfolding obdt_list_coherent [OF Suc.prems (3), symmetric]
    proof (cases "x = y")
      case True
      have cl_eq: "cost x X K = link x X K"
        by (rule cone_cost_eq_link [of x X T], rule x, rule cs, rule kt)
      show "evaluation l' (link y X K) @
            evaluation l' (cost y X K)
            \<in> not_evaders"
        using True using cl_eq unfolding l [symmetric]
        using not_evaders.intros(1) by presburger
    next
      case False
      have crw: "cost y X K = cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}"
      proof (rule cost_cone_eq)
        show "x \<in> X" using x .
        show "x \<noteq> y" using False .
        show "T \<subseteq> powerset (X - {x})" using cs .
        show "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" using kt .
      qed            
      have lrw: "link y X K = link y (X - {x}) T \<union> {s. \<exists>t\<in>link y (X - {x}) T. s = insert x t}"
      proof (rule link_cone_eq)
        show "x \<in> X" using x .
        show "x \<noteq> y" using False .
        show "T \<subseteq> powerset (X - {x})" using cs .
        show "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" using kt .
      qed
      show "evaluation l' (link y X K) @ evaluation l' (cost y X K) \<in> not_evaders"
        unfolding crw lrw
      proof (rule not_evaders.intros(2))
        show "evaluation l' (link y (X - {x}) T \<union> {s. \<exists>t\<in>link y (X - {x}) T. s = insert x t}) \<in> not_evaders"
        proof (rule Suc.hyps (1) [of "X - {y}"])
          show "n = card (X - {y})" using Suc.hyps (2) y x False by simp
          show "X - {y} \<noteq> {}" using x False by auto
          show "finite (X - {y})" using Suc.prems (2) by simp
          show "(X - {y}, l') \<in> obdt_list" 
            using Suc.prems (3) using l y Suc.prems (1)
            by (metis Diff_insert_absorb list.inject obdt_list.cases)
          show "cone (X - {y}) (link y (X - {x}) T \<union> {s. \<exists>t\<in>link y (X - {x}) T. s = insert x t})"
            unfolding cone_def
          proof (intro bexI [of _ x] exI [of _ "link y (X - {x}) T"], rule conjI)
            show "link y (X - {x}) T \<subseteq> powerset (X - {y} - {x})"
              unfolding link_def powerset_def by auto
            show "link y (X - {x}) T \<union> {s. \<exists>t\<in>link y (X - {x}) T. s = insert x t} =
                  link y (X - {x}) T \<union> {s. \<exists>t\<in>link y (X - {x}) T. s = insert x t}" ..
            show "x \<in> X - {y}" using x False by simp
          qed
        qed
        show "evaluation l' (cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}) \<in> not_evaders"
        proof (rule Suc.hyps (1) [of "X - {y}"])
          show "n = card (X - {y})" using Suc.hyps (2) y x False by simp
          show "X - {y} \<noteq> {}" using x False by auto
          show "finite (X - {y})" using Suc.prems (2) by simp
          show "(X - {y}, l') \<in> obdt_list" 
            using Suc.prems (3) using l y Suc.prems (1)
            by (metis Diff_insert_absorb list.inject obdt_list.cases)
          show "cone (X - {y}) (cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t})"
            unfolding cone_def
          proof (intro bexI [of _ x] exI [of _ "cost y (X - {x}) T"], rule conjI)
            show "cost y (X - {x}) T \<subseteq> powerset (X - {y} - {x})"
              unfolding cost_def powerset_def by auto
            show "cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t} =
                  cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}" ..
            show "x \<in> X - {y}" using x False by simp
          qed
        qed
        show "length (evaluation l' (link y (X - {x}) T \<union> {s. \<exists>t\<in>link y (X - {x}) T. s = insert x t})) =
              length (evaluation l' (cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}))"
          using length_evaluation_eq .
      qed
    qed
  qed
qed

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