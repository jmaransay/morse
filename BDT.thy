
theory BDT
  imports
    "HOL-Library.Tree"
begin

text\<open>The following file can be processed with Isabelle-2022\<close>

section\<open>BDT\<close>

inductive_set bdt :: "(nat set \<times> nat tree) set"
  where "({}, Leaf) \<in> bdt"
  | "({x}, (Node Leaf x Leaf)) \<in> bdt"
  | "(A, L) \<in> bdt \<and> (A, R) \<in> bdt \<Longrightarrow> (insert x A, (Node L x R)) \<in> bdt"

lemma "({}, Leaf) \<in> bdt" using bdt.intros (1) .

inductive_set bdt_s :: "(nat set \<times> nat tree) set"
  where "({}, Leaf) \<in> bdt_s"
  | "(A, L) \<in> bdt \<and> (A, R) \<in> bdt \<Longrightarrow> (insert x A, (Node L x R)) \<in> bdt_s"

lemma "bdt = bdt_s"
proof
  show "bdt \<subseteq> bdt_s"
  proof (auto simp add:  bdt.intros)
    fix a b
    assume bdt: "(a, b) \<in> bdt"
    then show "(a, b) \<in> bdt_s" 
    proof (cases "a = {}")
      case True
      then show ?thesis using bdt bdt.cases bdt_s.simps by auto
    next
      case False
      then show ?thesis
        by (smt (verit, best) bdt bdt.cases bdt.intros(1) bdt_s.intros(2))
    qed
  qed
  show "bdt_s \<subseteq> bdt"
  proof (auto simp add:  bdt.intros)
    fix a b
    assume bdt: "(a, b) \<in> bdt_s"
    then show "(a, b) \<in> bdt" 
    proof (cases "a = {}")
      case True
      then show ?thesis by (metis bdt bdt.simps bdt_s.simps)
    next
      case False
      then show ?thesis
        by (smt (verit, ccfv_threshold) bdt bdt.simps bdt_s.cases)
    qed
  qed
qed

section\<open>Ordered Binary Decision trees -- OBDT --\<close>

text\<open>We represent sorted sets of variables by means of a given list
  that contains the same elements as the set. These sorted sets of variables
  together with a hypergraph will give us the tools to evaluate a Boolean function
  over a given set of variables.\<close>

inductive_set sorted_variables :: "(nat set \<times> nat list) set"
  where "({}, []) \<in> sorted_variables"
  | "(A, l) \<in> sorted_variables \<Longrightarrow> x \<notin> A \<Longrightarrow> (insert x A, Cons x l) \<in> sorted_variables"

lemma "({1}, [1]) \<in> sorted_variables"
  by (simp add: sorted_variables.intros(1) sorted_variables.intros(2))

lemma "({1}, [1,1]) \<notin> sorted_variables"
  by (metis (no_types, lifting) insert_absorb insert_eq_iff insert_not_empty not_Cons_self2 sorted_variables.cases)

lemma "({1,2,3},[3,2,1]) \<in> sorted_variables"
  using sorted_variables.intros (1)
  using sorted_variables.intros (2) [of "{}" "[]" "1"]
  using sorted_variables.intros (2) [of "{1}" "[1]" "2"]
  using sorted_variables.intros (2) [of "{1,2}" "[2,1]" "3"]
  by (simp add: insert_commute sorted_variables.intros(2))

lemma
  sorted_variables_length_coherent:
  assumes al: "(A, l) \<in> sorted_variables"
  shows "card A = length l"
using al proof (induct)
  case 1
  then show ?case by simp
next
  case (2 A l x)
  then show ?case
    by (metis card_Suc_eq length_0_conv length_Cons neq_Nil_conv sorted_variables.simps)
qed

lemma sorted_variables_coherent:
  assumes al: "(A, l) \<in> sorted_variables"
  shows "A = set l" using al by (induct, simp_all)

lemma sorted_variables_distinct:
  assumes al: "(A, l) \<in> sorted_variables"
  shows "distinct l"
  using al card_distinct sorted_variables_coherent sorted_variables_length_coherent 
  by blast


section\<open>Powerset\<close>

text\<open>We use the term ``powerset'' just as a synonym of @{term Pow}.\<close>

definition powerset :: "nat set \<Rightarrow> nat set set"
  where "powerset A = Pow A"

lemma "powerset {} = {{}}" unfolding powerset_def by simp

lemma powerset_singleton: "powerset {x} = {{},{x}}" unfolding powerset_def by auto

lemma
  powerset_singleton_cases:
  assumes K: "K \<subseteq> powerset {x}"
  shows "K = {} \<or> K = {{}} \<or> K = {{x}} \<or> K = {{},{x}}" 
  using K
  by (smt (verit, del_insts) powerset_singleton insert_Diff subset_insert_iff subset_singletonD)

section\<open>Simplicial complexes\<close>

text\<open>In the following we introduce a definition 
  of simplicial complexes as a set of sets that
  satisfies the property of being closed by the 
  subset relation. It is worth noting that in the
  rest of the development we will mainly work with
  hypergraphs, or sets of sets without the property 
  of being closed by the subset relation, 
  and simplicial complexes will not be required.\<close>

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
  by (rule cc_s.intros(3) [of "{0,1,2}" "{{1},{}}"], 
      simp, unfold powerset_def, auto,
      unfold pow_closed_def, auto)

lemma "({0,1,2}, {{1},{2},{}}) \<in> cc_s"
  by (rule cc_s.intros(3) [of "{0,1,2}" "{{1},{2},{}}"], 
      simp, unfold powerset_def, auto,
      unfold pow_closed_def, auto)

lemma "({0,1,2}, {{1,2},{1},{2},{}}) \<in> cc_s"
  by (rule cc_s.intros(3) [of "{0,1,2}" "{{1,2},{1},{2},{}}"], 
      simp, unfold powerset_def, auto,
      unfold pow_closed_def, auto)

section\<open>Link and exterior link of a vertex in a set of sets\<close>

definition link_ext :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link_ext x V K = {s. s \<in> powerset V \<and> x \<notin> s \<and> insert x s \<in> K}"

lemma link_ext_empty [simp]: "link_ext x V {} = {}"
  by (simp add: link_ext_def)

lemma link_ext_closed:
  assumes k: "K \<subseteq> powerset V" 
  shows "link_ext v V K \<subseteq> powerset (V - {v})"
  using k unfolding powerset_def link_ext_def by auto

lemma link_ext_mono:
  assumes "K \<subseteq> L"
  shows "link_ext x V K \<subseteq> link_ext x V L"
  using assms unfolding link_ext_def powerset_def by auto

lemma link_ext_cc:
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

corollary link_ext_cc_s:
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

lemma link_ext_commute:
  assumes x: "x \<in> V" and y: "y \<in> V" 
  shows "link_ext y (V - {x}) (link_ext x V K) = 
        link_ext x (V - {y}) (link_ext y V K)"
  using x y unfolding link_ext_def powerset_def 
  by auto (simp add: insert_commute)+

definition link :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K \<and> insert x s \<in> K}"

lemma link_intro [intro]: 
  "y \<in> powerset (V - {x}) \<Longrightarrow> y \<in> K \<Longrightarrow> insert x y \<in> K \<Longrightarrow> y \<in> link x V K"
  using link_def by simp

lemma link_mono:
  assumes "K \<subseteq> L"
  shows "link x V K \<subseteq> link x V L"
  using assms unfolding link_def powerset_def by auto

lemma link_commute:
  assumes x: "x \<in> V" and y: "y \<in> V" 
  shows "link y (V - {x}) (link x V K) = link x (V - {y}) (link y V K)"
  using x y unfolding link_def powerset_def 
  by auto (simp add: insert_commute)+

lemma link_subset_link_ext:
  "link x V K \<subseteq> link_ext x V K"
  unfolding link_def link_ext_def powerset_def by auto

lemma cc_s_link_eq_link_ext:
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

lemma link_cc:
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

corollary link_cc_s:
  assumes v: "(V, K) \<in> cc_s"
  shows "(V, link x V K) \<in> cc_s" 
  using link_ext_cc_s [OF v, of x] 
  unfolding cc_s_link_eq_link_ext [OF v, symmetric] .

section\<open>A different characterization of simplicial complexes\<close>

definition closed_remove_element :: "nat set set \<Rightarrow> bool"
  where "closed_remove_element K = (\<forall>c\<in>K. \<forall>x\<in>c. c - {x} \<in> K)"

lemma cc_s_closed_remove_element:
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

lemma closed_remove_element_cc_s:
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

text\<open>The following result can be understood as the inverse 
  of @{thm cc_s_link_eq_link_ext}.\<close>

lemma link_eq_link_ext_cc_s:
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

section\<open>Costar of a vertex in a set of sets\<close>

definition cost :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K}"

lemma cost_closed:
  assumes k: "K \<subseteq> powerset V" 
  shows "cost v V K \<subseteq> powerset (V - {v})"
  using k unfolding powerset_def cost_def by auto

lemma cost_empty [simp]: "cost x V {} = {}" 
  unfolding cost_def powerset_def by simp

lemma cost_singleton [simp]: "cost x V {{}} = {{}}" 
  unfolding cost_def powerset_def by auto

lemma cost_mono:
  assumes "K \<subseteq> L"
  shows "cost x V K \<subseteq> cost x V L"
  using assms unfolding cost_def powerset_def by auto

lemma cost_commute:
  assumes x: "x \<in> V" and y: "y \<in> V" 
  shows "cost y (V - {x}) (cost x V K) = 
        cost x (V - {y}) (cost y V K)"
  using x y unfolding cost_def powerset_def by auto

lemma link_subset_cost:
  shows "link x V K \<subseteq> cost x V K"
  unfolding link_def cost_def powerset_def by auto

text\<open>The previous result does not hold for @{term link_ext}, 
  it is only true for @{term link}\<close>

lemma link_ext_cost_commute:
  assumes x: "x \<in> V" and y: "y \<in> V" and xy: "x \<noteq> y"
  shows "link_ext y (V - {x}) (cost x V K) = 
        cost x (V - {y}) (link_ext y V K)"
  using x y xy unfolding link_ext_def cost_def powerset_def by auto

lemma link_cost_commute:
  assumes x: "x \<in> V" and y: "y \<in> V" and xy: "x \<noteq> y"
  shows "link y (V - {x}) (cost x V K) = 
        cost x (V - {y}) (link y V K)"
  using x y xy unfolding link_def cost_def powerset_def by auto

section\<open>Open star of a vertex in a set of sets\<close>

definition star :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "star v V K = {s. s \<in> powerset V \<and> v \<in> s \<and> s \<in> K}"

lemma star_closed:
  assumes k: "K \<subseteq> powerset V" 
  shows "star v V K \<subseteq> powerset V"
  using k unfolding powerset_def star_def by auto

lemma vertex_in_star:
  assumes k: "K \<subseteq> powerset V" and x: "x \<in> star v V K"
  shows "v \<in> x"
  using k x unfolding powerset_def star_def by auto

lemma star_empty [simp]: "star x V {} = {}" 
  unfolding star_def powerset_def by simp

lemma star_empty_v_set [simp]: "star x {} K = {}" 
  unfolding star_def powerset_def by simp

lemma star_nempty [simp]: 
    assumes v: "V \<noteq> {}" 
  shows "star x V {{}} = {}"
  using v unfolding star_def powerset_def by simp

lemma star_mono:
  assumes "K \<subseteq> L"
  shows "star x V K \<subseteq> star x V L"
  using assms unfolding star_def powerset_def by auto

lemma star_commute:
  assumes x: "x \<in> V" and y: "y \<in> V" 
  shows "star y (V - {x}) (star x V K) = 
        star x (V - {y}) (star y V K)"
  using x y unfolding star_def powerset_def by auto

section\<open>Closed star of a vertex in a set of sets\<close>

definition closed_star :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "closed_star v V K = star v V K \<union> link v V K"

lemma closed_star_closed:
  assumes k: "K \<subseteq> powerset V" 
  shows "closed_star v V K \<subseteq> powerset V"
  using k unfolding powerset_def closed_star_def star_def link_def by auto

lemma closed_star_empty [simp]: "closed_star x V {} = {}" 
  unfolding closed_star_def star_def link_def powerset_def by simp

lemma closed_star_nempty [simp]: 
    assumes v: "V \<noteq> {}" 
  shows "closed_star x V {{}} = {}"
  using v unfolding closed_star_def star_def link_def powerset_def by simp

lemma
  cost_union_closed_star:
  assumes k: "K \<subseteq> powerset V" (*and v: "v \<in> V"*)
  shows "K = cost v V K \<union> closed_star v V K"
proof
  show "cost v V K \<union> closed_star v V K \<subseteq> K"
    unfolding cost_def closed_star_def star_def link_def powerset_def by auto  
  show "K \<subseteq> cost v V K \<union> closed_star v V K"
    using k unfolding cost_def closed_star_def star_def link_def powerset_def by auto
qed

text\<open>The premises can be omitted from the following statement:\<close>

lemma cost_inter_closed_star:
  (*assumes k: "K \<subseteq> powerset V" and v: "v \<in> V"*)
  shows "link v V K = cost v V K \<inter> closed_star v V K"
proof
  show "link v V K \<subseteq> cost v V K \<inter> closed_star v V K"
    unfolding link_def cost_def closed_star_def powerset_def by auto
  show "cost v V K \<inter> closed_star v V K \<subseteq> link v V K"
    unfolding link_def cost_def closed_star_def star_def powerset_def by auto
qed

section\<open>Evaluation of a list over a set of sets\<close>

function evaluation :: "nat list \<Rightarrow> nat set set \<Rightarrow> bool list"
  where
  "evaluation [] {} = [False]"
  | "A \<noteq> {} \<Longrightarrow> evaluation [] A = [True]"
  | "evaluation (x # l) K =
          (evaluation l (link_ext x (set (x # l)) K)) @ 
          (evaluation l (cost x (set (x # l)) K))"
  unfolding cost_def link_ext_def powerset_def 
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
    using Cons.hyps [of "(link_ext a (set (a # l)) K)" "(link_ext a (set (a # l)) L)"] 
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

lemma less_eq_list_append:
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

lemma evaluation_mono:
  assumes k: "K \<subseteq> powerset V" and l: "L \<subseteq> powerset V" 
    and kl: "K \<subseteq> L"
    (*and "(V, l) \<in> sorted_variables"*)
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
  show "length (evaluation l (link_ext a (set (a # l)) K)) = length (evaluation l (link_ext a (set (a # l)) L))"
    and "length (evaluation l (cost a (set (a # l)) K)) = length (evaluation l (cost a (set (a # l)) L))"
    using length_evaluation_eq by simp_all
  show "evaluation l (cost a (set (a # l)) K) \<le> evaluation l (cost a (set (a # l)) L)"
    using Cons.IH [OF cost_mono [OF kl, of a "set (a # l)"]] .
  show "evaluation l (link_ext a (set (a # l)) K) \<le> evaluation l (link_ext a (set (a # l)) L)"
    using Cons.IH [OF link_ext_mono [OF kl, of a "set (a # l)"]] .
  qed
qed

lemma append_eq_same_length:
  assumes mleq: "m1 @ m2 = l1 @ l2" 
    and lm: "length m1 = length m2" and ll: "length l1 = length l2"
  shows "m1 = l1" and "m2 = l2"
  using append_eq_conv_conj [of "m1" "m2" "l1 @ l2"]
  using mleq lm ll by force+

text\<open>The following result does not hold in general for 
  @{term link_ext}, but it is true for simplicial complexes,
  where @{thm cc_s_link_eq_link_ext} and then we can make use of 
  @{thm link_subset_cost} which holds in general.\<close>

corollary evaluation_cost_link_ext:
  assumes e: "evaluation l K = l1 @ l2"
    and cc_s: "(set l, K) \<in> cc_s"
    and l :"length l1 = length l2"
  shows "l1 \<le> l2"
using cc_s proof (cases l)
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
  have "l1 = evaluation l' (link_ext a (set (a # l')) K)"
  proof (rule append_eq_same_length [of "l1" "l2" "evaluation l' (link_ext a (set (a # l')) K)" "evaluation l' (cost a (set (a # l')) K)"])
    show "l1 @ l2 = evaluation l' (link_ext a (set (a # l')) K) @ evaluation l' (cost a (set (a # l')) K)"
      using e [symmetric] unfolding la unfolding evaluation.simps (3) .
    show "length l1 = length l2" using l .
    show "length (evaluation l' (link_ext a (set (a # l')) K)) = length (evaluation l' (cost a (set (a # l')) K))"
      using length_evaluation_eq [of "l'" "link_ext a (set (a # l')) K" "cost a (set (a # l')) K"] .
  qed
  hence l1: "l1 = evaluation l' (link a (set (a # l')) K)"
    using cc_s_link_eq_link_ext [OF cc_s, of a] 
    unfolding la by simp
  have l2: "l2 = evaluation l' (cost a (set (a # l')) K)"
  proof (rule append_eq_same_length [of "l1" "l2" "evaluation l' (link_ext a (set (a # l')) K)" "evaluation l' (cost a (set (a # l')) K)"])
    show "l1 @ l2 = evaluation l' (link_ext a (set (a # l')) K) @ evaluation l' (cost a (set (a # l')) K)"
      using e [symmetric] unfolding la unfolding evaluation.simps (3) .
    show "length l1 = length l2" using l .
    show "length (evaluation l' (link_ext a (set (a # l')) K)) = length (evaluation l' (cost a (set (a # l')) K))"
      using length_evaluation_eq [of "l'" "(link_ext a (set (a # l')) K)" "(cost a (set (a # l')) K)"] .
  qed
  show ?thesis
    unfolding l1 l2
  proof (rule evaluation_mono [of _ "set (a # l')"])
    show "cost a (set (a # l')) K \<subseteq> powerset (set (a # l'))" unfolding cost_def powerset_def by auto
    show "link a (set (a # l')) K \<subseteq> powerset (set (a # l'))" unfolding link_def powerset_def by auto
    show "link a (set (a # l')) K \<subseteq> cost a (set (a # l')) K" by (rule link_subset_cost)
  qed
qed

section\<open>Lists of Boolean elements with no evaders.\<close>

text\<open>The base cases, @{term "[False, False]"} 
  and  @{term "[True, True]"} belonging to the set 
  of no evaders, can be proven from the following 
  definition.\<close>

inductive_set not_evaders :: "(bool list) set"
  where 
  "l1 = l2 \<Longrightarrow> l1 @ l2 \<in> not_evaders"
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

lemma tf_not_not_evader: "[True, False] \<notin> not_evaders"
proof (rule ccontr, safe)
  assume "[True, False] \<in> not_evaders"
  show False
    using not_evaders.cases [of "[True, False]"] true_evader false_evader
    by (smt (verit, ccfv_threshold) \<open>[True, False] \<in> not_evaders\<close> append_butlast_last_id append_eq_same_length(1) butlast.simps(2) last.simps list.distinct(1) list.size(4))
qed

lemma ft_not_not_evader: "[False, True] \<notin> not_evaders"
proof (rule ccontr, safe)
  assume "[False, True] \<in> not_evaders"
  show False
    using not_evaders.cases [of "[False, True]"] true_evader false_evader
    by (smt (verit, ccfv_threshold) \<open>[False, True] \<in> not_evaders\<close> append_butlast_last_id append_eq_same_length(1) butlast.simps(2) last.simps list.distinct(1) list.size(4))
qed

section\<open>Join of a vertex with a set\<close>

definition join :: "nat \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "join v V = {{v}} \<union> V \<union> {w. \<exists>s\<in>V. w = insert v s}"

lemma [simp]:
  shows "{v} \<in> join v V"
   unfolding join_def by auto

lemma [simp]:
  assumes w: "w \<in> V"
  shows "w \<in> join v V"
  using w unfolding join_def by auto

lemma [simp]:
  assumes w: "w \<in> V"
  shows "{v} \<union> w \<in> join v V"
  using w unfolding join_def by auto

proposition
  assumes k: "K \<subseteq> powerset V" and p: "pow_closed K" and v: "{v} \<in> K"
  shows "closed_star v V K = join v (link v V K)"
proof
 show "join v (link v V K) \<subseteq> closed_star v V K"
    using k v
    unfolding join_def link_def closed_star_def star_def powerset_def pow_closed_def
    by auto
 show "closed_star v V K \<subseteq> join v (link v V K)"
    using k v p
    unfolding join_def link_def closed_star_def star_def powerset_def pow_closed_def
    apply simp 
    apply safe 
      apply auto [1] 
      apply auto [2]
      by (smt (verit, del_insts) Diff_empty Diff_subset insert_subset mk_disjoint_insert subset_Diff_insert)
qed

section\<open>A set of sets being a cone over a given vertex\<close>

definition cone :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where "cone X K = ((\<exists>x\<in>X. \<exists>T. T \<subseteq> powerset (X - {x})  
                      \<and> K = T \<union> {s. \<exists>t\<in>T. s = insert x t}))"

text\<open>There cannot be cones over an empty set of vertexes\<close>

lemma "\<not> cone {} K" unfolding cone_def by simp

text\<open>The trivial simplicial complex is a cone over a non-empty vertex set.\<close>

lemma cone_empty: assumes v: "V \<noteq> {}" shows "cone V {}"
  unfolding cone_def using v by auto

lemma cone_not_empty:
  assumes a: "(\<exists>x\<in>X. \<exists>T. T \<subseteq> powerset (X - {x}) \<and> K = T \<union> {s. \<exists>t\<in>T. s = insert x t})"
  shows "cone X K"
  unfolding cone_def
  using assms by blast

lemma cone_disjoint:
  assumes "cone X K" and "x \<in> X" and t: "T \<subseteq> powerset (X - {x})"
   and "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "T \<inter> {s. \<exists>t\<in>T. s = insert x t} = {}"
  using t unfolding powerset_def by auto

lemma cone_cost_eq_link:
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

text\<open>The following result does hold for @{term link_ext}, 
  but the proof is different than for @{term link} 
  because in general it does not hold that 
  @{term "link_ext x V K \<subseteq> cost x V K"}\<close>

lemma cone_impl_cost_eq_link_ext:
  assumes x: "x \<in> V"
    and cs: "T \<subseteq> powerset (V - {x})" 
    and kt: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "cost x V K = link_ext x V K"
proof
  show "link_ext x V K \<subseteq> cost x V K"
    using assms unfolding link_ext_def cost_def powerset_def
    by auto (metis Diff_insert_absorb PowD in_mono mk_disjoint_insert)
  show "cost x V K \<subseteq> link_ext x V K"
    unfolding kt
    unfolding cost_def link_ext_def powerset_def by auto
qed

lemma cost_eq_link_ext_impl_cone:
  assumes c: "cost x V K = link_ext x V K"
    and x: "x \<in> V" and p: "K \<subseteq> powerset V" and p1: "K \<noteq> {}"
  shows "cone V K"
proof (unfold cone_def)
  show "\<exists>x\<in>V. \<exists>T\<subseteq>powerset (V - {x}). K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  proof (rule bexI [OF _ x], rule exI [of _ "cost x V K"], rule conjI)
    show "cost x V K \<subseteq> powerset (V - {x})"
      using p unfolding cost_def powerset_def by auto
    show "K = cost x V K \<union> {s. \<exists>t\<in>cost x V K. s = insert x t}"
    proof
      show "cost x V K \<union> {s. \<exists>t\<in>cost x V K. s = insert x t} \<subseteq> K"
        using x p
        using c
        unfolding cost_def powerset_def link_ext_def by auto
      show "K \<subseteq> cost x V K \<union> {s. \<exists>t\<in>cost x V K. s = insert x t}" 
      proof (subst c, unfold cost_def link_ext_def powerset_def, rule)
        fix xa
        assume xa: "xa \<in> K"
        show "xa \<in> {s \<in> Pow V. x \<notin> s \<and> insert x s \<in> K} \<union>
                {s. \<exists>t\<in>{s \<in> Pow (V - {x}). s \<in> K}. s = insert x t}"
        proof (cases "x \<in> xa")
          case False
          then show ?thesis using xa c p 
            unfolding cost_def link_ext_def powerset_def by blast
        next
          case True
          have "xa - {x} \<in> {s \<in> Pow V. x \<notin> s \<and> insert x s \<in> K}"
            using xa p True unfolding powerset_def
            using mk_disjoint_insert by fastforce
          hence "xa - {x} \<in> {s \<in> Pow (V - {x}). s \<in> K}"
            using c unfolding cost_def link_ext_def powerset_def by simp
          hence "xa \<in> {s. \<exists>t\<in>{s \<in> Pow (V - {x}). s \<in> K}. s = insert x t}"
            using True by auto
          thus ?thesis by fast
        qed
      qed
    qed
  qed
qed

text\<open>Under the given premises, @{term cost} of a cone is a cone.\<close>

lemma cost_cone_eq:
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

text\<open>Under the given premises, @{term link_ext} of a cone is a cone.\<close>

lemma link_ext_cone_eq:
  assumes x: "x \<in> V" (*and y: "y \<in> V"*) and xy: "x \<noteq> y"
    and cs: "T \<subseteq> powerset (V - {x})" 
    and kt: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}"
  shows "link_ext y V K = (link_ext y (V - {x}) T) \<union> {s. \<exists>t\<in>(link_ext y (V - {x}) T). s = insert x t}"
proof
  show "link_ext y (V - {x}) T \<union> {s. \<exists>t\<in>link_ext y (V - {x}) T. s = insert x t} \<subseteq> link_ext y V K"
    unfolding kt link_ext_def powerset_def using x xy by auto
  show "link_ext y V K \<subseteq> link_ext y (V - {x}) T \<union> {s. \<exists>t\<in>link_ext y (V - {x}) T. s = insert x t}"
  unfolding link_ext_def [of y V K]
  unfolding link_ext_def [of y "V - {x}" T]
  proof
    fix xa
    assume "xa \<in> {s \<in> powerset V. y \<notin> s \<and> insert y s \<in> K}"
    hence xap: "xa \<in> powerset V" and xak: "y \<notin> xa" and iyxa: "insert y xa \<in> K" by auto
    show "xa \<in> {s \<in> powerset (V - {x}). y \<notin> s \<and> insert y s \<in> T} \<union>
                {s. \<exists>t\<in>{s \<in> powerset (V - {x}). y \<notin> s \<and> insert y s \<in> T}.
                       s = insert x t}"
    proof (cases "x \<in> xa")
      case False note xnxa = False
      hence xapxy: "xa \<in> powerset (V - {x})" using xap xy unfolding powerset_def by auto
      moreover have "y \<notin> xa" using xak .
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
      ultimately have "xa \<in> {s \<in> powerset (V - {x}). y \<notin> s \<and> insert y s \<in> T}"
        by auto
      thus ?thesis by fast
    next
      case True note xxa = True
      then obtain t where xai: "xa = insert x t" and xnt: "x \<notin> t" 
        using Set.set_insert [OF True] by auto
      have "t \<in> powerset (V - {x})" 
        using xap xai xnt unfolding powerset_def by auto
      moreover have t: "y \<notin> xa" using xak .
      moreover have "insert y t \<in> T"
      proof (cases "insert y xa \<in> T")
        case True then have False
          using cs xxa unfolding powerset_def by auto
        thus ?thesis by (rule ccontr)
      next
        case False
        with xai iyxa kt have "insert y xa \<in> {s. \<exists>t\<in>T. s = insert x t}" by simp
        with xai xap xnt kt show ?thesis
          unfolding powerset_def
          by auto (metis (full_types) Diff_insert_absorb False insert_absorb insert_commute insert_iff xak)
      qed
      ultimately show ?thesis using xai by auto
    qed
  qed
qed

text\<open>Even if it is not used in our later proofs,
  it also holds that @{term link} of a cone is a cone.\<close>

lemma link_cone_eq:
  assumes x: "x \<in> V" (*and y: "y \<in> V"*) and xy: "x \<noteq> y"
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
        then show ?thesis
          using xai xap xnt kt iyxa unfolding powerset_def
          by (smt (verit, del_insts) Diff_insert_absorb PowD UnE Un_insert_right insert_absorb insert_is_Un iyxa kt mem_Collect_eq powerset_def singletonD subset_Diff_insert xai xap xnt)
      qed
      ultimately show ?thesis using xai by auto
    qed
  qed
qed

lemma evaluation_cone_not_evaders:
  assumes k: "K \<subseteq> powerset X"
    and c: "cone X K" and X: "X \<noteq> {}" and f: "finite X" and xl: "(X, l) \<in> sorted_variables"
  shows "evaluation l K \<in> not_evaders"
  proof -
  from c and X obtain x :: nat and T :: "nat set set"
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
      using Suc.prems (1,4) unfolding cone_def by auto
    obtain y l' where l: "l = y # l'" and y: "y \<in> X"
      using Suc.prems Suc.hyps (2) sorted_variables_length_coherent [OF Suc.prems (3)]
      by (metis insert_iff sorted_variables.cases)
    show ?case
      unfolding l 
      unfolding evaluation.simps (3) 
      unfolding l [symmetric] 
      unfolding sorted_variables_coherent [OF Suc.prems (3), symmetric]
    proof (cases "x = y")
      case True
      have cl_eq: "cost x X K = link_ext x X K"
        by (rule cone_impl_cost_eq_link_ext [of x X T], rule x, rule cs, rule kt)
      show "evaluation l' (link_ext y X K) @ evaluation l' (cost y X K)
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
      have lrw: "link_ext y X K = link_ext y (X - {x}) T \<union> {s. \<exists>t\<in>link_ext y (X - {x}) T. s = insert x t}"
      proof (rule link_ext_cone_eq)
        show "x \<in> X" using x .
        show "x \<noteq> y" using False .
        show "T \<subseteq> powerset (X - {x})" using cs .
        show "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" using kt .
      qed
      show "evaluation l' (link_ext y X K) @ evaluation l' (cost y X K) \<in> not_evaders"
        unfolding crw lrw
      proof (rule not_evaders.intros(2))
        show "evaluation l' (link_ext y (X - {x}) T \<union> {s. \<exists>t\<in>link_ext y (X - {x}) T. s = insert x t}) \<in> not_evaders"
        proof (rule Suc.hyps (1) [of "X - {y}"])
          show "n = card (X - {y})" using Suc.hyps (2) y x False by simp
          show "X - {y} \<noteq> {}" using x False by auto
          show "finite (X - {y})" using Suc.prems (2) by simp
          show "(X - {y}, l') \<in> sorted_variables"
            using Suc.prems (3) using l y Suc.prems (1)
            by (metis Diff_insert_absorb list.inject sorted_variables.cases)
          show "cone (X - {y}) (link_ext y (X - {x}) T \<union> {s. \<exists>t\<in>link_ext y (X - {x}) T. s = insert x t})"
          proof (rule cone_not_empty, intro bexI [of _ x] exI [of _ "link_ext y (X - {x}) T"], rule conjI)
            show "link_ext y (X - {x}) T \<subseteq> powerset (X - {y} - {x})"
              unfolding link_ext_def powerset_def by auto
            show "link_ext y (X - {x}) T \<union> {s. \<exists>t\<in>link_ext y (X - {x}) T. s = insert x t} =
                  link_ext y (X - {x}) T \<union> {s. \<exists>t\<in>link_ext y (X - {x}) T. s = insert x t}" ..
            show "x \<in> X - {y}" using x False by simp
          qed
        qed
        show "evaluation l' (cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}) \<in> not_evaders"
        proof (rule Suc.hyps (1) [of "X - {y}"])
          show "n = card (X - {y})" using Suc.hyps (2) y x False by simp
          show "X - {y} \<noteq> {}" using x False by auto
          show "finite (X - {y})" using Suc.prems (2) by simp
          show "(X - {y}, l') \<in> sorted_variables"
            using Suc.prems (3) using l y Suc.prems (1)
            by (metis Diff_insert_absorb list.inject sorted_variables.cases)
          show "cone (X - {y}) (cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t})"
          proof (rule cone_not_empty, intro bexI [of _ x] exI [of _ "cost y (X - {x}) T"], rule conjI)
            show "cost y (X - {x}) T \<subseteq> powerset (X - {y} - {x})"
              unfolding cost_def powerset_def by auto
            show "cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t} =
                  cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}" ..
            show "x \<in> X - {y}" using x False by simp
          qed
        qed
        show "length (evaluation l' (link_ext y (X - {x}) T \<union> {s. \<exists>t\<in>link_ext y (X - {x}) T. s = insert x t})) =
              length (evaluation l' (cost y (X - {x}) T \<union> {s. \<exists>t\<in>cost y (X - {x}) T. s = insert x t}))"
          using length_evaluation_eq .
      qed
    qed
  qed
qed

lemma "link x {x} {{}, {x}} = {{}}"
  unfolding link_def powerset_def by auto

lemma cost_singleton2: "cost x {x} {{}, {x}} = {{}}" 
  unfolding cost_def powerset_def by auto

lemma
  evaluation_empty_set_not_evaders:
  assumes a: "l \<noteq> []"
  shows "evaluation l {} \<in> not_evaders"
proof -
  from a obtain x l' where xl: "l = x # l'"
    by (meson neq_Nil_conv)
  show ?thesis 
    unfolding xl unfolding evaluation.simps (3) 
    unfolding link_ext_empty cost_empty
    by (rule not_evaders.intros(1), rule refl)
qed

lemma finite_set_sorted_variables:
  assumes f: "finite X"
  shows "\<exists>l. (X, l) \<in> sorted_variables"
using f proof (induct "card X" arbitrary: X)
  case 0
  then have x: "X = {}" by simp
  show ?case unfolding x by (rule exI [of _ "[]"], rule sorted_variables.intros(1))
next
  case (Suc n)
  then obtain x X' 
    where X: "X = insert x X'" and cx': "card X' = n" 
      and f: "finite X'" and xx': "x \<notin> X'"
    by (metis card_Suc_eq_finite)
  from Suc.hyps (1) [OF cx'[symmetric] f] obtain l' where x'a': "(X', l') \<in> sorted_variables"
    by auto
  show ?case 
    by (unfold X, intro exI [of _ "x # l'"],
        intro sorted_variables.intros(2), intro x'a', intro xx')
qed

section\<open>Zero collapsible sets, based on @{term link_ext} and @{term cost}\<close>

function zero_collapsible :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> zero_collapsible V K = False"
  | "V = {x} \<Longrightarrow> K = {} \<Longrightarrow> zero_collapsible V K = True"
  | "V = {x} \<Longrightarrow> K = {{},{x}} \<Longrightarrow> zero_collapsible V K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> zero_collapsible V K = False"
  (*This can be proven from the definition: | "2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> nonevasive V K = True"*)
  | "2 \<le> card V \<Longrightarrow> zero_collapsible V K =
    (\<exists>x\<in>V. cone (V - {x}) (link_ext x V K) \<and> zero_collapsible (V - {x}) (cost x V K))"
  | "\<not> finite V \<Longrightarrow> zero_collapsible V K = False"
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
qed

(*function zero_collapsible :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> K = {{}} \<Longrightarrow> zero_collapsible V K = True"
  | "V = {} \<Longrightarrow> K \<noteq> {{}} \<Longrightarrow> zero_collapsible V K = False"
  | "V = {x} \<Longrightarrow> K = {} \<Longrightarrow> zero_collapsible V K = True"
  | "V = {x} \<Longrightarrow> K = {{},{x}} \<Longrightarrow> zero_collapsible V K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> zero_collapsible V K = False"
  | "2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> zero_collapsible V K = True"
  | "2 \<le> card V \<Longrightarrow> K \<noteq> {} \<Longrightarrow> zero_collapsible V K =
    (\<exists>x\<in>V. cone (V - {x}) (link_ext x V K) \<and> zero_collapsible (V - {x}) (cost x V K))"
  | "\<not> finite V \<Longrightarrow> zero_collapsible V K = False"
  unfolding link_ext_def cost_def
proof -
  fix P :: "bool" and x :: "(nat set \<times> nat set set)"
  assume ee: "(\<And>V K. V = {} \<Longrightarrow> K = {{}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and ene: "(\<And>V K. V = {} \<Longrightarrow> K \<noteq> {{}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)" 
      and se: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and sc: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)" 
      and sn: "(\<And>V xa K. V = {xa} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and e2: "(\<And>V K. 2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and en2: "(\<And>V K. 2 \<le> card V \<Longrightarrow> K \<noteq> {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
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
      show P
      proof (cases "snd x = {{}}")
        case True
        show P
          by (rule ee [of "fst x" "snd x"], intro ve, intro True) simp
      next
        case False
        show P
          by (rule ene [of "fst x" "snd x"], intro ve, intro False) simp
      qed
    next
      case False note vne = False
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
        show P
        proof (cases "snd x = {}")
          case True
          show P
            by (rule e2 [of "fst x" "snd x"], intro card2, intro True) simp
        next
          case False
          show P
            by (rule en2 [of "fst x" "snd x"], intro card2, intro False) simp
        qed
      qed
    qed
  qed
qed (auto)
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  show "wf (measure (\<lambda>(V, K). card V))" by simp
  fix V :: "nat set" and K :: "nat set set" and x :: "nat"
  assume c: "2 \<le> card V" and k: "K \<noteq> {}" and x: "x \<in> V"
  show "((V - {x}, cost x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c k x by simp
qed
*)

lemma shows "zero_collapsible {x} {}" by simp

lemma shows "\<not> zero_collapsible {x} {{}}" by simp

lemma "link_ext x {x} {{}, {x}} = {{}}"
  unfolding link_ext_def powerset_def by auto

lemma shows "zero_collapsible {x} {{}, {x}}" by simp

lemma v_ge_2: assumes two: "2 \<le> card V" shows "zero_collapsible V {}"
  using two proof (induct "card V" arbitrary: V)
  case 0
  fix V :: "nat set"
  assume "0 = card V" and "2 \<le> card V"
  hence False by linarith
  thus "zero_collapsible V {}" by fast
next
  case (Suc n)
  assume two: "2 \<le> card V"
  then obtain x where x: "x \<in> V" by fastforce
  have n: "zero_collapsible (V - {x}) {}"
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
    show ?thesis unfolding V using zero_collapsible.simps (2) by simp
  qed
  show "zero_collapsible V {}"
    unfolding zero_collapsible.simps (5) [OF two, of "{}"]
    using two link_ext_empty [of _ V] cone_empty [of V] n x
    by (metis cone_empty cost_empty zero_collapsible.simps(1))
qed

text\<open>There is always a valuation for which zero collapsible sets
 are not evasive.\<close>

theorem
  zero_collapsible_implies_not_evaders:
  assumes k: "K \<subseteq> powerset X"
    and x: "X \<noteq> {}" and f: "finite X" and cc: "zero_collapsible X K"
  shows "\<exists>l. (X, l) \<in> sorted_variables \<and> evaluation l K \<in> not_evaders"
using k x f cc proof (induct "card X" arbitrary: X K)
  case 0 with f have "X = {}" by simp
  with "0.prems" (2) have False by fast
  thus ?case by (rule ccontr)
next
  case (Suc n)
  show ?case
  proof (cases "K = {}")
    case True
    obtain l where xa: "(X, l) \<in> sorted_variables"
      using finite_set_sorted_variables [OF Suc.prems (3)] by auto
    show ?thesis
    proof (intro exI [of _ l], rule conjI)
      show "(X, l) \<in> sorted_variables" using xa .
      show "evaluation l K \<in> not_evaders"
      unfolding True
      using evaluation.simps (3)
      by (metis Suc.prems(2) empty_set evaluation_empty_set_not_evaders sorted_variables_coherent xa)
  qed
  next
    case False note kne = False
    show ?thesis
    proof (cases "card X = 1")
      case False
      hence cardx: "2 \<le> card X"
        using Suc.hyps(2) by linarith
      from Suc.prems (4) False Suc.prems (2)
      obtain x where x: "x \<in> X" and cl: "cone (X - {x}) (link_ext x X K)" 
        and ccc: "zero_collapsible (X - {x}) (cost x X K)" and xxne: "X - {x} \<noteq> {}"
        using zero_collapsible.simps (5) [OF cardx]
        by (metis One_nat_def Suc.prems(3) card.empty card_Suc_Diff1)
    have "\<exists>l. (X - {x}, l) \<in> sorted_variables \<and> evaluation l (cost x X K) \<in> not_evaders"
    proof (rule Suc.hyps (1))
      show "n = card (X - {x})" using x using Suc.hyps (2) by simp
      show "cost x X K \<subseteq> powerset (X - {x})" unfolding cost_def powerset_def by auto
      show "X - {x} \<noteq> {}"
        using False Suc.hyps (2) using cardx by (intro xxne)
      show "finite (X - {x})" using Suc.prems (3) by simp
      show "zero_collapsible (X - {x}) (cost x X K)" using ccc .
    qed
    then obtain l' where xxb: "(X - {x}, l') \<in> sorted_variables" 
      and ec: "evaluation l' (cost x X K) \<in> not_evaders" by auto
    from cl obtain y T where y: "y \<in> X - {x}" and t: "T \<subseteq> powerset (X - {x} - {y})" 
      and lc: "link_ext x X K = T \<union> {s. \<exists>t\<in>T. s = insert y t}" unfolding cone_def
      using x xxne by auto
    have el: "evaluation l' (link_ext x X K) \<in> not_evaders"
    proof (rule evaluation_cone_not_evaders)
      show "link_ext x X K \<subseteq> powerset (X - {x})" unfolding link_ext_def powerset_def by auto
      show "cone (X - {x}) (link_ext x X K)" using cl .
      show "X - {x} \<noteq> {}" using y by blast
      show "finite (X - {x})" using Suc.prems(3) by blast
      show "(X - {x}, l') \<in> sorted_variables" using xxb .
    qed
    show ?thesis
    proof (rule exI [of _ "x # l'"], rule conjI)
      show "(X, x # l') \<in> sorted_variables" using xxb x
        by (metis DiffE insert_Diff sorted_variables.intros(2) singletonI)
      show "evaluation (x # l') K \<in> not_evaders"
        unfolding evaluation.simps (3)
      proof (rule not_evaders.intros (2))
        show "evaluation l' (cost x (set (x # l')) K) \<in> not_evaders"
          using ec
          using \<open>(X, x # l') \<in> sorted_variables\<close> sorted_variables_coherent by blast
        show "length (evaluation l' (link_ext x (set (x # l')) K)) =
          length (evaluation l' (cost x (set (x # l')) K))" by (rule length_evaluation_eq)
        show "evaluation l' (link_ext x (set (x # l')) K) \<in> not_evaders"
          using el
          unfolding sorted_variables_coherent [OF \<open>(X, x # l') \<in> sorted_variables\<close>, symmetric]
          using evaluation.simps
          using el
          using \<open>(X, x # l') \<in> sorted_variables\<close> sorted_variables_coherent by blast
      qed
    qed
  next
    case True
    then obtain x where X: "X = {x}" by (rule card_1_singletonE)
    show "\<exists>l. (X, l) \<in> sorted_variables \<and> evaluation l K \<in> not_evaders"
    proof (unfold X, intro exI [of _ "[x]"], rule conjI)
      show "({x}, [x]) \<in> sorted_variables"
        by (simp add: sorted_variables.intros(1) sorted_variables.intros(2))
      show "evaluation [x] K \<in> not_evaders"
      proof -
        from kne and Suc.prems (1)
        have k_cases: "K = {{}} \<or> K = {{}, {x}} \<or> K = {{x}}"
          unfolding X powerset_def
          by (metis Suc.prems(1) X powerset_singleton_cases)
        show ?thesis
        proof (cases "K = {{}}")
          case True note kee = True
          have False
            using Suc.prems(4) unfolding True X by auto
          thus ?thesis by (rule ccontr)
        next
          case False note knee = False
          show ?thesis
          proof (cases "K = {{}, {x}}")
            case True note kex = True
            show ?thesis
              using Suc.prems (4)
              unfolding True X
              unfolding evaluation.simps link_ext_def cost_def powerset_def 
              using not_evaders.intros [of "[True]"] 
              by auto (metis (no_types, lifting) \<open>\<And>l2. [True] = l2 \<Longrightarrow> [True] @ l2 \<in> not_evaders\<close> bot.extremum empty_iff evaluation.simps(2) mem_Collect_eq)
          next
            case False
            have kx: "K = {{x}}" using False kne knee k_cases by simp
            have False 
              using Suc.prems(4) 
              unfolding X kx using zero_collapsible.simps (4) [of "{x}" x K] by simp
            thus ?thesis by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

end