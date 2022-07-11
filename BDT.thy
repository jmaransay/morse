
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
  using obdt_list.intros (2) [of "{}" "[]" "1"
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
  | "k \<subseteq> powerset A \<Longrightarrow> (A, k) \<in> cc"

lemma "({0}, {}) \<in> cc"
  by (rule cc.intros(2))

lemma "({0,1,2}, {}) \<in> cc" 
  by (rule cc.intros(5))

lemma "({0,1,2}, {{1,2}}) \<in> cc" 
  by (simp add: cc.intros(6) powerset_def)

lemma "({0,1,2}, {{1},{2}}) \<in> cc"
  by (simp add: cc.intros(6) powerset_def)

inductive_set cc_s :: "(nat set \<times> nat set set) set"
  where "({}, {}) \<in> cc_s"
  | "(A, {}) \<in> cc_s"
  | "k \<subseteq> powerset A \<Longrightarrow> (A, k) \<in> cc_s"

lemma "({0}, {}) \<in> cc_s" 
  by (rule cc_s.intros(2))

lemma "({0,1,2}, {}) \<in> cc_s" 
  by (rule cc_s.intros(2))

lemma "({0,1,2}, {{1,2}}) \<in> cc_s" 
  by (simp add: cc_s.intros(3) powerset_def)

lemma "({0,1,2}, {{1},{2}}) \<in> cc_s"
  by (simp add: cc_s.intros(3) powerset_def)

lemma cc_s_empty: "({}, A) \<in> cc_s \<Longrightarrow> A = {} \<or> A = {{}}"
  by (metis Diff_insert_absorb Pow_empty cc_s.cases empty_iff insert_absorb powerset_def singleton_insert_inj_eq')

definition link :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x V K = {s. s \<in> powerset (V - {x}) \<and> s \<union> {x} \<in> K}"

definition cost :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K}"

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

instantiation list :: (ord) ord  
begin

definition "less_eq l m \<equiv> (length l \<le> length m) \<and> (\<forall>i<length l. l!i \<le> m!i)"

definition "less l m \<equiv> (length l \<le> length m) \<and> (\<forall>i<length l. l!i < m!i)"

instance
proof

qed

lemma
  assumes "finite X" and "(X, K) \<in> cc_s" and "(X, L) \<in> cc_s" and "K \<subseteq> L"
   and "(X, l) \<in> obdt_list"
 shows "evaluation l K \<le> evaluation l L"
proof (cases "card X")
  case 0
  then have x: "X = {}" by (simp add: assms(1))
  hence l: "l = []" and k: "K = {} \<or> K = {{}}" and L: "L = {} \<or> L = {{}}"
    using assms (5)
    using obdt_list.cases cc_s_empty [of K] cc_s_empty [of L] x
    using assms (2) assms (3) by auto
  show ?thesis 
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