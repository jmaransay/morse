
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

inductive_set obdt_list :: "(nat list) set"
  where "[] \<in> obdt_list"
  | "A \<in> obdt_list \<Longrightarrow> x \<notin> set A \<Longrightarrow> Cons x A \<in> obdt_list"

lemma "[1] \<in> obdt_list"
  by (simp add: obdt_list.intros(1) obdt_list.intros(2))

lemma "[1,1] \<notin> obdt_list"
  by (metis list.distinct(1) list.sel(3) list.set_intros(1) nth_Cons_0 obdt_list.simps)

lemma "[6,2,3,4,5,1] \<in> obdt_list"
  by (simp add: obdt_list.intros(1) obdt_list.intros(2))

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

definition link :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "link x V K = {s. s \<in> powerset (V - {x}) \<and> s \<union> {x} \<in> K}"

definition cost :: "nat \<Rightarrow> nat set \<Rightarrow> nat set set \<Rightarrow> nat set set"
  where "cost x V K = {s. s \<in> powerset (V - {x}) \<and> s \<in> K}"


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