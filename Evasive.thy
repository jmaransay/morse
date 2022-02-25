
theory Evasive
  imports
    Bij_betw_simplicial_complex_bool_func
    MkIfex
    Alexander
begin

section\<open>Relation between type @{typ "bool vec => bool"} and type @{typ "'a boolfunc"}\<close>

definition vec_to_boolfunc :: "nat \<Rightarrow> (bool vec => bool) => (nat boolfunc)"
  where "vec_to_boolfunc n f = (\<lambda>i. f (vec n i))"

lemma
  ris: "reads_inside_set (\<lambda>i. bool_fun_threshold_2_3 (vec 4 i)) (set [0,1,2,3])"
  unfolding reads_inside_set_def
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding set_list_four [symmetric] by simp 

lemma
  shows "val_ifex (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0,1,2,3])
    = vec_to_boolfunc 4 bool_fun_threshold_2_3"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  unfolding vec_to_boolfunc_def
  using ris .

text\<open>For any Boolean function in dimension @{term n},
  its ifex representation is @{const ifex_ordered} and @{const ifex_minimal}.\<close>

lemma mk_ifex_boolean_function: 
  fixes f :: "bool vec => bool"
  shows "ro_ifex (mk_ifex (vec_to_boolfunc n f) [0..n])"
  using mk_ifex_ro by fast

text\<open>Any Boolean function in dimension @{term n} can be 
  seen as an expression over the underlying set of variables.\<close>

lemma
  reads_inside_set_boolean_function:
  fixes f :: "bool vec => bool"
  shows "reads_inside_set (vec_to_boolfunc n f) {..<n}"
  unfolding vec_to_boolfunc_def
  unfolding reads_inside_set_def
  by (smt (verit, best) dim_vec eq_vecI index_vec lessThan_iff)

text\<open>Any Boolean function of a finite dimension
  is equal to its ifex representation
  by means of @{const mk_ifex}.\<close>

lemma
  mk_ifex_equivalence:
  fixes f :: "bool vec => bool"
  shows "val_ifex (mk_ifex (vec_to_boolfunc n f) [0..n])
    = vec_to_boolfunc n f"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  using reads_inside_set_boolean_function [of n f]
  unfolding reads_inside_set_def by auto

(*definition bcount_true :: "nat => (nat=> bool) => nat"
  where "bcount_true n f =  (\<Sum>i = 0..<n. if f i then 1 else (0::nat))"

definition boolfunc_threshold_2_3 :: "(nat => bool) => bool"
  where "boolfunc_threshold_2_3 = (\<lambda>v. 2 \<le> bcount_true 4 v)"

definition proj_2 :: "(nat => bool) => bool"
  where "proj_2 = (\<lambda>v. v 2)"

definition proj_2_n3 :: "(nat => bool) => bool"
  where "proj_2_n3 = (\<lambda>v. v 2 \<and> \<not> v 3)"*)

definition proj_2_bool :: "bool vec \<Rightarrow> bool"
  where "proj_2_bool v = v $ 2"

definition proj_2_n3_bool :: "bool vec \<Rightarrow> bool"
  where "proj_2_n3_bool v = (v $ 2 \<and> \<not> v $ 3)"

text\<open>The following definition computes the height of an @{typ "'a ifex"} expression.\<close>

fun height :: "'a ifex => nat"
  where "height Trueif = 0"
  | "height Falseif = 0"
  | "height (IF v va vb) = 1 + max (height va) (height vb)"  

text\<open>The function @{term restrict_top} takes a @{typ "'a ifex"} 
  expression, a variable and a boolean. If the variable is at the
  top of the @{term IF} expression then it uses the boolean 
  value to produce the corresponding subexpression. Otherwise, 
  it keeps the original @{term IF} expression.\<close>

lemma restrict_height_le: "height (restrict_top k var val) \<le> height k"
  by (induction k, auto)

lemma restrict_height_less: 
  "ifex_top_var k = Some var \<Longrightarrow> height (restrict_top k var val) < height k"
  by (induction k, auto)

lemma restrict_height_some_less:
  "lowest_tops [i, t, e] = Some xa \<Longrightarrow>
  (height (restrict_top i xa val) + height (restrict_top t xa val) + height (restrict_top e xa val)) 
    < (height i + height t + height e)"
  using restrict_height_le[of i xa val] restrict_height_le[of t xa val] restrict_height_le[of e xa val]
  by (auto dest!: lowest_tops_cases restrict_height_less[of _ _ val])

(*lemma 
  "lowest_tops [i, t, e] = Some xa \<Longrightarrow> max (max (height (restrict_top i xa val)) (height (restrict_top t xa val))) (height (restrict_top e xa val))
  < max (max (height i) (height t)) (height e)"*)
  

text\<open>The @{term IFC} function takes as parameters a variable and two
   @{typ "'a ifex"} expressions. If the expressions are the same,
    then it returns either of them. Otherwise, it builds the
   @{term "IF"} expression with the variable and the
    two subtrees.\<close>

lemma height_IFC:
  "height (IFC v t e) \<le> max (height t) (height e) + 1"
  unfolding IFC_def by simp

text\<open>The @{term "ifex_ite"} function takes three \<close>

lemma 
  height_0:
  assumes "height t = 0"
  shows "t = Trueif \<or> t = Falseif"
  using assms height.elims by auto

lemma "rit < i \<Longrightarrow>
    rif < i \<Longrightarrow>
    rtt \<le> t \<Longrightarrow>
    rtf \<le> t \<Longrightarrow>
    ret \<le> e \<Longrightarrow>
    ref \<le> e \<Longrightarrow>
    Suc (max (max (max rit rtt) ret)
             (max (max rif rtf) ref))
    \<le> max (max i t) (e::nat)"

lemma height_ifex_ite:
  assumes n: "n = height i + height t + height e"
  shows "height (ifex_ite i t e) \<le> max (max (height i) (height t)) (height e) + 1"
using n proof (induct n arbitrary: i t e rule: less_induct)
  case (less n)
  then show ?case
  proof (cases "lowest_tops [i,t,e] = None")
    case True 
    from True have i: "i = Trueif \<or> i = Falseif"
      using lowest_tops.elims by auto
    from True have t: "t = Trueif \<or> t = Falseif"
      by (metis height.elims lowest_tops_NoneD three_ins(2))
    from True have e: "e = Trueif \<or> e = Falseif"
      by (metis (no_types, lifting) height.elims lowest_tops.simps(2) lowest_tops.simps(3) lowest_tops.simps(4) option.distinct(1))
    from i t e have hi: "height i = 0" and ht: "height t = 0" and he: "height e = 0"
        using height.simps by auto+
    show ?thesis
      unfolding ifex_ite.simps [of i t e] 
      unfolding True
      using i by force
  next
    case False
    then obtain x where some: "Some x = lowest_tops [i, t, e]" by auto
    have h_true: "height (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
      \<le> max (max (height (restrict_top i x True)) (height (restrict_top t x True))) 
        (height (restrict_top e x True)) + 1"
    proof (rule less.hyps [of "height (restrict_top i x True) 
        + height (restrict_top t x True) + height (restrict_top e x True)"], safe)
      show "height (restrict_top i x True) + height (restrict_top t x True) +
        height (restrict_top e x True) < n"
        by (subst less.prems) (simp add: some restrict_height_some_less)
    qed
    have h_false: "height (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False))
        \<le> max (max (height (restrict_top i x False)) (height (restrict_top t x False))) 
      (height (restrict_top e x False)) + 1"
    proof (rule less.hyps [of "height (restrict_top i x False) 
        + height (restrict_top t x False) + height (restrict_top e x False)"], safe)
      show " height (restrict_top i x False) + height (restrict_top t x False) +
        height (restrict_top e x False) < n"
        by (subst less.prems) (simp add: some restrict_height_some_less)
    qed
    have "height (ifex_ite i t e) = 
      height (IFC x (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
           (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False)))"
      unfolding ifex_ite.simps [of i t e] unfolding some [symmetric] by simp
    also have "height (IFC x (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
           (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False)))
        \<le> max
        (height (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True)))
        (height (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False)))
        + 1" using height_IFC by simp
    also have "... \<le> max
      (max (max (height (restrict_top i x True)) (height (restrict_top t x True))) 
        (height (restrict_top e x True)) + 1)
      (max (max (height (restrict_top i x False)) (height (restrict_top t x False))) 
      (height (restrict_top e x False)) + 1) 
      + 1" using h_true h_false by auto
    also have "...  \<le> max (max (height i) (height t)) (height e) + 1"
    proof -
      from lowest_tops_cases [OF some [symmetric]]
      have ifex: "ifex_top_var i = Some x \<or> ifex_top_var t = Some x \<or> ifex_top_var e = Some x"
        by simp
      show ?thesis
      proof (cases "ifex_top_var i = Some x")
        case True
        have hi: "\<And>b. height (restrict_top i x b) < height i" 
          using restrict_height_less[OF True] by simp
        show ?thesis
          using hi [of True] hi [of False]
          using restrict_height_le[of t x True] restrict_height_le[of t x False]
          using restrict_height_le[of e x True] restrict_height_le[of e x False] apply auto
          try
        have 
        thm lowest_tops_cases proof (cases lowest_tops_cases)
      using some
        using restrict_height_le[of i x True] restrict_height_le[of t x True] restrict_height_le[of e x True]
        using restrict_height_le[of i x False] restrict_height_le[of t x False] restrict_height_le[of e x False]
        using restrict_height_less[of _ _ True] restrict_height_less[of _ _ False]
        using lowest_tops_cases [OF some [symmetric]]
        apply (auto dest!: lowest_tops_cases restrict_height_less[of _ _ True] restrict_height_less[of _ _ False])
      try
    show ?thesis
      unfolding ifex_ite.simps [of i t e] 
      unfolding some [symmetric]
      
  qed
  show ?case
  case 0
  from 0 have i: "height i = 0" and t: "height t = 0" and e: "height e = 0" by simp_all
  then have "lowest_tops [i,t,e] = None" 
    using height_0
    by (metis (no_types, lifting) lowest_tops.simps(1) lowest_tops.simps(3) lowest_tops.simps(4)) 
  then show ?case unfolding ifex_ite.simps [of i t e] using height_IFC
    by (smt (verit, ccfv_threshold) i t e add.commute add.right_neutral height_0 ifex.simps(8) ifex.simps(9) max_0R option.simps(4) zero_less_one_class.zero_le_one)
next
  case (Suc n)
  
lemma height_ifex_ite:
  "height (ifex_ite i t e) \<le> max (max (height i) (height t)) (height e) + 1"
proof (induction i t e rule: ifex_ite_induct)
  case (Trueif i t e)
  then show ?case by simp
next
  case (Falseif i t e)
  then show ?case by simp
next
  case (IF i t e x)
  have ifex_rewr: "ifex_ite i t e = IFC x (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
           (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False))"
    by (subst ifex_ite.simps) (simp add: IF.hyps)
  have "height (ifex_ite i t e) \<le>
  height (IFC x (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True))
           (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False)))"
    unfolding ifex_rewr ..
  also have "... \<le> max 
            (height (ifex_ite (restrict_top i x True) (restrict_top t x True) (restrict_top e x True)))
            (height (ifex_ite (restrict_top i x False) (restrict_top t x False) (restrict_top e x False))) 
    + 1"
    using height_IFC by metis
  also have "... \<le> max 
      ( max (max (height (restrict_top i x True)) (height (restrict_top t x True)))
        (height (restrict_top e x True)) + 1 )
      ( max (max (height (restrict_top i x False)) (height (restrict_top t x False)))
        (height (restrict_top e x False)) + 1 )
    + 1" using IF.IH [of True] IF.IH [of False] by auto
  also have "... \<le> max (max (height i) (height t)) (height e) + 2"
    using height_restrict_top apply auto
    by (simp add: height_restrict_top le_max_iff_disj)+
  finally show ?case sorry
qed

lemma "height (mk_ifex f l) \<le> length l"
proof (induct l arbitrary: f)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  assume hyp: "(\<And>f. height (mk_ifex f l) \<le> length l)"
  have lt: "height (mk_ifex (bf_restrict a True f) l) \<le> length l"
       and lf: "height (mk_ifex (bf_restrict a False f) l) \<le> length l"
    using hyp [of "(bf_restrict a True f)"] and hyp [of "(bf_restrict a False f)"] .
  show ?case
  proof (subst mk_ifex.simps (2), subst ifex_ite.simps) thm ifex_ite.simps

  
  
    .      cases "lowest_tops
  .          [IF a Trueif Falseif, mk_ifex (bf_restrict a True f) l,
             mk_ifex (bf_restrict a False f) l]")
    case None
    then show "height
     (case lowest_tops
            [IF a Trueif Falseif, mk_ifex (bf_restrict a True f) l,
             mk_ifex (bf_restrict a False f) l] of
      None \<Rightarrow>
        case IF a Trueif Falseif of Trueif \<Rightarrow> mk_ifex (bf_restrict a True f) l
        | Falseif \<Rightarrow> mk_ifex (bf_restrict a False f) l
      | Some x \<Rightarrow>
          IFC x
           (ifex_ite (restrict_top (IF a Trueif Falseif) x True)
             (restrict_top (mk_ifex (bf_restrict a True f) l) x True)
             (restrict_top (mk_ifex (bf_restrict a False f) l) x True))
           (ifex_ite (restrict_top (IF a Trueif Falseif) x False)
             (restrict_top (mk_ifex (bf_restrict a True f) l) x False)
             (restrict_top (mk_ifex (bf_restrict a False f) l) x False)))
    \<le> length (a # l)" 
      using lt lf
      by (metis None lowest_tops.simps(2) option.discI)
  next
    case (Some x)
    show "lowest_tops
           [IF a Trueif Falseif, mk_ifex (bf_restrict a True f) l,
            mk_ifex (bf_restrict a False f) l] =
          Some x \<Longrightarrow>
          height
           (case lowest_tops
                  [IF a Trueif Falseif, mk_ifex (bf_restrict a True f) l,
                   mk_ifex (bf_restrict a False f) l] of
            None \<Rightarrow>
              case IF a Trueif Falseif of Trueif \<Rightarrow> mk_ifex (bf_restrict a True f) l
              | Falseif \<Rightarrow> mk_ifex (bf_restrict a False f) l
            | Some x \<Rightarrow>
                IFC x
                 (ifex_ite (restrict_top (IF a Trueif Falseif) x True)
                   (restrict_top (mk_ifex (bf_restrict a True f) l) x True)
                   (restrict_top (mk_ifex (bf_restrict a False f) l) x True))
                 (ifex_ite (restrict_top (IF a Trueif Falseif) x False)
                   (restrict_top (mk_ifex (bf_restrict a True f) l) x False)
                   (restrict_top (mk_ifex (bf_restrict a False f) l) x False)))
          \<le> length (a # l)" using Some using lf lt height_ifex_ite height_IFC 
      apply auto try
  qed
    case None
    then show ?thesis
  proof (induct ifex_ite_induct) try
    using lt lf
    using ifex_ite.simps apply auto try
    sorry
qed

text\<open>Both @{term mk_ifex} and @{term height} can be used in computations.\<close>

definition example :: "bool vec \<Rightarrow> bool"
  where "example v = ((v $ 1 \<and> v $ 2) \<or> (\<not> (v $ 1) \<and> v $ 3))"

value "height (mk_ifex (vec_to_boolfunc 4 example) [0..3])"

value "size (mk_ifex (vec_to_boolfunc 4 example) [0..3])"

value "(mk_ifex (vec_to_boolfunc 4 example) [0..3])"

value "size (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0..4])"

value "mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0..4]"

lemma "height (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0..4]) = 4"
  by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 
        (boolean_functions.Alexander_dual bool_fun_threshold_2_3)) [0..4]) = 4"
  by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0..4]) = 
  height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual bool_fun_threshold_2_3)) [0..4])"
  by eval

(*lemma "height (mk_ifex (boolfunc_threshold_2_3) [0,1,2,3]) = 4"
  by eval

lemma "height (mk_ifex (proj_2) [0,1,2,3]) = 1"
  by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0,1,2,3]) = 1"
  by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 
  (boolean_functions.Alexander_dual proj_2_bool)) [0,1,2,3]) = 1"
  by eval

(*lemma "mk_ifex (proj_2) [0] = Falseif" by eval*)

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0] = Falseif" by eval

lemma "mk_ifex (vec_to_boolfunc 4 
        (boolean_functions.Alexander_dual proj_2_bool)) [0] = Falseif" 
  by eval

(*lemma "height (mk_ifex (proj_2) [0]) = 0" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0]) = 0" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 
      (boolean_functions.Alexander_dual proj_2_bool)) [0]) = 0" 
  by eval

(*lemma "mk_ifex (proj_2) [3,2,1,0] = IF 2 Trueif Falseif"
  by eval*)

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_bool) [3,2,1,0] = IF 2 Trueif Falseif"
  by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_bool)) [3,2,1,0] 
  = IF 2 Trueif Falseif"
  by eval

(*lemma "mk_ifex (proj_2) [0,1,2,3] = IF 2 Trueif Falseif"
  by eval*)

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0,1,2,3] = IF 2 Trueif Falseif"
  by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_bool)) [0,1,2,3] 
  = IF 2 Trueif Falseif"
  by eval

(*lemma "height (mk_ifex (proj_2) [0,1,2,3]) = 1" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0,1,2,3]) = 1" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_bool)) 
        [0,1,2,3]) = 1" by eval

(*lemma "mk_ifex (proj_2_n3) [0,1,2,3] = IF 2 (IF 3 Falseif Trueif) Falseif" by eval*)

text\<open>Here the @{typ "nat ifex"} obtained is different for 
  @{term "boolean_functions.Alexander_dual proj_2_n3_bool"}
  and @{term "proj_2_n3_bool"}. In some sense, they are "dual"\<close>

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_n3_bool) [0,1,2,3] 
    = IF 2 (IF 3 Falseif Trueif) Falseif"
   by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_n3_bool)) [0,1,2,3]
    = IF 2 Trueif (IF 3 Falseif Trueif)"
   by eval

(*lemma "mk_ifex (bf_False::nat boolfunc) [0,1,2,3] = Falseif" by eval*)

text\<open>Here the @{typ "nat ifex"} obtained is different for 
  @{term "boolean_functions.Alexander_dual (\<lambda>x. False)"}
  and @{term "(\<lambda>x. False)"}. In some sense, they are "dual"\<close>

lemma "mk_ifex (vec_to_boolfunc 4 (\<lambda>x. False)) [0,1,2,3] = Falseif" by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. False)))
  [0,1,2,3] = Trueif" 
  by eval

(*lemma "height (mk_ifex (bf_False::nat boolfunc) [0,1,2,3]) = 0" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 (\<lambda>x. False)) [0,1,2,3]) = 0" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. False))) 
  [0,1,2,3]) = 0"
  by eval

(*lemma "mk_ifex (bf_True::nat boolfunc) [0,1,2,3] = Trueif" by eval*)

text\<open>Here the @{typ "nat ifex"} obtained is different for 
  @{term "boolean_functions.Alexander_dual (\<lambda>x. False)"}
  and @{term "(\<lambda>x. False)"}. In some sense, they are "dual"\<close>

lemma "mk_ifex (vec_to_boolfunc 4 (\<lambda>x. True)) [0,1,2,3] = Trueif" by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. True)))
  [0,1,2,3] = Falseif"
  by eval

(*lemma "height (mk_ifex (bf_True::nat boolfunc) [0,1,2,3]) = 0" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 (\<lambda>x. True)) [0,1,2,3]) = 0" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. True))) 
  [0,1,2,3]) = 0"
  by eval

section\<open>Definition of \emph{evasive} Boolean function\<close>

text\<open>Now we introduce the definition of evasive Boolean function. 
  It is based on the height of the ifex expression of the given function.
  The definition is inspired by the one by Scoville~\cite[Ex. 6.19]{SC19}.\<close>

definition evasive :: "nat => (bool vec => bool) => bool"
  where "evasive n f \<equiv> (height (mk_ifex (vec_to_boolfunc n f) [0..n])) = n"


(*definition evasive :: "nat => ((nat => bool) => bool) => bool"
  where "evasive n f \<equiv> (height (mk_ifex f [0..n])) = n"*)

(*corollary "evasive 4 boolfunc_threshold_2_3" by eval*)

lemma "evasive 4 (bool_fun_threshold_2_3)"
  by eval

lemma "evasive 4 (boolean_functions.Alexander_dual bool_fun_threshold_2_3)"
  by eval

(*lemma "\<not> evasive 4 proj_2" by eval*)

lemma "\<not> evasive 4 proj_2_bool" by eval

(*lemma "\<not> evasive 4 proj_2_n3" by eval*)

lemma "\<not> evasive 4 proj_2_n3_bool" by eval

lemma "\<not> evasive 4 bf_True" by eval

lemma "\<not> evasive 4 bf_False" by eval

section\<open>The @{term boolean_functions.Alexander_dual} and @{typ "'a ifex"}\<close>

context boolean_functions
begin

(*lemma 
  assumes "monotone_bool_fun f"
  shows "mk_ifex (vec_to_boolfunc n f) [0..n] 
        = mk_ifex (vec_to_boolfunc n (Alexander_dual f)) [0..n]"
  sorry*)

end

end