
section \<open>Finite types as explicit enumerations\<close>

theory Enum_mod
  imports Main
begin

subsection \<open>Small finite types as arithmetic modulo its cardinal\<close>

text \<open>Similar types are defined as @{term finite_1} up to @{term finite_5} in Enum.thy
  in the Isabelle distribution, but they define the binary minus 
  (see Enum.thy in the HOL folder of the Isabelle distribution) 
  not modulo the cardinal of the Universe set, but as in a lattice. 
  They are neither proven to be instances of linear order, but lattices.\<close>

datatype (plugins only: code "quickcheck" extraction) finite_mod_1 =
  a\<^sub>0

notation (output) a\<^sub>0  ("a\<^sub>0")

lemma UNIV_finite_mod_1:
  "UNIV = {a\<^sub>0}"
  by (auto intro: finite_mod_1.exhaust)

instantiation finite_mod_1 :: enum
begin

definition enum_finite_mod_1 :: "finite_mod_1 list"
  where "enum_finite_mod_1 = [a\<^sub>0]"

definition enum_all_finite_mod_1 :: "(finite_mod_1 \<Rightarrow> bool) \<Rightarrow> bool"
  where "enum_all_finite_mod_1 P = P a\<^sub>0"

definition enum_ex_finite_mod_1 :: "(finite_mod_1 \<Rightarrow> bool) \<Rightarrow> bool"
  where "enum_ex_finite_mod_1 P = P a\<^sub>0"

instance proof (intro_classes)
qed (simp_all only: enum_finite_mod_1_def enum_all_finite_mod_1_def enum_ex_finite_mod_1_def UNIV_finite_mod_1, simp_all)

end

instantiation finite_mod_1 :: linorder
begin

definition less_finite_mod_1 :: "finite_mod_1 \<Rightarrow> finite_mod_1 \<Rightarrow> bool"
where
  "x < (y :: finite_mod_1) \<longleftrightarrow> False"

definition less_eq_finite_mod_1 :: "finite_mod_1 \<Rightarrow> finite_mod_1 \<Rightarrow> bool"
where
  "x \<le> (y :: finite_mod_1) \<longleftrightarrow> True"

instance
apply (intro_classes)
apply (auto simp add: less_finite_mod_1_def less_eq_finite_mod_1_def)
apply (metis (full_types) finite_mod_1.exhaust)
done

end

instance finite_mod_1 :: "{dense_linorder, wellorder}"
by intro_classes (simp_all add: less_finite_mod_1_def)

instantiation finite_mod_1 :: complete_lattice
begin

definition [simp]: "Inf = (\<lambda>_. a\<^sub>0)"
definition [simp]: "Sup = (\<lambda>_. a\<^sub>0)"
definition [simp]: "bot = a\<^sub>0"
definition [simp]: "top = a\<^sub>0"
definition [simp]: "inf = (\<lambda>_ _. a\<^sub>0)"
definition [simp]: "sup = (\<lambda>_ _. a\<^sub>0)"

instance by intro_classes(simp_all add: less_eq_finite_mod_1_def)
end

instance finite_mod_1 :: complete_distrib_lattice
  by standard simp_all

instance finite_mod_1 :: complete_linorder ..

lemma finite_mod_1_eq: "x = a\<^sub>0"
by(cases x) simp

simproc_setup finite_mod_1_eq ("x::finite_mod_1") = \<open>
  fn _ => fn _ => fn ct =>
    (case Thm.term_of ct of
      Const (\<^const_name>\<open>a\<^sub>0\<close>, _) => NONE
    | _ => SOME (mk_meta_eq @{thm finite_mod_1_eq}))
\<close>

instantiation finite_mod_1 :: complete_boolean_algebra
begin
definition [simp]: "(-) = (\<lambda>_ _. a\<^sub>0)"
definition [simp]: "uminus = (\<lambda>_. a\<^sub>0)"
instance by intro_classes simp_all
end

instantiation finite_mod_1 ::
  "{linordered_ring_strict, linordered_comm_semiring_strict, ordered_comm_ring,
    ordered_cancel_comm_monoid_diff, comm_monoid_mult, ordered_ring_abs,
    one, modulo, sgn, inverse}"
begin
definition [simp]: "Groups.zero = a\<^sub>0"
definition [simp]: "Groups.one = a\<^sub>0"
definition [simp]: "(+) = (\<lambda>_ _. a\<^sub>0)"
definition [simp]: "(*) = (\<lambda>_ _. a\<^sub>0)"
definition [simp]: "(mod) = (\<lambda>_ _. a\<^sub>0)" 
definition [simp]: "abs = (\<lambda>_. a\<^sub>0)"
definition [simp]: "sgn = (\<lambda>_. a\<^sub>0)"
definition [simp]: "inverse = (\<lambda>_. a\<^sub>0)"
definition [simp]: "divide = (\<lambda>_ _. a\<^sub>0)"

instance by intro_classes (simp_all add: less_finite_1_def)
end

declare [[simproc del: finite_mod_1_eq]]
hide_const (open) a\<^sub>0

datatype (plugins only: code "quickcheck" extraction) finite_mod_2 =
  a\<^sub>0 | a\<^sub>1

notation (output) a\<^sub>0  ("a\<^sub>0")
notation (output) a\<^sub>1  ("a\<^sub>1")

lemma UNIV_finite_mod_2:
  "UNIV = {a\<^sub>0, a\<^sub>1}"
  by (auto intro: finite_mod_2.exhaust)

instantiation finite_mod_2 :: enum
begin

definition
  "enum_finite_mod_2 = [a\<^sub>0, a\<^sub>1]"

definition
  "enum_all_finite_mod_2 P \<longleftrightarrow> P a\<^sub>0 \<and> P a\<^sub>1"

definition
  "enum_ex_finite_mod_2 P \<longleftrightarrow> P a\<^sub>0 \<or> P a\<^sub>1"

instance proof
qed (simp_all only: enum_finite_mod_2_def enum_all_finite_mod_2_def enum_ex_finite_mod_2_def UNIV_finite_mod_2, simp_all)

end

instantiation finite_mod_2 :: linorder
begin

definition less_finite_mod_2 :: "finite_mod_2 \<Rightarrow> finite_mod_2 \<Rightarrow> bool"
where
  "x < y \<longleftrightarrow> x = a\<^sub>0 \<and> y = a\<^sub>1"

definition less_eq_finite_mod_2 :: "finite_mod_2 \<Rightarrow> finite_mod_2 \<Rightarrow> bool"
where
  "x \<le> y \<longleftrightarrow> x = y \<or> x < (y :: finite_mod_2)"

instance
apply (intro_classes)
apply (auto simp add: less_finite_mod_2_def less_eq_finite_mod_2_def)
apply (metis finite_mod_2.nchotomy)+
done

end

instance finite_mod_2 :: wellorder
by(rule wf_wellorderI)(simp add: less_finite_mod_2_def, intro_classes)

instantiation finite_mod_2 :: complete_lattice
begin

definition "Inf_finite_mod_2 A = (if a\<^sub>0 \<in> A then a\<^sub>0 else a\<^sub>1)"
definition "Sup_finite_mod_2 A = (if a\<^sub>1 \<in> A then a\<^sub>1 else a\<^sub>0)"
definition [simp]: "bot = a\<^sub>0"
definition [simp]: "top = a\<^sub>1"
definition "sup_finite_mod_2 x y = (if x = a\<^sub>1 \<or> y = a\<^sub>1 then a\<^sub>1 else a\<^sub>0)"
definition "inf_finite_mod_2 x y = (if x = a\<^sub>0 \<or> y = a\<^sub>0 then a\<^sub>0 else a\<^sub>1)"

lemma neq_finite_mod_2_a\<^sub>1_iff [simp]: "x \<noteq> a\<^sub>0 \<longleftrightarrow> x = a\<^sub>1"
by(cases x) simp_all

lemma neq_finite_mod_2_a\<^sub>1_iff' [simp]: "a\<^sub>0 \<noteq> x \<longleftrightarrow> x = a\<^sub>1"
by(cases x) simp_all

lemma neq_finite_mod_2_a\<^sub>2_iff [simp]: "x \<noteq> a\<^sub>1 \<longleftrightarrow> x = a\<^sub>0"
by(cases x) simp_all

lemma neq_finite_mod_2_a\<^sub>2_iff' [simp]: "a\<^sub>1 \<noteq> x \<longleftrightarrow> x = a\<^sub>0"
by(cases x) simp_all

instance
  apply (intro_classes)
  apply (auto simp add: less_eq_finite_mod_2_def less_finite_mod_2_def 
      inf_finite_mod_2_def sup_finite_mod_2_def Inf_finite_mod_2_def Sup_finite_mod_2_def finite_mod_2.exhaust)+
  by (metis finite_mod_2.exhaust)+
end

instance finite_mod_2 :: complete_linorder ..

instance finite_mod_2 :: complete_distrib_lattice ..

instantiation finite_mod_2 :: "{field, idom_abs_sgn, idom_modulo}" begin
definition [simp]: "0 = a\<^sub>0"
definition [simp]: "1 = a\<^sub>1"
definition "x + y = (case (x, y) of (a\<^sub>0, a\<^sub>0) \<Rightarrow> a\<^sub>0 | (a\<^sub>1, a\<^sub>1) \<Rightarrow> a\<^sub>0 | _ \<Rightarrow> a\<^sub>1)"
definition "uminus = (\<lambda>x :: finite_mod_2. x)"
definition "(-) = ((+) :: finite_mod_2 \<Rightarrow> _)"
definition "x * y = (case (x, y) of (a\<^sub>1, a\<^sub>1) \<Rightarrow> a\<^sub>1 | _ \<Rightarrow> a\<^sub>0)"
definition "inverse = (\<lambda>x :: finite_mod_2. x)"
definition "divide = ((*) :: finite_mod_2 \<Rightarrow> _)"
definition "x mod y = (case (x, y) of (a\<^sub>1, a\<^sub>0) \<Rightarrow> a\<^sub>1 | _ \<Rightarrow> a\<^sub>0)"
definition "abs = (\<lambda>x :: finite_mod_2. x)"
definition "sgn = (\<lambda>x :: finite_mod_2. x)"
instance
  by standard
    (subproofs
      \<open>simp_all add: plus_finite_mod_2_def uminus_finite_mod_2_def minus_finite_mod_2_def
        times_finite_mod_2_def
        inverse_finite_mod_2_def divide_finite_mod_2_def modulo_finite_mod_2_def
        abs_finite_mod_2_def sgn_finite_mod_2_def
        split: finite_mod_2.splits\<close>)
end

hide_const (open) a\<^sub>0 a\<^sub>1

datatype (plugins only: code "quickcheck" extraction) finite_mod_3 =
  a\<^sub>0 | a\<^sub>1 | a\<^sub>2

notation (output) a\<^sub>0  ("a\<^sub>0")
notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")

lemma UNIV_finite_mod_3:
  "UNIV = {a\<^sub>0, a\<^sub>1, a\<^sub>2}"
  by (auto intro: finite_mod_3.exhaust)

instantiation finite_mod_3 :: enum
begin

definition
  "enum_finite_mod_3 = [a\<^sub>0, a\<^sub>1, a\<^sub>2]"

definition
  "enum_all_finite_mod_3 P \<longleftrightarrow> P a\<^sub>0 \<and> P a\<^sub>1 \<and> P a\<^sub>2"

definition
  "enum_ex_finite_mod_3 P \<longleftrightarrow> P a\<^sub>0 \<or> P a\<^sub>1 \<or> P a\<^sub>2"

instance proof
qed (simp_all only: enum_finite_mod_3_def enum_all_finite_mod_3_def enum_ex_finite_mod_3_def UNIV_finite_mod_3, simp_all)

end

lemma finite_mod_3_not_eq_unfold:
  "x \<noteq> a\<^sub>0 \<longleftrightarrow> x \<in> {a\<^sub>1, a\<^sub>2}"
  "x \<noteq> a\<^sub>1 \<longleftrightarrow> x \<in> {a\<^sub>0, a\<^sub>2}"
  "x \<noteq> a\<^sub>2 \<longleftrightarrow> x \<in> {a\<^sub>0, a\<^sub>1}"
  by (cases x; simp)+

instantiation finite_mod_3 :: linorder
begin

definition less_finite_mod_3 :: "finite_mod_3 \<Rightarrow> finite_mod_3 \<Rightarrow> bool"
where
  "x < y = (case x of a\<^sub>0 \<Rightarrow> y \<noteq> a\<^sub>0 | a\<^sub>1 \<Rightarrow> y = a\<^sub>2 | a\<^sub>2 \<Rightarrow> False)"

definition less_eq_finite_mod_3 :: "finite_mod_3 \<Rightarrow> finite_mod_3 \<Rightarrow> bool"
where
  "x \<le> y \<longleftrightarrow> x = y \<or> x < (y :: finite_mod_3)"

instance proof (intro_classes)
qed (auto simp add: less_finite_mod_3_def less_eq_finite_mod_3_def split: finite_mod_3.split_asm)

end

instance finite_mod_3 :: wellorder
proof(rule wf_wellorderI)
  have "inv_image less_than (case_finite_mod_3 0 1 2) = {(x, y). x < y}"
    by(auto simp add: less_finite_mod_3_def split: finite_mod_3.splits)
  from this[symmetric] show "wf \<dots>" by simp
qed intro_classes

instantiation finite_mod_3 :: "{field, idom_abs_sgn, idom_modulo}" begin
definition [simp]: "0 = a\<^sub>0"
definition [simp]: "1 = a\<^sub>1"
definition
  "x + y = (case (x, y) of
     (a\<^sub>0, a\<^sub>0) \<Rightarrow> a\<^sub>0 | (a\<^sub>1, a\<^sub>2) \<Rightarrow> a\<^sub>0 | (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>0
   | (a\<^sub>0, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>1, a\<^sub>0) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>1
   | _ \<Rightarrow> a\<^sub>2)"
definition "- x = (case x of a\<^sub>0 \<Rightarrow> a\<^sub>0 | a\<^sub>1 \<Rightarrow> a\<^sub>2 | a\<^sub>2 \<Rightarrow> a\<^sub>1)"
definition "x - y = x + (- y :: finite_mod_3)"
definition "x * y = (case (x, y) of (a\<^sub>1, a\<^sub>1) \<Rightarrow> a\<^sub>1 | (a\<^sub>2, a\<^sub>2) \<Rightarrow> a\<^sub>1 | (a\<^sub>1, a\<^sub>2) \<Rightarrow> a\<^sub>2 | (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> a\<^sub>0)"
definition "inverse = (\<lambda>x :: finite_mod_3. x)" 
definition "x div y = x * inverse (y :: finite_mod_3)"
definition "x mod y = (case y of a\<^sub>0 \<Rightarrow> x | _ \<Rightarrow> a\<^sub>0)"
definition "abs = (\<lambda>x. case x of a\<^sub>2 \<Rightarrow> a\<^sub>1 | _ \<Rightarrow> x)"
definition "sgn = (\<lambda>x :: finite_mod_3. x)"
instance
  by standard
    (subproofs
      \<open>simp_all add: plus_finite_mod_3_def uminus_finite_mod_3_def minus_finite_mod_3_def
        times_finite_mod_3_def
        inverse_finite_mod_3_def divide_finite_mod_3_def modulo_finite_mod_3_def
        abs_finite_mod_3_def sgn_finite_mod_3_def
        less_finite_mod_3_def
        split: finite_mod_3.splits\<close>)
end

hide_const (open) a\<^sub>0 a\<^sub>1 a\<^sub>2

datatype (plugins only: code "quickcheck" extraction) finite_mod_4 =
  a\<^sub>0 | a\<^sub>1 | a\<^sub>2 | a\<^sub>3

notation (output) a\<^sub>0  ("a\<^sub>0")
notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")
notation (output) a\<^sub>3  ("a\<^sub>3")

lemma UNIV_finite_mod_4:
  "UNIV = {a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3}"
  by (auto intro: finite_mod_4.exhaust)

instantiation finite_mod_4 :: enum
begin

definition
  "enum_finite_mod_4 = [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]"

definition
  "enum_all_finite_mod_4 P \<longleftrightarrow> P a\<^sub>0 \<and> P a\<^sub>1 \<and> P a\<^sub>2 \<and> P a\<^sub>3"

definition
  "enum_ex_finite_mod_4 P \<longleftrightarrow> P a\<^sub>0 \<or> P a\<^sub>1 \<or> P a\<^sub>2 \<or> P a\<^sub>3"

instance proof
qed (simp_all only: enum_finite_mod_4_def enum_all_finite_mod_4_def enum_ex_finite_mod_4_def UNIV_finite_mod_4, simp_all)

end

instantiation finite_mod_4 :: linorder
begin

definition
  "x < y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, a\<^sub>0) \<Rightarrow> False | (a\<^sub>0, _) \<Rightarrow> True
   |  (a\<^sub>1, a\<^sub>2) \<Rightarrow> True |  (a\<^sub>1, a\<^sub>3) \<Rightarrow> True
   |  (a\<^sub>2, a\<^sub>3) \<Rightarrow> True  | _ \<Rightarrow> False)"

definition
  "x \<le> y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, _) \<Rightarrow> True
   | (a\<^sub>1, a\<^sub>1) \<Rightarrow> True | (a\<^sub>1, a\<^sub>2) \<Rightarrow> True | (a\<^sub>1, a\<^sub>3) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>2) \<Rightarrow> True | (a\<^sub>2, a\<^sub>3) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>3) \<Rightarrow> True | _ \<Rightarrow> False)"

instance proof (intro_classes)
  fix x::finite_mod_4
  show refl: "x \<le> x" unfolding less_eq_finite_mod_4_def
    by (metis (no_types, lifting) case_prodI finite_mod_4.case(1) finite_mod_4.exhaust finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16))
  fix y::finite_mod_4
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_finite_mod_4_def
    by (smt (z3) case_prodD finite_mod_4.case(1) finite_mod_4.exhaust finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16))
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_finite_mod_4_def 
    apply (cases "x", cases "y")
    apply simp_all
      by (metis finite_mod_4.exhaust finite_mod_4.simps(13) finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16))+
  fix z::finite_mod_4
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_finite_mod_4_def
    apply (cases "x", cases "y", cases "z") 
    apply simp_all 
    by (metis finite_mod_4.exhaust finite_mod_4.simps(13) finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16))+
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_eq_finite_mod_4_def less_finite_mod_4_def
    apply (cases "x", cases "y") apply simp_all
    by (metis (full_types) finite_mod_4.exhaust finite_mod_4.simps(13) finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16))+
qed    

end

hide_const (open) a\<^sub>0 a\<^sub>1 a\<^sub>2 a\<^sub>3

datatype (plugins only: code "quickcheck" extraction) finite_mod_5 =
  a\<^sub>0 | a\<^sub>1 | a\<^sub>2 | a\<^sub>3 | a\<^sub>4

notation (output) a\<^sub>0  ("a\<^sub>0")
notation (output) a\<^sub>1  ("a\<^sub>1")
notation (output) a\<^sub>2  ("a\<^sub>2")
notation (output) a\<^sub>3  ("a\<^sub>3")
notation (output) a\<^sub>4  ("a\<^sub>4")

lemma UNIV_finite_mod_5:
  "UNIV = {a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3, a\<^sub>4}"
  by (auto intro: finite_mod_5.exhaust)

instantiation finite_mod_5 :: enum
begin

definition
  "enum_finite_mod_5 = [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3, a\<^sub>4]"

definition
  "enum_all_finite_mod_5 P \<longleftrightarrow> P a\<^sub>0 \<and> P a\<^sub>1 \<and> P a\<^sub>2 \<and> P a\<^sub>3 \<and> P a\<^sub>4"

definition
  "enum_ex_finite_mod_5 P \<longleftrightarrow> P a\<^sub>0 \<or> P a\<^sub>1 \<or> P a\<^sub>2 \<or> P a\<^sub>3 \<or> P a\<^sub>4"

instance proof
qed (simp_all only: enum_finite_mod_5_def enum_all_finite_mod_5_def enum_ex_finite_mod_5_def UNIV_finite_mod_5, simp_all)

end

instantiation finite_mod_5 :: linorder
begin

definition
  "x < y \<longleftrightarrow> (case (x, y) of
      (a\<^sub>0, a\<^sub>1) \<Rightarrow> True | (a\<^sub>0, a\<^sub>2) \<Rightarrow> True | (a\<^sub>0, a\<^sub>3) \<Rightarrow> True | (a\<^sub>0, a\<^sub>4) \<Rightarrow> True
   |  (a\<^sub>1, a\<^sub>2) \<Rightarrow> True | (a\<^sub>1, a\<^sub>3) \<Rightarrow> True | (a\<^sub>1, a\<^sub>4) \<Rightarrow> True
   |  (a\<^sub>2, a\<^sub>3) \<Rightarrow> True | (a\<^sub>2, a\<^sub>4) \<Rightarrow> True
   |  (a\<^sub>3, a\<^sub>4) \<Rightarrow> True
   | _ \<Rightarrow> False)"

definition
  "x \<le> y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, _) \<Rightarrow> True
   | (a\<^sub>1, a\<^sub>1) \<Rightarrow> True | (a\<^sub>1, a\<^sub>2) \<Rightarrow> True | (a\<^sub>1, a\<^sub>3) \<Rightarrow> True | (a\<^sub>1, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>2) \<Rightarrow> True | (a\<^sub>2, a\<^sub>3) \<Rightarrow> True | (a\<^sub>2, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>3) \<Rightarrow> True | (a\<^sub>3, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>4, a\<^sub>4) \<Rightarrow> True
   | _ \<Rightarrow> False)"

instance proof (intro_classes)
  fix x::finite_mod_5
  show refl: "x \<le> x" unfolding less_eq_finite_mod_5_def
    by (smt (z3) curry_case_prod curry_conv finite_mod_5.case(1) finite_mod_5.case(2) finite_mod_5.case(3) finite_mod_5.case(4) finite_mod_5.case(5) finite_mod_5.exhaust)
  fix y::finite_mod_5
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_finite_mod_4_def
    by (smt (z3) curry_case_prod curry_conv finite_mod_5.case(1) finite_mod_5.case(2) finite_mod_5.case(3) finite_mod_5.case(4) finite_mod_5.case(5) finite_mod_5.exhaust less_eq_finite_mod_5_def)
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_finite_mod_5_def 
    apply (cases "x", cases "y")
    apply simp_all
    by (metis finite_mod_5.exhaust finite_mod_5.simps(21) finite_mod_5.simps(22) finite_mod_5.simps(23) finite_mod_5.simps(24) finite_mod_5.simps(25))+
  fix z::finite_mod_5
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_finite_mod_5_def
    apply (cases "x", cases "y", cases "z") 
    apply simp_all
    by (metis finite_mod_5.exhaust finite_mod_5.simps(21) finite_mod_5.simps(22) finite_mod_5.simps(23) finite_mod_5.simps(24) finite_mod_5.simps(25))+
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_eq_finite_mod_5_def less_finite_mod_5_def
    apply (cases "x", cases "y") apply simp_all
    by (smt (z3) finite_mod_5.exhaust finite_mod_5.simps(21) finite_mod_5.simps(22) finite_mod_5.simps(23) finite_mod_5.simps(24) finite_mod_5.simps(25))+
  qed

end

hide_const (open) a\<^sub>0 a\<^sub>1 a\<^sub>2 a\<^sub>3 a\<^sub>4

end
