
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Finite types as explicit enumerations\<close>

theory Enum_mod
  imports Main
begin

subsection \<open>Small finite types as arithmetic modulo its cardinal\<close>

text \<open>Similar types are defined as finite_1 up to finite_5 in Enum.thy, 
  but they define the bynary minus (see Enum.thy in the HOL folder 
  of the Isabelle distribution) not modulo the cardinal of the Universe set, 
  but as in a lattice\<close>

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

(*lemma two_finite_mod_2:
  "2 = a\<^sub>1" apply simp thm numeral.simps
  apply (simp add: numeral.simps plus_finite_mod_2_def) try

lemma dvd_finite_2_unfold:
  "x dvd y \<longleftrightarrow> x = a\<^sub>2 \<or> y = a\<^sub>1"
  by (auto simp add: dvd_def times_finite_mod_2_def split: finite_mod_2.splits)
   (meson finite_mod_2.exhaust)+

instantiation finite_mod_2 :: "{normalization_semidom, unique_euclidean_semiring}" begin
definition [simp]: "normalize = (id :: finite_mod_2 \<Rightarrow> _)"
definition [simp]: "unit_factor = (id :: finite_mod_2 \<Rightarrow> _)"
definition [simp]: "euclidean_size x = (case x of a\<^sub>1 \<Rightarrow> 0 | a\<^sub>2 \<Rightarrow> 1)"
definition [simp]: "division_segment (x :: finite_mod_2) = 1"
instance
  by standard
    (subproofs
      \<open>auto simp add: divide_finite_mod_2_def times_finite_mod_2_def dvd_finite_mod_2_unfold
        split: finite_mod_2.splits\<close>)
end*)

 
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

(*class finite_lattice = finite +  lattice + Inf + Sup  + bot + top +
  assumes Inf_finite_empty: "Inf {} = Sup UNIV"
  assumes Inf_finite_insert: "Inf (insert a A) = a \<sqinter> Inf A"
  assumes Sup_finite_empty: "Sup {} = Inf UNIV"
  assumes Sup_finite_insert: "Sup (insert a A) = a \<squnion> Sup A"
  assumes bot_finite_def: "bot = Inf UNIV"
  assumes top_finite_def: "top = Sup UNIV"
begin

subclass complete_lattice
proof
  fix x A
  show "x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x"
    by (metis Set.set_insert abel_semigroup.commute local.Inf_finite_insert local.inf.abel_semigroup_axioms local.inf.left_idem local.inf.orderI)
  show "x \<in> A \<Longrightarrow> x \<le> \<Squnion>A"
    by (metis Set.set_insert insert_absorb2 local.Sup_finite_insert local.sup.absorb_iff2)
next
  fix A z
  have "\<Squnion> UNIV = z \<squnion> \<Squnion>UNIV"
    by (subst Sup_finite_insert [symmetric], simp add: insert_UNIV)
  from this have [simp]: "z \<le> \<Squnion>UNIV"
    using local.le_iff_sup by auto
  have "(\<forall> x. x \<in> A \<longrightarrow> z \<le> x) \<longrightarrow> z \<le> \<Sqinter>A"
    by (rule finite_induct [of A "\<lambda> A . (\<forall> x. x \<in> A \<longrightarrow> z \<le> x) \<longrightarrow> z \<le> \<Sqinter>A"])
      (simp_all add: Inf_finite_empty Inf_finite_insert)
  from this show "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>A"
    by simp

  have "\<Sqinter> UNIV = z \<sqinter> \<Sqinter>UNIV"
    by (subst Inf_finite_insert [symmetric], simp add: insert_UNIV)
  from this have [simp]: "\<Sqinter>UNIV \<le> z"
    by (simp add: local.inf.absorb_iff2)
  have "(\<forall> x. x \<in> A \<longrightarrow> x \<le> z) \<longrightarrow> \<Squnion>A \<le> z"
    by (rule finite_induct [of A "\<lambda> A . (\<forall> x. x \<in> A \<longrightarrow> x \<le> z) \<longrightarrow> \<Squnion>A \<le> z" ], simp_all add: Sup_finite_empty Sup_finite_insert)
  from this show " (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
    by blast
next
  show "\<Sqinter>{} = \<top>"
    by (simp add: Inf_finite_empty top_finite_def)
  show " \<Squnion>{} = \<bottom>"
    by (simp add: Sup_finite_empty bot_finite_def)
qed
end

class finite_distrib_lattice = finite_lattice + distrib_lattice 
begin
lemma finite_inf_Sup: "a \<sqinter> (Sup A) = Sup {a \<sqinter> b | b . b \<in> A}"
proof (rule finite_induct [of A "\<lambda> A . a \<sqinter> (Sup A) = Sup {a \<sqinter> b | b . b \<in> A}"], simp_all)
  fix x::"'a"
  fix F
  assume "x \<notin> F"
  assume [simp]: "a \<sqinter> \<Squnion>F = \<Squnion>{a \<sqinter> b |b. b \<in> F}"
  have [simp]: " insert (a \<sqinter> x) {a \<sqinter> b |b. b \<in> F} = {a \<sqinter> b |b. b = x \<or> b \<in> F}"
    by blast
  have "a \<sqinter> (x \<squnion> \<Squnion>F) = a \<sqinter> x \<squnion> a \<sqinter> \<Squnion>F"
    by (simp add: inf_sup_distrib1)
  also have "... = a \<sqinter> x \<squnion> \<Squnion>{a \<sqinter> b |b. b \<in> F}"
    by simp
  also have "... = \<Squnion>{a \<sqinter> b |b. b = x \<or> b \<in> F}"
    by (unfold Sup_insert[THEN sym], simp)
  finally show "a \<sqinter> (x \<squnion> \<Squnion>F) = \<Squnion>{a \<sqinter> b |b. b = x \<or> b \<in> F}"
    by simp
qed

lemma finite_Inf_Sup: "\<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"
proof (rule finite_induct [of A "\<lambda>A. \<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"], simp_all add: finite_UnionD)
  fix x::"'a set"
  fix F
  assume "x \<notin> F"
  have [simp]: "{\<Squnion>x \<sqinter> b |b . b \<in> Inf ` {f ` F |f. \<forall>Y\<in>F. f Y \<in> Y} } = {\<Squnion>x \<sqinter> (Inf (f ` F)) |f  . (\<forall>Y\<in>F. f Y \<in> Y)}"
    by auto
  define fa where "fa = (\<lambda> (b::'a) f Y . (if Y = x then b else f Y))"
  have "\<And>f b. \<forall>Y\<in>F. f Y \<in> Y \<Longrightarrow> b \<in> x \<Longrightarrow> insert b (f ` (F \<inter> {Y. Y \<noteq> x})) = insert (fa b f x) (fa b f ` F) \<and> fa b f x \<in> x \<and> (\<forall>Y\<in>F. fa b f Y \<in> Y)"
    by (auto simp add: fa_def)
  from this have B: "\<And>f b. \<forall>Y\<in>F. f Y \<in> Y \<Longrightarrow> b \<in> x \<Longrightarrow> fa b f ` ({x} \<union> F) \<in> {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)}"
    by blast
  have [simp]: "\<And>f b. \<forall>Y\<in>F. f Y \<in> Y \<Longrightarrow> b \<in> x \<Longrightarrow> b \<sqinter> (\<Sqinter>x\<in>F. f x)  \<le> \<Squnion>(Inf ` {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)})"
    using B apply (rule SUP_upper2)
    using \<open>x \<notin> F\<close> apply (simp_all add: fa_def Inf_union_distrib)
    apply (simp add: image_mono Inf_superset_mono inf.coboundedI2)
    done
  assume "\<Sqinter>(Sup ` F) \<le> \<Squnion>(Inf ` {f ` F |f. \<forall>Y\<in>F. f Y \<in> Y})"

  from this have "\<Squnion>x \<sqinter> \<Sqinter>(Sup ` F) \<le> \<Squnion>x \<sqinter> \<Squnion>(Inf ` {f ` F |f. \<forall>Y\<in>F. f Y \<in> Y})"
    using inf.coboundedI2 by auto
  also have "... = Sup {\<Squnion>x \<sqinter> (Inf (f ` F)) |f  .  (\<forall>Y\<in>F. f Y \<in> Y)}"
    by (simp add: finite_inf_Sup)

  also have "... = Sup {Sup {Inf (f ` F) \<sqinter> b | b . b \<in> x} |f  .  (\<forall>Y\<in>F. f Y \<in> Y)}"
    by (subst inf_commute) (simp add: finite_inf_Sup)

  also have "... \<le> \<Squnion>(Inf ` {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)})"
    apply (rule Sup_least, clarsimp)+
    apply (subst inf_commute, simp)
    done

  finally show "\<Squnion>x \<sqinter> \<Sqinter>(Sup ` F) \<le> \<Squnion>(Inf ` {insert (f x) (f ` F) |f. f x \<in> x \<and> (\<forall>Y\<in>F. f Y \<in> Y)})"
    by simp
qed

subclass complete_distrib_lattice
  by (standard, rule finite_Inf_Sup)
end

instantiation finite_3 :: finite_lattice
begin

definition "\<Sqinter>A = (if a\<^sub>1 \<in> A then a\<^sub>1 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>3)"
definition "\<Squnion>A = (if a\<^sub>3 \<in> A then a\<^sub>3 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>1)"
definition [simp]: "bot = a\<^sub>1"
definition [simp]: "top = a\<^sub>3"
definition [simp]: "inf = (min :: finite_3 \<Rightarrow> _)"
definition [simp]: "sup = (max :: finite_3 \<Rightarrow> _)"

instance
proof
qed (auto simp add: Inf_finite_3_def Sup_finite_3_def max_def min_def less_eq_finite_3_def less_finite_3_def split: finite_3.split)
end

instance finite_3 :: complete_lattice ..

instance finite_3 :: finite_distrib_lattice
proof 
qed (auto simp add: min_def max_def)

instance finite_3 :: complete_distrib_lattice ..

instance finite_3 :: complete_linorder ..
*)

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

(*lemma two_finite_mod_3 [simp]:
  "2 = a\<^sub>3"
  by (simp add: numeral.simps plus_finite_mod_3_def)

lemma dvd_finite_3_unfold:
  "x dvd y \<longleftrightarrow> x = a\<^sub>2 \<or> x = a\<^sub>3 \<or> y = a\<^sub>1"
  by (cases x) (auto simp add: dvd_def times_finite_3_def split: finite_3.splits)

instantiation finite_3 :: "{normalization_semidom, unique_euclidean_semiring}" begin
definition [simp]: "normalize x = (case x of a\<^sub>3 \<Rightarrow> a\<^sub>2 | _ \<Rightarrow> x)"
definition [simp]: "unit_factor = (id :: finite_3 \<Rightarrow> _)"
definition [simp]: "euclidean_size x = (case x of a\<^sub>1 \<Rightarrow> 0 | _ \<Rightarrow> 1)"
definition [simp]: "division_segment (x :: finite_3) = 1"
instance
proof
  fix x :: finite_3
  assume "x \<noteq> 0"
  then show "is_unit (unit_factor x)"
    by (cases x) (simp_all add: dvd_finite_3_unfold)
qed
  (subproofs
    \<open>auto simp add: divide_finite_3_def times_finite_3_def
      dvd_finite_3_unfold inverse_finite_3_def plus_finite_3_def
      split: finite_3.splits\<close>)
end
*)
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

instantiation finite_mod_4 :: finite_distrib_lattice begin

text \<open>\<^term>\<open>a\<^sub>0\<close> $<$ \<^term>\<open>a\<^sub>1\<close>,\<^term>\<open>a\<^sub>2\<close> $<$ \<^term>\<open>a\<^sub>3\<close>,
  but \<^term>\<open>a\<^sub>1\<close> and \<^term>\<open>a\<^sub>2\<close> are incomparable.\<close>

definition
  "x < y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, a\<^sub>0) \<Rightarrow> False | (a\<^sub>0, _) \<Rightarrow> True
   |  (a\<^sub>1, a\<^sub>3) \<Rightarrow> True
   |  (a\<^sub>2, a\<^sub>3) \<Rightarrow> True  | _ \<Rightarrow> False)"

definition 
  "x \<le> y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, _) \<Rightarrow> True
   | (a\<^sub>1, a\<^sub>1) \<Rightarrow> True | (a\<^sub>1, a\<^sub>3) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>2) \<Rightarrow> True | (a\<^sub>2, a\<^sub>3) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>3) \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  "Inf A = (if a\<^sub>0 \<in> A \<or> a\<^sub>1 \<in> A \<and> a\<^sub>2 \<in> A then a\<^sub>0 else if a\<^sub>1 \<in> A then a\<^sub>1 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>3)"
definition
  "Sup A = (if a\<^sub>3 \<in> A \<or> a\<^sub>1 \<in> A \<and> a\<^sub>2 \<in> A then a\<^sub>3 else if a\<^sub>1 \<in> A then a\<^sub>1 else if a\<^sub>2 \<in> A then a\<^sub>2 else a\<^sub>0)"
definition [simp]: "bot = a\<^sub>0"
definition [simp]: "top = a\<^sub>3"
definition
  "inf x y = (case (x, y) of
     (a\<^sub>0, _) \<Rightarrow> a\<^sub>0 | (_, a\<^sub>0) \<Rightarrow> a\<^sub>0 | (a\<^sub>1, a\<^sub>2) \<Rightarrow> a\<^sub>0 | (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>0
   | (a\<^sub>1, _) \<Rightarrow> a\<^sub>1 | (_, a\<^sub>1) \<Rightarrow> a\<^sub>1
   | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
   | _ \<Rightarrow> a\<^sub>3)"
definition
  "sup x y = (case (x, y) of
     (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3 | (a\<^sub>1, a\<^sub>2) \<Rightarrow> a\<^sub>3 | (a\<^sub>2, a\<^sub>1) \<Rightarrow> a\<^sub>3
  | (a\<^sub>1, _) \<Rightarrow> a\<^sub>1 | (_, a\<^sub>1) \<Rightarrow> a\<^sub>1
  | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
  | _ \<Rightarrow> a\<^sub>0)"

instance
  by standard
    (subproofs
      \<open>auto simp add: less_finite_mod_4_def less_eq_finite_mod_4_def Inf_finite_mod_4_def Sup_finite_mod_4_def 
        inf_finite_mod_4_def sup_finite_mod_4_def split: finite_mod_4.splits\<close>)
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

instantiation finite_mod_5 :: finite_lattice
begin

text \<open>The non-distributive pentagon lattice $N_5$\<close>

definition
  "x < y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, a\<^sub>0) \<Rightarrow> False | (a\<^sub>0, _) \<Rightarrow> True
   | (a\<^sub>1, a\<^sub>2) \<Rightarrow> True  | (a\<^sub>1, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>4) \<Rightarrow> True  | _ \<Rightarrow> False)"

definition
  "x \<le> y \<longleftrightarrow> (case (x, y) of
     (a\<^sub>0, _) \<Rightarrow> True
   | (a\<^sub>1, a\<^sub>1) \<Rightarrow> True | (a\<^sub>1, a\<^sub>2) \<Rightarrow> True | (a\<^sub>1, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>2, a\<^sub>2) \<Rightarrow> True | (a\<^sub>2, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>3, a\<^sub>3) \<Rightarrow> True | (a\<^sub>3, a\<^sub>4) \<Rightarrow> True
   | (a\<^sub>4, a\<^sub>4) \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  "Inf A = 
  (if a\<^sub>0 \<in> A \<or> a\<^sub>3 \<in> A \<and> (a\<^sub>1 \<in> A \<or> a\<^sub>2 \<in> A) then a\<^sub>0
   else if a\<^sub>1 \<in> A then a\<^sub>1
   else if a\<^sub>2 \<in> A then a\<^sub>2
   else if a\<^sub>3 \<in> A then a\<^sub>3
   else a\<^sub>4)"
definition
  "Sup A = 
  (if a\<^sub>4 \<in> A \<or> a\<^sub>3 \<in> A \<and> (a\<^sub>1 \<in> A \<or> a\<^sub>2 \<in> A) then a\<^sub>4
   else if a\<^sub>2 \<in> A then a\<^sub>2
   else if a\<^sub>1 \<in> A then a\<^sub>1
   else if a\<^sub>3 \<in> A then a\<^sub>3
   else a\<^sub>0)"
definition [simp]: "bot = a\<^sub>0"
definition [simp]: "top = a\<^sub>4"
definition
  "inf x y = (case (x, y) of
     (a\<^sub>0, _) \<Rightarrow> a\<^sub>0 | (_, a\<^sub>0) \<Rightarrow> a\<^sub>0 | (a\<^sub>1, a\<^sub>3) \<Rightarrow> a\<^sub>0 | (a\<^sub>3, a\<^sub>1) \<Rightarrow> a\<^sub>0 | (a\<^sub>2, a\<^sub>3) \<Rightarrow> a\<^sub>0 | (a\<^sub>3, a\<^sub>2) \<Rightarrow> a\<^sub>0
   | (a\<^sub>1, _) \<Rightarrow> a\<^sub>1 | (_, a\<^sub>1) \<Rightarrow> a\<^sub>1
   | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
   | (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3
   | _ \<Rightarrow> a\<^sub>4)"
definition
  "sup x y = (case (x, y) of
     (a\<^sub>4, _) \<Rightarrow> a\<^sub>4 | (_, a\<^sub>4) \<Rightarrow> a\<^sub>4 | (a\<^sub>1, a\<^sub>3) \<Rightarrow> a\<^sub>4 | (a\<^sub>3, a\<^sub>1) \<Rightarrow> a\<^sub>4 | (a\<^sub>2, a\<^sub>3) \<Rightarrow> a\<^sub>4 | (a\<^sub>3, a\<^sub>2) \<Rightarrow> a\<^sub>4
   | (a\<^sub>2, _) \<Rightarrow> a\<^sub>2 | (_, a\<^sub>2) \<Rightarrow> a\<^sub>2
   | (a\<^sub>1, _) \<Rightarrow> a\<^sub>1 | (_, a\<^sub>1) \<Rightarrow> a\<^sub>1
   | (a\<^sub>3, _) \<Rightarrow> a\<^sub>3 | (_, a\<^sub>3) \<Rightarrow> a\<^sub>3
   | _ \<Rightarrow> a\<^sub>0)"

instance
  by standard
    (subproofs
      \<open>auto simp add: less_eq_finite_mod_5_def less_finite_mod_5_def inf_finite_mod_5_def sup_finite_mod_5_def 
        Inf_finite_mod_5_def Sup_finite_mod_5_def split: finite_mod_5.splits if_split_asm\<close>)
end


instance  finite_mod_5 :: complete_lattice ..


hide_const (open) a\<^sub>0 a\<^sub>1 a\<^sub>2 a\<^sub>3 a\<^sub>4

subsection \<open>Closing up\<close>

(*hide_type (open) finite_mod_1 finite_mod_2 finite_mod_3 finite_mod_4 finite_mod_5*)
(*hide_const (open) enum enum_all enum_ex all_n_lists ex_n_lists ntrancl*)

end
