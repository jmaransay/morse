
theory Mod_type
  imports 
    "HOL-Analysis.Cartesian_Euclidean_Space"
    Enum_mod
begin

class class_mod_type = zero + one + plus + times + uminus + minus + ord + enum +
  fixes Rep :: "'a \<Rightarrow> int"
  and Abs :: "int \<Rightarrow> 'a"
  assumes type: "type_definition Rep Abs {0..< int CARD('a)}"
  and size1: "1 < CARD('a)"
  and zero_def: "0 = Abs 0"
  and one_def:  "1 = Abs 1"
  and add_def:  "x + y = Abs ((Rep x + Rep y) mod int CARD('a))"
  and mult_def: "x * y = Abs ((Rep x * Rep y) mod int CARD('a))"
  and diff_def: "x - y = Abs ((Rep x - Rep y) mod int CARD('a))"
  and minus_def: "- x = Abs ((- Rep x) mod int CARD('a))"
  and less_def: "x < y = (Rep x < Rep y)"
  and less_eq_def: "x \<le> y = (Rep x \<le> Rep y)"
begin

lemma Rep_in: "Rep x \<in> {0::int..<int CARD('a)}"
  by (meson local.type type_definition.Rep)

lemma Abs_Rep_inverse: "Abs (Rep x) = x"
  by (rule type_definition.Rep_inverse [of _ _ "{0::int..<int CARD('a)}"])
   (rule local.type)

lemma Rep_Abs_inverse: assumes y: "y \<in> {0::int..<int CARD('a)}" 
  shows "Rep (Abs y) = y"
  by (rule type_definition.Abs_inverse [of Rep Abs "{0::int..<int CARD('a)}"])
   (rule local.type, rule y)

(*sublocale f: mod_type "int CARD ('a)" Rep Abs
  using mod_type.intro [of Rep Abs "CARD('a)"]
  apply (intro_locales)
  using local.add_def local.diff_def local.minus_def local.mult_def local.one_def 
    local.size1 local.type local.zero_def by fastforce*)

lemma size0: "0 < int CARD ('a)"
  using size1 by simp

lemmas definitions =
  zero_def one_def add_def mult_def minus_def diff_def

lemma Rep_less_n: "Rep x < int CARD ('a)"
  by (rule type_definition.Rep [OF type, simplified, THEN conjunct2])

lemma Rep_le_n: "Rep x \<le> int CARD ('a)"
  by (rule Rep_less_n [THEN order_less_imp_le])

lemma Rep_inject_sym: "x = y \<longleftrightarrow> Rep x = Rep y"
  by (rule type_definition.Rep_inject [OF type, symmetric])

lemma Rep_inverse: "Abs (Rep x) = x"
  by (rule type_definition.Rep_inverse [OF type])

lemma Abs_inverse: "m \<in> {0..<int CARD ('a)} \<Longrightarrow> Rep (Abs m) = m"
  by (rule type_definition.Abs_inverse [OF type])

lemma Rep_Abs_mod: "Rep (Abs (m mod int CARD ('a))) = m mod int CARD ('a)"
  by (simp add: Abs_inverse pos_mod_conj [OF size0])

lemma Rep_Abs_0: "Rep (Abs 0) = 0"
  using Abs_inverse [of 0] using size0 by simp

lemma Rep_0: "Rep 0 = 0"
  by (simp add: zero_def Rep_Abs_0)

lemma Rep_Abs_1: "Rep (Abs 1) = 1"
  using Abs_inverse [of 1] using size1 by simp

lemma Rep_1: "Rep 1 = 1"
  by (simp add: one_def Rep_Abs_1)

lemma Rep_mod: "Rep x mod (int CARD('a)) = Rep x"
  by (meson Rep_in mod_pos_pos_trivial ord_class.atLeastLessThan_iff)

lemmas Rep_simps =
  Rep_inject_sym Rep_inverse Rep_Abs_mod Rep_mod Rep_Abs_0 Rep_Abs_1

lemma bij_betw_univ_range: "bij_betw Rep UNIV {0..< int CARD('a)}"
  unfolding bij_betw_def unfolding inj_def
  by (meson Rep_inject_sym type type_definition.Rep_range)

lemma inj_on_Abs: "inj_on Abs {0..<int CARD('a)}" 
  unfolding inj_on_def
  by (metis Abs_inverse)

lemma range_Abs: "range Abs = UNIV"
  unfolding surj_def
  by (metis Rep_inverse)

lemma bij_betw_range_univ: "bij_betw Abs {0..<int CARD('a)} UNIV"
  unfolding bij_betw_def using inj_on_Abs range_Abs
  by (metis local.type type_definition.univ)

definition to_int :: "'a => int"
  where "to_int = Rep"

definition from_int :: "int => 'a"
  where "from_int x = Abs (x mod int CARD ('a))"

lemma inj_to_int: "inj to_int"
  by (simp add: Rep_inject_sym inj_on_def to_int_def)

lemma range_to_int: "range (to_int::'a \<Rightarrow> int) = {0..<int CARD('a)}"
  by (simp add: bij_betw_imp_surj_on bij_betw_univ_range to_int_def)

lemma bij_betw_range_univ_to_int: "bij_betw to_int UNIV {0 ..<int CARD('a)}"
  unfolding bij_betw_def
  using inj_to_int range_to_int by blast

lemma inj_on_from_int: "inj_on from_int {0..<int CARD('a)}"
  by (metis (mono_tags, lifting) Rep_Abs_inverse Rep_mod from_int_def inj_onI)

lemma range_from_int: "range (from_int::int \<Rightarrow> 'a) = (UNIV::'a set)"
proof (unfold surj_def, rule)
  fix y::'a
  show "\<exists>x::int. y = from_int x"
    apply (rule exI [of _ "Rep y"])
    apply (unfold from_int_def) try
    using Rep_inverse Rep_mod by presburger
qed

lemma bij_betw_range_univ_from_int: "bij_betw from_int {0..<int CARD('a)} UNIV"
  unfolding bij_betw_def
  using inj_on_from_int range_from_int
  by (metis Abs_inverse Rep_mod from_int_def image_cong local.type type_definition.univ)

lemma finite_univ: "finite (UNIV::'a set)"
  using Finite_Set.bij_betw_finite [OF bij_betw_univ_range]
  using Set_Interval.finite_atLeastZeroLessThan_int [of "int CARD('a)"] by blast

subclass finite
  by (intro_classes) (rule finite_univ)

subclass linorder
  apply (unfold class.linorder_def class.linorder_axioms_def 
    class.order_def class.order_axioms_def class.preorder_def less_def less_eq_def, 
    intro conjI)
  apply auto [1]
  apply simp
  apply simp
   apply (simp add: Rep_inject_sym)
  by auto

end

end