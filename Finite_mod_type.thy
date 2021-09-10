
theory Finite_mod_type
  imports 
    Mod_type 
    Enum_mod
begin

lemma CARD_finite_mod_1 [simp]: "CARD(finite_mod_1) = 1"
  unfolding card_UNIV_length_enum 
  unfolding enum_finite_mod_1_def by simp

lemma CARD_finite_mod_2 [simp]: "CARD(finite_mod_2) = 2"
  unfolding card_UNIV_length_enum 
  unfolding enum_finite_mod_2_def by simp

lemma CARD_finite_mod_3 [simp]: "CARD(finite_mod_3) = 3"
  unfolding card_UNIV_length_enum 
  unfolding enum_finite_mod_3_def by simp

lemma CARD_finite_mod_5 [simp]: "CARD(finite_mod_5) = 5"
  unfolding card_UNIV_length_enum
  unfolding enum_finite_mod_5_def by simp

instantiation finite_mod_4 :: class_mod_type
begin

notation finite_mod_4.a\<^sub>0  ("a\<^sub>0")
notation finite_mod_4.a\<^sub>1  ("a\<^sub>1")
notation finite_mod_4.a\<^sub>2  ("a\<^sub>2")
notation finite_mod_4.a\<^sub>3  ("a\<^sub>3")

definition "Rep = (\<lambda>i::finite_mod_4. case (i) of a\<^sub>0 \<Rightarrow> 0
                                                | a\<^sub>1 \<Rightarrow> 1
                                                | a\<^sub>2 \<Rightarrow> 2
                                                | a\<^sub>3 \<Rightarrow> 3)"

definition "Abs = (\<lambda>i::int. if (i mod 4) = 0 then a\<^sub>0
                                                else if (i mod 4) = 1 then a\<^sub>1
                                                  else if (i mod 4) = 2 then a\<^sub>2
                                                    else a\<^sub>3)"

lemma Abs0: "Abs 0 = a\<^sub>0" unfolding Abs_finite_mod_4_def by simp

lemma Abs1: "Abs 1 = a\<^sub>1" unfolding Abs_finite_mod_4_def by simp

lemma Abs2: "Abs 2 = a\<^sub>2" unfolding Abs_finite_mod_4_def by simp

lemma Abs3: "Abs 3 = a\<^sub>3" unfolding Abs_finite_mod_4_def by simp

lemmas AbsExt = Abs0 Abs1 Abs2 Abs3

lemma Rep0: "Rep a\<^sub>0 = 0" unfolding Rep_finite_mod_4_def by simp

lemma Rep1: "Rep a\<^sub>1 = 1" unfolding Rep_finite_mod_4_def by simp

lemma Rep2: "Rep a\<^sub>2 = 2" unfolding Rep_finite_mod_4_def by simp

lemma Rep3: "Rep a\<^sub>3 = 3" unfolding Rep_finite_mod_4_def by simp

lemmas RepExt = Rep0 Rep1 Rep2 Rep3

lemma CARD_finite_mod_4 [simp]: "CARD(finite_mod_4) = 4"
  unfolding card_UNIV_length_enum 
  unfolding enum_finite_mod_4_def by simp

lemma Abs_mod: "Abs (x mod int 4) = (Abs::int \<Rightarrow> finite_mod_4) x"
  unfolding Abs_finite_mod_4_def by simp

lemma type_definition_finite_mod_4: "type_definition (Rep::(finite_mod_4 \<Rightarrow> int)) Abs {0..<int CARD(finite_mod_4)}"
proof (unfold type_definition_def, rule conjI)
  show "\<forall>x. (Rep::finite_mod_4 \<Rightarrow> int) x \<in> {0..<int CARD(finite_mod_4)}" 
    unfolding CARD_finite_mod_4 
    using RepExt
    by (smt (verit, ccfv_threshold) atLeastLessThan_iff finite_mod_4.exhaust int_ops(2) int_ops(3) numeral_Bit0 numerals(1))
  show "(\<forall>x. Abs ((Rep::finite_mod_4 \<Rightarrow> int) x) = x) \<and> (\<forall>y. y \<in> {0..<int CARD(finite_mod_4)} \<longrightarrow> (Rep::finite_mod_4 \<Rightarrow> int) (Abs y) = y)"
  proof (rule conjI)
    show "\<forall>x. Abs ((Rep::finite_mod_4 \<Rightarrow> int) x) = x"
      by (smt (z3) AbsExt RepExt finite_mod_4.exhaust)
    show "\<forall>y. y \<in> {0..<int CARD(finite_mod_4)} \<longrightarrow> (Rep::finite_mod_4 \<Rightarrow> int) (Abs y) = y"
      by (smt (verit, ccfv_threshold) Abs_finite_mod_4_def CARD_finite_mod_4 RepExt atLeastLessThan_iff mod_pos_pos_trivial numeral_Bit0 numerals(1) of_nat_1 of_nat_numeral)
  qed
qed

definition "1 = a\<^sub>1"

definition plus_finite_mod_4 :: "finite_mod_4 \<Rightarrow> finite_mod_4 \<Rightarrow> finite_mod_4"
  where "plus_finite_mod_4 a b = Abs ((Rep a) + (Rep b))"

definition minus_finite_mod_4 :: "finite_mod_4 \<Rightarrow> finite_mod_4 \<Rightarrow> finite_mod_4"
  where "minus_finite_mod_4 a b = Abs ((Rep a) - (Rep b))"

definition uminus_finite_mod_4 :: "finite_mod_4 \<Rightarrow> finite_mod_4"
  where "uminus_finite_mod_4 x = finite_mod_4.a\<^sub>0 - x"

lemma "a\<^sub>2 - a\<^sub>1 = a\<^sub>1"
  unfolding minus_finite_mod_4_def
  by (simp add: Abs_finite_mod_4_def Rep_finite_mod_4_def)

definition "0 = a\<^sub>0"

definition times_finite_mod_4 :: "finite_mod_4 \<Rightarrow> finite_mod_4 \<Rightarrow> finite_mod_4"
  where "times_finite_mod_4 a b = Abs ((Rep a) * (Rep b))"

lemma "a\<^sub>2 * a\<^sub>1 = a\<^sub>2"
  unfolding times_finite_mod_4_def
  by (simp add: Abs_finite_mod_4_def Rep_finite_mod_4_def)

instance
proof (intro_classes)
  show "type_definition (Rep::(finite_mod_4 \<Rightarrow> int)) Abs {0..<int CARD(finite_mod_4)}" 
    using type_definition_finite_mod_4 .
  show "(1::nat) < CARD(finite_mod_4)" by simp
  show "(0::finite_mod_4) = Abs (0::int)" unfolding zero_finite_mod_4_def Abs_finite_mod_4_def by simp
  show "(1::finite_mod_4) = Abs (1::int)" unfolding one_finite_mod_4_def Abs_finite_mod_4_def by simp
  fix x::finite_mod_4 and y::finite_mod_4
  show "x + y = Abs ((Rep x + Rep y) mod int CARD(finite_mod_4))"
    unfolding CARD_finite_mod_4
    unfolding plus_finite_mod_4_def 
    unfolding Abs_mod ..  
  show "x * y = Abs (Rep x * Rep y mod int CARD(finite_mod_4))"  
    unfolding CARD_finite_mod_4
    unfolding times_finite_mod_4_def 
    unfolding Abs_mod ..
  show "x - y = Abs ((Rep x - Rep y) mod int CARD(finite_mod_4))"
    unfolding CARD_finite_mod_4
    unfolding minus_finite_mod_4_def
    unfolding Abs_mod..
  show "- x = Abs (- Rep x mod int CARD(finite_mod_4))"
    unfolding CARD_finite_mod_4
    unfolding uminus_finite_mod_4_def
    unfolding Abs_mod
    using RepExt(1) minus_finite_mod_4_def by fastforce
  show "(x < y) = (Rep x < Rep y)"
    by (smt (z3) Rep_finite_mod_4_def finite_mod_4.exhaust finite_mod_4.simps(13) finite_mod_4.simps(14) finite_mod_4.simps(15) finite_mod_4.simps(16) less_finite_mod_4_def prod.simps(2))
  show "(x \<le> y) = (Rep x \<le> Rep y)"
    by (smt (z3) RepExt(1) RepExt(2) RepExt(3) RepExt(4) \<open>(x < y) = (Rep x < Rep y)\<close> dual_order.order_iff_strict finite_mod_4.exhaust)
qed

lemma to_int_a1: "to_int a\<^sub>0 = 0" unfolding to_int_def using RepExt(1) .

lemma to_int_a2: "to_int a\<^sub>1 = 1" unfolding to_int_def using RepExt(2) . 

lemma to_int_a3: "to_int a\<^sub>2 = 2" unfolding to_int_def using RepExt(3) . 

lemma to_int_a4: "to_int a\<^sub>3 = 3" unfolding to_int_def using RepExt(4) .

lemmas to_int_finite_mod_4 [simp] = to_int_a1 to_int_a2 to_int_a3 to_int_a4

lemma finite_UNIV: "finite {a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3}"
  by simp

lemma finite_mod_4_enum: "{a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3} = set [a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3]"
  by simp

lemma cfi: "comp_fun_idem (\<lambda>x A. A \<union> insert x ` A)"
  unfolding comp_fun_idem_def
  unfolding comp_fun_commute_def apply auto unfolding comp_def apply (rule ext) apply auto
  unfolding comp_fun_idem_axioms_def unfolding comp_def by auto

lemma powerset_finite_mod_4: "Pow {a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3} = {{},{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0,a\<^sub>1},{a\<^sub>0,a\<^sub>2},{a\<^sub>0,a\<^sub>3},{a\<^sub>1,a\<^sub>2},{a\<^sub>1,a\<^sub>3},{a\<^sub>2,a\<^sub>3},
      {a\<^sub>0,a\<^sub>1,a\<^sub>2},{a\<^sub>0,a\<^sub>1,a\<^sub>3},{a\<^sub>0,a\<^sub>2,a\<^sub>3},{a\<^sub>1,a\<^sub>2,a\<^sub>3},{a\<^sub>0,a\<^sub>1,a\<^sub>2,a\<^sub>3}}"
  unfolding Finite_Set.Pow_fold [OF finite_UNIV] 
  unfolding finite_mod_4_enum
  unfolding comp_fun_idem.fold_set_fold [OF cfi]
  unfolding fold_simps (2) [of "(\<lambda>x A. A \<union> insert x ` A)" "a\<^sub>0" "[a\<^sub>1,a\<^sub>2,a\<^sub>3]" "{{}}"]
  unfolding fold_simps (2) [of "(\<lambda>x A. A \<union> insert x ` A)" "a\<^sub>1" "[a\<^sub>2, a\<^sub>3]" "({{}} \<union> insert a\<^sub>0 ` {{}})"]
  unfolding fold_simps (2) [of "(\<lambda>x A. A \<union> insert x ` A)" "a\<^sub>2" "[a\<^sub>3]" "({{}} \<union> insert a\<^sub>0 ` {{}} \<union> insert a\<^sub>1 ` ({{}} \<union> insert a\<^sub>0 ` {{}}))"]
  unfolding fold_simps (2) [of "(\<lambda>x A. A \<union> insert x ` A)" "a\<^sub>3" "[]" "({{}} \<union> insert a\<^sub>0 ` {{}} \<union> insert a\<^sub>1 ` ({{}} \<union> insert a\<^sub>0 ` {{}}) \<union>
      insert a\<^sub>2 ` ({{}} \<union> insert a\<^sub>0 ` {{}} \<union> insert a\<^sub>1 ` ({{}} \<union> insert a\<^sub>0 ` {{}})))"]
  unfolding fold_simps (1) 
  unfolding finite_mod_4_enum [symmetric]
  by (simp add: insert_commute)

lemma list_powerset_finite_mod_4: "Pow {a\<^sub>0, a\<^sub>1, a\<^sub>2, a\<^sub>3} 
  = set [{},{a\<^sub>0},{a\<^sub>1},{a\<^sub>2},{a\<^sub>3},{a\<^sub>0,a\<^sub>1},{a\<^sub>0,a\<^sub>2},{a\<^sub>0,a\<^sub>3},{a\<^sub>1,a\<^sub>2},{a\<^sub>1,a\<^sub>3},{a\<^sub>2,a\<^sub>3},
      {a\<^sub>0,a\<^sub>1,a\<^sub>2},{a\<^sub>0,a\<^sub>1,a\<^sub>3},{a\<^sub>0,a\<^sub>2,a\<^sub>3},{a\<^sub>1,a\<^sub>2,a\<^sub>3},{a\<^sub>0,a\<^sub>1,a\<^sub>2,a\<^sub>3}]"
  unfolding powerset_finite_mod_4 by simp

end

text\<open>TODO: prove that the bit0 type constructor is an instance of class_mod_type\<close>




instantiation bit0:: (finite) class_mod_type
begin

definition "(Rep::'a bit0 => int) x = Rep_bit0 x"
definition "(Abs::int => 'a bit0) x = Abs_bit0' x"

lemma Abs_bit0'_mod [simp]: "(Abs_bit0'::int \<Rightarrow> 'a bit0) x = Abs_bit0' (x mod int CARD('a bit0))"
  unfolding Abs_bit0'_def
  by auto
          
instance proof (intro_classes)
  show "(1::nat) < CARD('a bit0)"
    by (metis One_nat_def one_less_card)
  fix x y :: "'a bit0"
  show "x + y = Abs ((Rep x + Rep y) mod int CARD('a bit0))"
    unfolding plus_bit0_def
    unfolding Abs_bit0_def
    unfolding Rep_bit0_def
    using Abs_bit0'_mod
    by arith
  show "x - y = Abs ((Rep x - Rep y) mod int CARD('a bit0))"
    unfolding minus_bit0_def
    unfolding Abs_bit0_def
    unfolding Rep_bit0_def
    using Abs_bit0'_mod
    by arith
  show "x * y = Abs ((Rep x * Rep y) mod int CARD('a bit0))"
    unfolding times_bit0_def
    unfolding Abs_bit0_def
    unfolding Rep_bit0_def
    using Abs_bit0'_mod
    by arith
  show "- x = Abs (- Rep x mod int CARD('a bit0))"
    unfolding uminus_bit0_def
    unfolding Abs_bit0_def
    unfolding Rep_bit0_def
    using Abs_bit0'_mod
    by arith
  show "(x < y) = (Rep x < Rep y)"
    unfolding less_bit0_def
    unfolding Rep_bit0_def
    by auto
  show "(x \<le> y) = (Rep x \<le> Rep y)"
    unfolding less_eq_bit0_def
    unfolding Rep_bit0_def
    by auto
  show "(0::'a bit0) = Abs (0::int)"
    unfolding Abs_bit0_def
    unfolding Abs_bit0'_def
    unfolding zero_bit0_def
    by auto
  show "(1::'a bit0) = Abs (1::int)"
    unfolding Abs_bit0_def
    unfolding Abs_bit0'_def
    unfolding one_bit0_def
    using \<open>(1::nat) < CARD('a bit0)\<close>
    by auto
  show "type_definition (Rep::'a bit0 => int) Abs {0::int..<int CARD('a bit0)}"
    by (smt (verit) Abs_bit0'_code Finite_mod_type.Abs_bit0_def Finite_mod_type.Rep_bit0_def bit0.Rep_mod bit0.type type_definition_def)
qed

end

text\<open>TODO: prove that the bit1 type constructor is an instance of class_mod_type\<close>

instantiation bit1:: (finite) class_mod_type
begin

definition "(Rep::'a bit1 => int) x = Rep_bit1 x"
definition "(Abs::int => 'a bit1) x = Abs_bit1' x"

lemma Abs_bit1'_mod [simp]: "(Abs_bit1'::int \<Rightarrow> 'a bit1) x = Abs_bit1' (x mod int CARD('a bit1))"
  unfolding Abs_bit1'_def
  by auto

instance proof (intro_classes)
  show "(1::nat) < CARD('a bit1)"
    by (metis One_nat_def one_less_card)
  fix x y :: "'a bit1"
  show "x + y = Abs ((Rep x + Rep y) mod int CARD('a bit1))"
    unfolding plus_bit1_def
    unfolding Abs_bit1_def
    unfolding Rep_bit1_def
    using Abs_bit1'_mod
    by arith
  show "x - y = Abs ((Rep x - Rep y) mod int CARD('a bit1))"
    unfolding minus_bit1_def
    unfolding Abs_bit1_def
    unfolding Rep_bit1_def
    using Abs_bit1'_mod
    by arith
  show "x * y = Abs ((Rep x * Rep y) mod int CARD('a bit1))"
    unfolding times_bit1_def
    unfolding Abs_bit1_def
    unfolding Rep_bit1_def
    using Abs_bit1'_mod
    by arith
  show "- x = Abs (- Rep x mod int CARD('a bit1))"
    unfolding uminus_bit1_def
    unfolding Abs_bit1_def
    unfolding Rep_bit1_def
    using Abs_bit1'_mod
    by arith
  show "(x < y) = (Rep x < Rep y)"
    unfolding less_bit1_def
    unfolding Rep_bit1_def
    by auto
  show "(x \<le> y) = (Rep x \<le> Rep y)"
    unfolding less_eq_bit1_def
    unfolding Rep_bit1_def
    by auto
  show "(0::'a bit1) = Abs (0::int)"
    unfolding Abs_bit1_def
    unfolding Abs_bit1'_def
    unfolding zero_bit1_def
    by auto
  show "(1::'a bit1) = Abs (1::int)"
    unfolding Abs_bit1_def
    unfolding Abs_bit1'_def
    unfolding one_bit1_def
    using \<open>(1::nat) < CARD('a bit1)\<close>
    by auto
  show "type_definition (Rep::'a bit1 => int) Abs {0::int..<int CARD('a bit1)}"
    by (smt (verit, ccfv_threshold) Abs_bit1'_code Finite_mod_type.Abs_bit1_def Finite_mod_type.Rep_bit1_def bit1.Rep_mod bit1.type type_definition_def)
qed

end

end