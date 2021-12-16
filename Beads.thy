
theory Beads
  imports 
    Boolean_functions
begin

definition first_half :: "bool vec \<Rightarrow> bool vec"
  where "first_half v = vec ((dim_vec v) div 2) (\<lambda> i. (v $ i))"

definition second_half :: "bool vec \<Rightarrow> bool vec"
  where "second_half v = vec ((dim_vec v) div 2) (\<lambda> i. (v $ (i + ((dim_vec v) div 2))))"

definition bead :: "bool vec => bool"
  where "bead v = (first_half v \<noteq> second_half v)"

lemma "bead (vec 8 (\<lambda>x. if x = 0 then True else False))"
(is "bead ?v")
proof -
  have "first_half ?v $ 0 = True"
    unfolding bead_def
    unfolding first_half_def by simp
  moreover have "second_half ?v $ 0 = False"
    unfolding bead_def
    unfolding second_half_def by simp
  ultimately show ?thesis unfolding bead_def by metis
qed

lemma "\<not> bead (vec 4 (\<lambda>x. True))"
  unfolding bead_def
  unfolding first_half_def
  unfolding second_half_def
  unfolding dim_vec
  by auto

lemma "\<not> bead (vec 8 (\<lambda>x. if x mod 2 = 0 then True else False))"
  unfolding bead_def
  unfolding first_half_def
  unfolding second_half_def
  unfolding dim_vec by (auto) fastforce

lemma
  \<open>0b0000000000000000000011 = 3\<close> (*binary*)
  \<open>0x0000F = 15\<close> (*hexa*)
  by simp_all

definition nat_to_bool_vec :: "nat \<Rightarrow> nat \<Rightarrow> bool vec"
  where "nat_to_bool_vec n k = vec n (\<lambda>i. bit k i)"

value "nat_to_bool_vec 8 5 $ 0 = True"

value "nat_to_bool_vec 8 4 $ 0 = False"

value "nat_to_bool_vec 8 5 $ 1 = False"

value "nat_to_bool_vec 8 1 $ 0 = False"

value "nat_to_bool_vec 8 5 $ 2 = True"

value "nat_to_bool_vec 8 2 $ 0 = False"

definition bead_of_boolean_function 
  :: "nat \<Rightarrow> (bool vec \<Rightarrow> bool) \<Rightarrow> bool vec"
  where "bead_of_boolean_function n f = 
      vec n (\<lambda>i. f (nat_to_bool_vec n i))"

lemma "bead_of_boolean_function 8 (\<lambda>x. True) = vec 8 (\<lambda>i. True)"
  unfolding bead_of_boolean_function_def ..

context boolean_functions
begin


end




end