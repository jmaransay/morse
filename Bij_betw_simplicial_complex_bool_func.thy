
theory Bij_betw_simplicial_complex_bool_func
  imports 
    Simplicial_complex
begin

section\<open>Bijection between simplicial complexes and Boolean functions\<close>

text\<open>Proposition 6.16 in Scoville\<close>

definition boolean_function_from_simplicial_complex :: "('n::finite) set set => (bool^'n => bool)"
  where "boolean_function_from_simplicial_complex K = (\<lambda>x. True)"

declare [[show_types]]
declare [[show_consts]]
lemma shows "bij_betw simplicial_complex_induced_by_monotone_boolean_function UNIV UNIV"
proof (intro bij_betwI [of _ _ _ boolean_function_from_simplicial_complex], simp+)

qed

end