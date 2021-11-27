
theory ListLexorder
imports Main
begin

(* There's probably an easier way to get a sorted list of lists from a set of lists. Some lexicographic ordering does have to exist. No idea... *)

datatype 'a :: linorder linorder_list = LinorderList "'a list"

definition "linorder_list_unwrap L \<equiv> case L of LinorderList L \<Rightarrow> L" (* Meh, there is a way to get datatype to generate this. I forgot *)

fun less_eq_linorder_list_pre where
  "less_eq_linorder_list_pre (LinorderList []) (LinorderList []) = True" |
  "less_eq_linorder_list_pre (LinorderList []) _ = True" |
  "less_eq_linorder_list_pre _ (LinorderList []) = False" |
  "less_eq_linorder_list_pre (LinorderList (a # as)) (LinorderList (b # bs)) 
    = (if a = b then less_eq_linorder_list_pre (LinorderList as) (LinorderList bs) else a < b)"

instantiation linorder_list :: (linorder) linorder
begin
definition "less_linorder_list x y \<equiv> 
              (less_eq_linorder_list_pre x y \<and> \<not> less_eq_linorder_list_pre y x)"
definition "less_eq_linorder_list x y \<equiv> less_eq_linorder_list_pre x y"
instance
  apply standard
  apply(unfold less_eq_linorder_list_def less_linorder_list_def)
  subgoal by simp
  subgoal
    apply(induction)
    subgoal for x
      apply(induction x; simp)
      done
    done
  subgoal for x y z
    apply(induction x z arbitrary: y rule: less_eq_linorder_list_pre.induct; simp)
     apply (metis less_eq_linorder_list_pre.simps(3) linorder_list.exhaust neq_Nil_conv)
    apply (smt (verit, ccfv_threshold) 
            less_eq_linorder_list_pre.elims(2) less_eq_linorder_list_pre.simps(4) 
            less_trans not_less_iff_gr_or_eq)
    done
  subgoal for x y 
    by(induction x y rule: less_eq_linorder_list_pre.induct; simp split: if_splits)
  subgoal for x y 
    by(induction x y rule: less_eq_linorder_list_pre.induct; auto)
  done
end

definition "sorted_list_of_list_set L \<equiv> 
  map linorder_list_unwrap (sorted_list_of_set (LinorderList ` L))"

lemma set_sorted_list_of_list_set[simp]: 
  "finite L \<Longrightarrow> set (sorted_list_of_list_set L) = L"
  by(force simp add: sorted_list_of_list_set_def linorder_list_unwrap_def)

end