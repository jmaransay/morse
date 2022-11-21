
theory Binary_Decision_Diagrams
  imports "HOL.Main"
begin

(*datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex*)

datatype ifex = CIF bool | IF nat ifex ifex

primrec valif :: "ifex => (nat => bool) => bool"
  where
  "valif (CIF b)    env = b" |
  "valif (IF b t e) env = (if env b then valif t env
                                      else valif e env)"

(*primrec valif :: "ifex => (nat => bool) => bool"
  where
  "valif (CIF b)    env = b" |
  "valif (VIF x)    env = env x" |
  "valif (IF b t e) env = (if valif b env then valif t env
                                      else valif e env)"
*)

lemma "valif (CIF True) f" by simp

lemma "\<not> valif (CIF False) f" by simp

(*lemma "valif (VIF 3) (\<lambda>x. True)" by simp*)

(*lemma "\<not> valif (VIF 3) (\<lambda>x. False)" by simp*)

lemma "valif (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp

(*lemma "valif (IF (VIF 3) (IF (VIF 3) (CIF True) (CIF False))
                         (IF (VIF 3) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp*)

(*lemma "\<not> valif (IF (VIF 3) (IF (VIF 2) (CIF True) (CIF False))
                         (IF (VIF 4) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp*)

lemma "\<not> valif (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False)))
              (\<lambda>x. if x = 2 then True else False)" by simp

(*lemma "\<not> valif (IF (VIF 3) (IF (VIF 3) (CIF True) (CIF False))
                         (IF (VIF 3) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 2 then True else False)" by simp*)

lemma "\<not> valif (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False)))
              (\<lambda>x. if x = 3 then True else False)" by simp

(*lemma "\<not> valif (IF (VIF 1) (IF (VIF 2) (IF (VIF 3) (IF (VIF 4) (CIF True) (CIF False)) 
                                                   (IF (VIF 4) (CIF True) (CIF False)))
                                       (IF (VIF 3) (IF (VIF 4) (CIF True) (CIF False)) 
                                                   (IF (VIF 4) (CIF True) (CIF False))))
                           (IF (VIF 4) (CIF True) (CIF False))) 
              (\<lambda>x. if x = 3 then True else False)" by simp*)


fun vars :: "ifex \<Rightarrow> nat set" 
  where
  "vars (IF v t f) =  insert v (vars t \<union> vars f)" |
  "vars (CIF True) = {}" |
  "vars (CIF False) = {}"


fun ifex_unique_var :: "ifex \<Rightarrow> bool"
  where 
    "ifex_unique_var (CIF True) = True"  |
    "ifex_unique_var (CIF False) = True" |
    "ifex_unique_var (IF n t f) = (n \<notin> vars t \<and> n \<notin> vars f)"



lemma "ifex_unique_var (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False)))" by simp

lemma "\<not> ifex_unique_var (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False)))" by simp

end

