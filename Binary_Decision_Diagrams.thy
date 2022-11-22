
theory Binary_Decision_Diagrams
  imports
    "ROBDD.Bool_Func"
begin

(*datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex*)

datatype ifex = CIF bool | IF nat ifex ifex

primrec valif :: "ifex => (nat => bool) => bool"
  where
  "valif (CIF b)    env = b" |
  "valif (IF b f t) env = (if env b then valif f env
                                      else valif t env)"

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
  "vars (IF v f t) =  insert v (vars f \<union> vars t)" |
  "vars (CIF b) = {}"

fun ifex_unique_var :: "ifex \<Rightarrow> bool"
  where
    "ifex_unique_var (CIF b) = True" |
    "ifex_unique_var (IF n f t) = (n \<notin> vars t \<and> n \<notin> vars f)"


lemma "ifex_unique_var (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False)))" by simp

lemma "\<not> ifex_unique_var (IF 3 (IF 3 (CIF True) (CIF False))
                         (IF 3 (CIF True) (CIF False)))" by simp



fun depth :: "ifex \<Rightarrow> nat"
  where 
    "depth (CIF b) = 0" |
    "depth (IF b f t) = 1 + min (depth f) (depth t)" 

lemma "depth (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False))) = 2" by simp

text\<open>Pending definition\<close>

fun reduce :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> ifex"
  where
    "reduce (CIF b) env = CIF b" |
    "reduce (IF a f t) env = (if f = t then (reduce f env) else IF a (reduce f (env(a:=True)))
                               (reduce t (env(a:=False))))"

value "reduce (IF 1 (IF 2 (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF 4 (CIF True) (CIF False)))
                           (IF 3 (IF 4 (CIF True) (CIF False)) 
                                 (IF  4 (CIF True) (CIF False))))
                           (IF 4 (CIF True) (CIF False))) (\<lambda>x. if x = 3 then False else True)"

lemma
  assumes "depth (IF a t f) = n"
    and "a \<in> vars t"
  shows "True"


end