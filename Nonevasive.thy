
theory Nonevasive
  imports
    "BDT"
begin

function nonevasive :: "nat set \<Rightarrow> nat set set \<Rightarrow> bool"
  where
  "V = {} \<Longrightarrow> nonevasive V K = False"
  | "V = {x} \<Longrightarrow> K = {} \<Longrightarrow> nonevasive V K = True"
  | "V = {x} \<Longrightarrow> K = {{},{x}} \<Longrightarrow> nonevasive V K = True"
  | "V = {x} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{},{x}} \<Longrightarrow> nonevasive V K = False"
  (*This can be proven from the definition: | "2 \<le> card V \<Longrightarrow> K = {} \<Longrightarrow> nonevasive V K = True"*)
  | "2 \<le> card V \<Longrightarrow> nonevasive V K =
    (\<exists>x\<in>V. nonevasive (V - {x}) (link_ext x V K) \<and> nonevasive (V - {x}) (cost x V K))"
  | "\<not> finite V \<Longrightarrow> nonevasive V K = False"
proof -
  fix P :: "bool" and x :: "(nat set \<times> nat set set)"
  assume ee: "(\<And>V K. V = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and se: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and sc: "(\<And>V xa K. V = {xa} \<Longrightarrow> K = {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)" 
      and sn: "(\<And>V xa K. V = {xa} \<Longrightarrow> K \<noteq> {} \<Longrightarrow> K \<noteq> {{}, {xa}} \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and en2: "(\<And>V K. 2 \<le> card V \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
      and inf: "(\<And>V K. infinite V \<Longrightarrow> x = (V, K) \<Longrightarrow> P)"
  show P
  proof (cases "finite (fst x)")
    case False
    show P
      by (rule inf [of "fst x" "snd x"], intro False) auto
  next
    case True note finitex = True
    show P
    proof (cases "fst x = {}")
      case True note ve = True
      show P using ee True by (metis eq_fst_iff)
      next
      case False
      note vne = False
      show P
      proof (cases "card (fst x) = 1")
        case True then obtain xa where f: "fst x = {xa}" by (rule card_1_singletonE)
        show P
        proof (cases "snd x = {}")
          case True
          show P
            by (rule se [of "fst x" xa "snd x"], intro f, intro True) simp
          next
          case False note kne = False
          show P
          proof (cases "snd x = {{},{xa}}")
            case True
            show P
              by (rule sc [of "fst x" xa "snd x"], intro f, intro True) simp
          next
            case False
            show P
              by (rule sn [of "fst x" xa "snd x"], intro f, intro kne, intro False) simp
          qed
        qed
      next
        case False
        have card2: "2 \<le> card (fst x)" using finitex vne False
          by (metis One_nat_def Suc_1 card_gt_0_iff le_SucE not_less not_less_eq_eq)
        show P using en2 [of "fst x" "snd x"] card2 False by simp
         qed
      qed
    qed
qed (auto)
termination proof (relation "Wellfounded.measure (\<lambda>(V,K). card V)")
  show "wf (measure (\<lambda>(V, K). card V))" by simp
  fix V :: "nat set" and K :: "nat set set" and x :: "nat"
  assume c: "2 \<le> card V" and x: "x \<in> V"
  show "((V - {x}, cost x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c  x by simp
  show "((V - {x}, link_ext x V K), V, K) \<in> measure (\<lambda>(V, K). card V)"
    using c  x by simp
qed

lemma v_ge_2: assumes two: "2 \<le> card V" shows "nonevasive V {}"
  using two proof (induct "card V" arbitrary: V)
  case 0
  fix V :: "nat set"
  assume "0 = card V" and "2 \<le> card V"
  hence False by linarith
  thus "nonevasive V {}" by fast
next
  case (Suc n)
  assume two: "2 \<le> card V"
  then obtain x where x: "x \<in> V" by fastforce
  have n: "nonevasive (V - {x}) {}"
  proof (cases "2 \<le> card (V - {x})")
    case True
    show ?thesis
    proof (rule Suc.hyps (1))
      show "n = card (V - {x})" using Suc.hyps (2) using x by simp
      show "2 \<le> card (V - {x})" using True .
    qed
  next
    case False hence "card (V - {x}) = 1" using x two Suc.hyps (2) by simp
    then obtain y where V: "V - {x} = {y}" using card_1_singletonE by auto
    show ?thesis unfolding V using nonevasive.simps (2) by simp
  qed
  show "nonevasive V {}"
    unfolding nonevasive.simps (5) [OF two, of "{}"]
    using two link_ext_empty [of _ V] cost_empty [of _ V] n x by auto
qed

lemma assumes "V \<noteq> {}"  and f: "finite V" shows "nonevasive V {}"
  using v_ge_2 nonevasive.simps (2) f
  by (metis Suc_leI assms(1) card_1_singleton_iff card_gt_0_iff nle_le not_less_eq_eq numerals(2))

lemma nonevasiveI1:
  assumes v: "V = {x}" and k: "K = {{},{x}}"
  shows "nonevasive V K"
  using nonevasive.simps (3) [OF v k] by fast

lemma nonevasiveI2:
  assumes v: "2 \<le> card V" and kne: "K \<noteq> {}"
    and k: "(\<exists>x\<in>V. nonevasive (V - {x}) (link_ext x V K) \<and> nonevasive (V - {x}) (cost x V K))"
  shows "nonevasive V K"
  unfolding nonevasive.simps (5) [OF v] using k .

lemma assumes c: "cone {x} K" shows "K = {{x},{}} \<or> K = {}"
  using c unfolding cone_def powerset_def by (cases "K = {}", auto)

lemma cone_nonevasive: 
  assumes f: "finite V" and c: "cone V K" shows "nonevasive V K"
using c f proof (induct "card V" arbitrary: V K)
   case 0
   from "0.hyps" and finite have "V = {}" by (simp add: "0.prems"(2))
   then have False using "0.prems" (1) unfolding cone_def by simp 
   thus ?case by (rule ccontr)
 next
   case (Suc n)
   from `cone V K` obtain x T
     where K: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" and T: "T \<subseteq> powerset (V - {x})" 
       and x: "x \<in> V" unfolding cone_def by auto
   show ?case
   proof (cases "n = 0")
     case True
     hence "card V = 1" using Suc.hyps (2) by simp
     hence v: "V = {x}" using x using card_1_singletonE [OF `card V = 1`] by auto
     hence t: "T = {{}} \<or> T = {}" using T unfolding powerset_def by auto
     show ?thesis
     proof (cases "T = {}")
       case True
       show ?thesis unfolding v K True using nonevasive.simps (2) by simp
     next
       case False note tne = False
       show ?thesis
       proof (cases "T = {{}}")
        case True
        show ?thesis unfolding v K True using nonevasive.simps (3)
          by (simp add: insert_commute)
       next
        case False with tne and t have False by simp
        thus ?thesis by (rule ccontr)
       qed
     qed
   next
    case False
    hence "2 \<le> Suc n" by simp
    hence two: "2 \<le> card V" using Suc.hyps (2) by simp
    from two obtain y where y: "y \<in> V" and ynex: "y \<noteq> x" and xvy: "x \<in> V - {y}"
      using x Suc.prems (2)
      by (metis card_le_Suc0_iff_eq insertE insert_Diff not_less_eq_eq numeral_2_eq_2)
    have lp: "link_ext y (V - {x}) T \<subseteq> powerset (V - {y} - {x})"
      using T unfolding link_ext_def powerset_def by auto
    have cp: "cost y (V - {x}) T \<subseteq> powerset (V - {y} - {x})"
      using T unfolding cost_def powerset_def by auto
    show ?thesis unfolding nonevasive.simps (5) [OF two]
    proof (rule bexI [OF _ y], rule conjI)
      show "nonevasive (V - {y}) (link_ext y V K)"
      proof (rule Suc.hyps(1))
        show "n = card (V - {y})" using y Suc.hyps (2) by simp
        show "cone (V - {y}) (link_ext y V K)"
          unfolding link_ext_cone_eq [OF x ynex [symmetric] T K]
          unfolding cone_def
          by (rule bexI [OF _ xvy], rule exI [of _ "link_ext y (V - {x}) T"], rule conjI) 
            (intro lp, fast)
        show "finite (V - {y})" using `finite V` by fast
      qed
      show "nonevasive (V - {y}) (cost y V K)"
      proof (rule Suc.hyps(1))
        show "n = card (V - {y})" using y Suc.hyps (2) by simp
        show "cone (V - {y}) (cost y V K)"
          unfolding cost_cone_eq [OF x ynex [symmetric] T K]
          unfolding cone_def
          by (rule bexI [OF _ xvy], rule exI [of _ "cost y (V - {x}) T"], rule conjI)
            (intro cp, fast)
        show "finite (V - {y})" using `finite V` by fast
      qed
    qed
  qed
qed

lemma
  zerocollapsible__nonevasive:
  assumes f: "finite V" and z: "zero_collapsible V K" shows "nonevasive V K"
using z f proof (induct "card V" arbitrary: V K)
   case 0
   from "0.hyps" and finite have "V = {}" by (simp add: "0.prems"(2))
   then have False using "0.prems" (1) unfolding cone_def by simp 
   thus ?case by (rule ccontr)
 next
   case (Suc n)
   (*from `cone V K` obtain x T
     where K: "K = T \<union> {s. \<exists>t\<in>T. s = insert x t}" and T: "T \<subseteq> powerset (V - {x})" 
       and x: "x \<in> V" unfolding cone_def by auto*)
   show ?case
   proof (cases "n = 0")
     case True
     hence "card V = 1" using Suc.hyps (2) by simp
     then obtain x where v: "V = {x}" using card_1_singletonE [OF `card V = 1`] by auto
     show ?thesis
     proof (cases "K = {}")
       case True
       show ?thesis unfolding v True using nonevasive.simps (2) by simp
     next
       case False note tne = False
       show ?thesis
       proof (cases "K = {{}, {x}}")
        case True
        show ?thesis unfolding v True using nonevasive.simps (3)
          by (simp add: insert_commute)
       next
         case False 
         have False using zero_collapsible.simps (4) [OF v tne False] 
           using Suc.prems (1) by simp
         thus ?thesis by (rule ccontr)
       qed
     qed
   next
    case False
    hence "2 \<le> Suc n" by simp
    hence two: "2 \<le> card V" using Suc.hyps (2) by simp
    obtain x where x: "x \<in> V" and cl: "cone (V - {x}) (link_ext x V K)" 
      and ccc: "zero_collapsible (V - {x}) (cost x V K)" and xxne: "V - {x} \<noteq> {}"
      using zero_collapsible.simps (5) [OF two, of K]
      by (metis Suc.prems(1) zero_collapsible.simps(1))
    show ?thesis
    proof (unfold nonevasive.simps (5) [OF two, of K], rule bexI [OF _ x], rule conjI)
      show "nonevasive (V - {x}) (cost x V K)" 
      proof (rule Suc.hyps)
        show "n = card (V - {x})" using x `Suc n = card V` by simp
        show "zero_collapsible (V - {x}) (cost x V K)" using ccc .
        show "finite (V - {x})" using `finite V` by simp
      qed
      show "nonevasive (V - {x}) (link_ext x V K)"
      proof (rule cone_nonevasive)
        show "finite (V - {x})" using `finite V` by simp
        show "cone (V - {x}) (link_ext x V K)" using cl .
      qed
    qed
  qed
qed

lemma
  sorted_variables_remove:
  assumes vl: "(V, l) \<in> sorted_variables" and x: "x \<in> V" and f: "finite V"
  shows "(V - {x}, remove1 x l) \<in> sorted_variables"
  using vl x f proof (induct "card V" arbitrary: V l)
  case 0 from "0.hyps" "0.prems" (3) have "V = {}" by simp
  with "0.prems" (2) have False by fast
  thus "(V - {x}, remove1 x l) \<in> sorted_variables" by (rule ccontr)
next
  case (Suc n)
  from Suc.prems (1) obtain A l' y where v: "V = insert y A" and l: "l = y # l'" 
      and al: "(A, l') \<in> sorted_variables" and y: "y \<notin> A"
    using sorted_variables.simps [of V l] using `x \<in> V` by auto
  show "(V - {x}, remove1 x l) \<in> sorted_variables"
  proof (cases "V - {x} = {}")
    case True hence v: "V = {x}" using `x \<in> V` by auto hence l: "l = [x]"
      using \<open>(V, l) \<in> sorted_variables\<close> \<open>V = insert y A\<close> \<open>l = y # l'\<close> 
      using sorted_variables_length_coherent by fastforce
    show ?thesis unfolding v l
      by (simp add: sorted_variables.intros(1))
  next
    case False note vxne = False
    show ?thesis
    proof (cases "x = y")
      case True
      show ?thesis unfolding True unfolding v l using al y by simp
    next
      case False
      have yax: "y \<notin> A - {x}" using False \<open>V = insert y A\<close> using y by blast
      have vx: "V - {x} = insert y (A - {x})" using \<open>V = insert y A\<close> y False by auto
      have rxl: "remove1 x l = y # (remove1 x l')" using \<open>l = y # l'\<close> False by simp
      have axr: "(A - {x}, remove1 x l') \<in> sorted_variables"
      proof (rule Suc.hyps (1))
        show "n = card A" using \<open>V = insert y A\<close> y \<open>Suc n = card V\<close> `finite V`
          by auto
        show "(A, l') \<in> sorted_variables" by (rule al)
        show "x \<in> A" using `x \<in> V` \<open>V = insert y A\<close> y False by simp
        show "finite A" using `finite V` \<open>V = insert y A\<close> by simp
      qed
      show ?thesis unfolding vx rxl
        by (intro sorted_variables.intros (2), rule axr, rule yax)
    qed
  qed
qed

lemma
  assumes k: "K \<subseteq> powerset V" and vl: "(V, l) \<in> sorted_variables"
    and f: "finite V"
    and ene: "evaluation l K \<in> not_evaders" and x: "x \<in> V"
  shows "evaluation (remove1 x l) (link_ext x V K) \<in> not_evaders"
  using k vl f ene x proof (induct "card V" arbitrary: V l K)
  case 0 have v: "V = {}" using "0.hyps" "0.prems"(3) by force
  hence False using `x \<in> V` by fast 
  thus "evaluation (remove1 x l) (link_ext x V K) \<in> not_evaders" by (rule ccontr)
next
  case (Suc n) thm evaluation.simps
  
  hence "l = []" using "Suc.prems"(5) by auto
  have "K = {} \<or> K = {{}}" using v "0.prems" (1) try
    using "0.prems"(5) by auto
  from evaluation.simps

lemma
  assumes k: "K \<subseteq> powerset V" and vl: "(V, l) \<in> sorted_variables"
    and ene: "evaluation l K \<in> not_evaders" and x: "x \<in> V"
  shows "(V - {x}, remove1 x l) \<in> sorted_variables"
    and "evaluation (remove1 x l) (link_ext x V K) \<in> not_evaders"
proof -
  from vl obtain A l' y where v: "V = insert y A" and l: "l = y # l'" 
      and al: "(A, l') \<in> sorted_variables" and y: "y \<notin> A"
    using sorted_variables.simps [of V l] using x by auto
  have "(V - {x}, remove1 x l) \<in> sorted_variables"
  proof (cases "V - {x} = {}")
    case True hence v: "V = {x}" using x by auto hence l: "l = [x]" 
      using vl using \<open>V = insert y A\<close> \<open>l = y # l'\<close> sorted_variables_length_coherent 
      by fastforce
    show ?thesis unfolding v l
      by (simp add: sorted_variables.intros(1))
  next
    case False note vxne = False
    show ?thesis
    proof (cases "x = y")
      case True
      show ?thesis unfolding True unfolding v l using al y by simp
    next
      case False
      have vx: "V - {x} = insert y (A - {x})" using \<open>V = insert y A\<close> y False by auto
      have rxl: "remove1 x l = y # (remove1 x l')" using \<open>l = y # l'\<close> False by simp
      have "(A - {x}, remove1 x l') \<in> sorted_variables"
      show ?thesis unfolding vx rxl
      proof (intro sorted_variables.intros (2))
        show "(A - {x}, remove1 x l') \<in> sorted_variables" 
          using al using sorted_variables.intros

    have "(V - {x}, remove1 x l) \<in> sorted_variables"
    using vl x using sorted_variables.simps
    using False remove1_idem sorted_variables_coherent vl by fastforce
  have "K = link_ext x V K" using False k unfolding link_ext_def powerset_def apply auto try

lemma assumes k: "K \<subseteq> powerset V" and x: "V \<noteq> {}" and f: "finite V" 
  and l: "\<exists>l. (V, l) \<in> sorted_variables \<and> evaluation l K \<in> not_evaders"
  shows "nonevasive V K"
  using x k f l proof (induct "card V" arbitrary: V K)
  case 0 have v: "V = {}" using "0.prems" (3) "0.hyps" by simp  
  hence False using "0.prems" (1) by fast
  thus "nonevasive V K" by (rule ccontr)
next
  case (Suc n)
  show "nonevasive V K"
  proof (cases "n = 0")
    case True
    then obtain x where v: "V = {x}" using Suc.hyps (2)
      by (metis One_nat_def card_1_singletonE)
    show ?thesis
    proof (cases "K = {} \<or> K = {{x}, {}}")
      case True
      show ?thesis using True using nonevasive.simps (2,3) [OF v, of K] by blast
    next
      case False
      have k: "K = {{x}} \<or> K = {{}}"
        unfolding powerset_def using v using False
        by (metis Suc.prems(2) doubleton_eq_iff powerset_singleton_cases)
      from Suc.prems (4)
      obtain l where vl: "(V, l) \<in> sorted_variables" and el: "evaluation l K \<in> not_evaders"
        by auto
      have l: "l = [x]"
        using sorted_variables_coherent [OF vl]
        using sorted_variables_length_coherent [OF vl]
        unfolding v
        by (metis card_1_singleton_iff empty_iff length_0_conv length_Suc_conv list.set(1) list.set_intros(1) list.simps(15) set_ConsD)
      show ?thesis
      proof (cases "K = {{x}}")
        case True
        have "evaluation l K = [True, False]"
          unfolding l True
          unfolding evaluation.simps link_ext_def cost_def powerset_def
          using evaluation.simps (1,2) using v apply auto
          by (smt (verit, ccfv_threshold) Suc.prems(1) append.left_neutral append_Cons bot.extremum emptyE empty_Collect_eq evaluation.simps(1) evaluation.simps(2))
        hence "evaluation l K \<notin> not_evaders"
          using tf_not_not_evader by simp
        hence False using el by simp
        thus ?thesis by (rule ccontr)
      next
        case False hence k: "K = {{}}" using k by fast
        have "evaluation l K = [False, True]"
          unfolding l k
          unfolding evaluation.simps link_ext_def cost_def powerset_def
          using evaluation.simps (1,2) using v by auto
        hence "evaluation l K \<notin> not_evaders"
          using ft_not_not_evader by simp
        hence False using el by simp
        thus ?thesis by (rule ccontr)
      qed
    qed
  next
    case False
    hence two: "2 \<le> card V" using Suc.hyps (2) by simp
    obtain x where x: "x \<in> V" using two by fastforce
    have ne_link: "nonevasive (V - {x}) (link_ext x V K)"
    proof (rule Suc.hyps (1))
      show "n = card (V - {x})" using x Suc.hyps (2) by simp
      show "V - {x} \<noteq> {}" using False \<open>n = card (V - {x})\<close> by force
      show "link_ext x V K \<subseteq> powerset (V - {x})" 
        using Suc.prems (2)
        using link_ext_def powerset_def by force
      show "finite (V - {x})" using Suc.prems(3) by blast
      show "\<exists>l. (V - {x}, l) \<in> sorted_variables \<and> evaluation l (link_ext x V K) \<in> not_evaders"
        using Suc
    from Suc
    show "nonevasive V K" unfolding nonevasive.simps (5) [OF two, of K]
  hence k: "K = {} \<or> K = {{}}" using "0.prems" (1) unfolding powerset_def by auto
  show "nonevasive V K" unfolding v using k using nonevasive.simps



end