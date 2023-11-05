theory Simple_Hypergraphs imports Hypergraph_Basics.Hypergraph_Variations
begin

(* This uses the existing graph system locale from my undirected graph library,
which was the base locale with several useful definitions before introducing an edge size constraint *)
locale simple_hypersys = graph_system +
  assumes finV: "finite V"
begin

(* Define any definitions which would benefit from the simpler set syntax *)

definition shdegree :: "'a \<Rightarrow> nat" where
"shdegree v \<equiv> card (incident_edges v)"

definition shdegree_set :: "'a set \<Rightarrow> nat" where
"shdegree_set vs \<equiv> card {e \<in> E. vs \<subseteq> e}"

definition "link_ext x = {s. s \<in> Pow V \<and> x \<notin> s \<and> insert x s \<in> E}"

definition "cost x = {s. s \<in> Pow (V - {x}) \<and> s \<in> E}"

lemma "cost x =  E \<inter> Pow (V - {x})" unfolding cost_def by auto

end

lemma (in simple_hypersys) shows "E \<subseteq> Pow V"
  by (simp add: subsetI wellformed)

lemma (in simple_hypersys) shows "finite V" using finV .

lemma (in simple_hypersys) shows "finite E" 
  using finV wellformed subsetI
  by (metis PowI finite_Pow_iff finite_Un sup.absorb2)

locale simplicial_complex = simple_hypersys +
  assumes subset_closed: " (\<forall>s\<in>E. \<forall>s'\<subseteq>s. s'\<in> E)"
begin

lemma "simplicial_complex V {}" using finV by unfold_locales (simp+)

lemma assumes v: "V \<noteq> {}" shows "simplicial_complex V {{}}" 
  using v finV by unfold_locales (simp+)

(*there is an additional premise of x being in V:

interpretation l: simplicial_complex "V" "(simple_hypersys.link_ext V E x)"
proof (unfold_locales, unfold link_ext_def, simp, intro finV)*)

lemma assumes x: "x \<in> V" shows "simplicial_complex V (link_ext x)"
  apply (unfold_locales, unfold link_ext_def, simp, intro finV) 
  using subset_closed x
  by (smt (verit, ccfv_SIG) Pow_iff insert_absorb insert_mono insert_subset mem_Collect_eq subset_trans)

lemma assumes x: "x \<in> V" shows "simplicial_complex (V - {x}) (cost x)"
  by (unfold_locales, unfold cost_def, simp, simp add: finV, auto simp add: subset_closed x)

end

lemma (in simplicial_complex)
  shows "simplicial_complex V (simple_hypersys.link_ext V E x)"
  sorry

lemma (in simplicial_complex) 
  shows "simplicial_complex (V - {x}) (simple_hypersys.cost V E x)"
  sorry


lemma
  assumes s: "simplicial_complex V E" 
  shows "simplicial_complex V (simple_hypersys.link_ext V E x)"
  sorry


lemma assumes "finite V" and "K \<subseteq> Pow V" shows "simple_hypersis"

(* In sublocale declaration, include rewrite proofs for equivalent definitions. 
This should help ensure all lemmas related to the more general definition can still be used 
with the set definition replacing the multiset definition automatically. I've included a few examples
of equivalent definitions I can think of, there would likely be more *)

sublocale simple_hypersys \<subseteq> hypersystem V "mset_set E"
  rewrites "hdegree v = shdegree v" and "hedge_neighbourhood v = mset_set (incident_edges v)"
and "hdegree_set vs = shdegree_set vs"
proof -
  interpret hypersystem V "mset_set E"
    by unfold_locales (simp add: wellformed finE) 
  show "hypersystem V (mset_set E)" by unfold_locales
  show "hdegree v = shdegree v" 
    unfolding hdegree_def shdegree_def incident_edges_def vincident_def using finE by auto
  show "hedge_neighbourhood v = mset_set (incident_edges v)"
    unfolding hedge_neighbourhood_def incident_edges_def vincident_def using finE by auto
  show "hdegree_set vs = shdegree_set vs"
    unfolding hdegree_set_def shdegree_set_def using finE by auto
qed

(* You can also now connect this to other locales *)

(* E.g. assuming you still want the additional hypergraph condition of no empty edges *)

locale simple_hypgraph = simple_hypersys + 
  assumes edges_nempty: "e \<in> E \<Longrightarrow> e \<noteq> {}"

sublocale simple_hypgraph \<subseteq> hypergraph V "mset_set E"
  using edges_nempty finE by unfold_locales simp

(* Or adding finiteness assumptions - see the fin graph system locale *)

sublocale fin_graph_system \<subseteq> simple_hypersys
  apply unfold_locales using fin_edges by simp

locale fin_simple_hypgraph = simple_hypgraph + fin_graph_system

sublocale fin_simple_hypgraph \<subseteq> fin_hypergraph V "mset_set E"
  by (unfold_locales)


(*Or to model a kuniform simple hypergraph - each edge having the same size *)

locale simple_uni_hypgraph = simple_hypgraph + 
  assumes edges_nempty: "e \<in> E \<Longrightarrow> e \<noteq> {}"

sublocale simple_hypgraph \<subseteq> hypergraph V "mset_set E"
  using hypergraph_axioms by simp

(* Note the above could also be done directly like this, but it would mean 
your unformity condition uses "mset_set E". It is a tradeoff between adding more locales/sublocales,
and simplicity in the fact - up to the user 
locale simple_uni_hyperpgraph = simple_hypgraph + kuniform_hypergraph V "mset_set E"
*)

(* This could also be connected back to the simple design locale to benefit from proofs/lemmas there
- rewrites might be worth adding to the below proof *)

sublocale fin_simple_hypgraph \<subseteq> simple_design V "mset_set E"
  using finE by unfold_locales simp

end