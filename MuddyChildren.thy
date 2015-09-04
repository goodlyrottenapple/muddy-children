theory MuddyChildren
imports Main DEAKDerivedRules "calculus/src/isabelle/DEAK_SE" NatToString
begin

(*
Implements and follows closely the proof of Proposition 24 in (Ma-Palmigiano-Sadrzadeh, 2014), 
referred to in the comments below as [MPS].
We consider classical logic and define clean as the negation of dirty.
*)

(* as upto is not defined for nats in isabelle core theories, we introduce a sugar notation for constructing a list of nats from x to y: [[x .. y]] *)
fun upto' :: "nat \<Rightarrow> nat \<Rightarrow> nat list" ("[[_ .. _]]") where
"upto' x 0 = (if x = 0 then [0] else [])" |
"upto' x (Suc y) = (if x \<le> (Suc y) then (if x = Suc y then [Suc y] else (Suc y) # (upto' x y)) else [])"

lemma upto'_simp1[simp]: "x \<le> y \<Longrightarrow> set ([[x .. y]]) = {x..y}"
by (induct y, auto)

lemma upto'_simp2[simp]: "x > y \<Longrightarrow> set ([[x .. y]]) = {x..y}"
by (induct y, auto)

(* E f := \<And>n i=1 fboxK i f. The intended meaning of the defined connective E is ‘Everybody knows’ *)
fun E :: "nat \<Rightarrow> Formula \<Rightarrow> Formula" where
"E 0 formula = \<top>\<^sub>F" |
"E (Suc x) formula = (fboxK\<^sub>F (`Suc x`) formula) \<and>\<^sub>F (E x formula)"

lemma E_der_simp: 
  fixes x A
  shows "\<And>i. 0 < i \<and> i \<le> (Suc x) \<Longrightarrow> loc \<turnstile>d ( E (Suc x) A )\<^sub>S \<turnstile>\<^sub>S ( fboxK\<^sub>F `i` A )\<^sub>S"
proof(induct x)
case 0 
  then have i_eq_1: "i = Suc 0" by simp
  show ?case
  apply (subst i_eq_1)+
  unfolding E.simps
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  by (rule Id)
next
case (Suc x)
  thus ?case
  proof (cases "i \<le> Suc x")
  case goal1 
    then have assm: "loc \<turnstile>d E (Suc x) A \<^sub>S \<turnstile>\<^sub>S fboxK\<^sub>F `i` A \<^sub>S" by simp
    thus ?case 
    apply (subst E.simps)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impL_disp2)
    apply (rule_tac derivable.W_impL_L)
    by simp
  next
  case goal2 
    then have assm: "i = Suc (Suc x)" by simp
    thus ?case
    apply (subst E.simps)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    apply (subst assm)
    by (rule Id)
  qed
qed

lemma E_der_simp2:
  assumes "\<And>ag. LAgent ag \<in> set loc"
  shows "\<And>x A. loc \<turnstile>d ( E (Suc x)\<^sup>y A )\<^sub>S \<turnstile>\<^sub>S ( A )\<^sub>S"
apply(induct y)
unfolding k_apply.simps
apply (rule Id)
apply (subst E.simps)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac a="`Suc x`" in derivable.Refl_ForwK)
using assms apply simp
apply (rule_tac derivable.FboxK_L)
by simp

definition father :: "nat \<Rightarrow> Formula" where
"father n = \<Or>\<^sub>F map (Formula_Atprop \<circ> nat_to_string) [[1 .. n]]"

(* vision expresses the fact that every child knows whether each other child is clean or dirty *)
fun vision_aux :: "nat \<Rightarrow> nat \<Rightarrow> Formula list" where
"vision_aux _ 0 = []" |
"vision_aux m (Suc n) = (
  ((`m` \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (`Suc n`) (`m` \<^sub>F))) \<and>\<^sub>F 
  (((`m` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (`Suc n`) ((`m` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
)
#
(
  (((`Suc n`) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F `m` ((`Suc n`) \<^sub>F))) \<and>\<^sub>F 
  ((((`Suc n`) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F `m` (((`Suc n`) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
)
# vision_aux m n"

fun vision' :: "nat \<Rightarrow> Formula list" where
"vision' 0 = []" |
"vision' (Suc x) = (vision_aux (Suc x) x) @ (vision' x)"

definition vision :: "nat \<Rightarrow> Formula" where
"vision x = \<And>\<^sub>F (vision' x)"

lemma vision_aux_contains1 :
  assumes "0 < i \<and> i < (Suc x)"
  shows "\<And> ii. 0 < ii \<and> ii < i \<Longrightarrow> (
   (((`Suc x`) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F `ii` ((`Suc x`) \<^sub>F))) \<and>\<^sub>F 
   ((((`Suc x`) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F `ii` (((`Suc x`) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
  )
   \<in> set (vision_aux (Suc x) i)"
using assms proof (induction x i rule: vision_aux.induct)
case 1 thus ?case by auto
next
case (2 m n)
  show ?case
  apply(cases "ii < n")
  proof -
  case goal1
    with 2 show ?case by simp
  next
  case goal2
    then have "ii \<ge> n" by simp
    from 2 have "ii \<le> n" by simp
    then have i_def: "ii = n" by (simp add: `n \<le> ii` dual_order.antisym)
    then obtain n' where n'_def: "n = Suc n'" by (metis "2.prems"(1) Suc_pred)
    show ?case 
    unfolding i_def vision_aux.simps
    apply(subst (9) n'_def)
    unfolding vision_aux.simps using n'_def by simp
  qed
qed

lemma vision_aux_contains2 :
  assumes "0 < i \<and> i < (Suc x)"
  shows "\<And> ii. 0 < ii \<and> ii < i \<Longrightarrow> (
   ((`ii` \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (`Suc x`) (`ii` \<^sub>F))) \<and>\<^sub>F 
   (((`ii` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (`Suc x`) ((`ii` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
  )
   \<in> set (vision_aux (Suc x) i)"
using assms proof (induction x i rule: vision_aux.induct)
case 1 thus ?case by auto
next
case (2 m n)
  show ?case
  apply(cases "ii < n")
  proof -
  case goal1
    with 2 show ?case by simp
  next
  case goal2
    then have "ii \<ge> n" by simp
    from 2 have "ii \<le> n" by simp
    then have i_def: "ii = n" by (simp add: `n \<le> ii` dual_order.antisym)
    then obtain n' where n'_def: "n = Suc n'" by (metis "2.prems"(1) Suc_pred)
    show ?case 
    unfolding i_def vision_aux.simps
    apply(subst (9) n'_def)
    unfolding vision_aux.simps using n'_def by simp
  qed
qed

lemma vision_contains :
  fixes i j dirty_children num_of_children
  assumes "0 < i \<and> i \<le> num_of_children" "0 < j \<and> j \<le> num_of_children"
  and "i \<noteq> j"
  shows "((`j` \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F `i` (`j` \<^sub>F))) \<and>\<^sub>F 
  (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F `i` ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))) \<in> set (vision' num_of_children)"
using assms apply (induct num_of_children)
apply simp
proof -
case goal1 
  note g1 = goal1
  show ?case
  proof (cases "i \<le> num_of_children" ; cases "j \<le> num_of_children")
  case goal1 
    with g1 have "((`j` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `i` `j` \<^sub>F) \<and>\<^sub>F (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `i` (`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)
    \<in> set (vision' num_of_children)" by simp
    thus ?case unfolding vision'.simps by simp
  next
  case goal2 
    with g1 have j_def: "j = Suc num_of_children" by simp
    with g1 goal2 obtain num' where num'_def: "num_of_children = Suc num'" using Suc_pred less_le_trans by metis
    then have "((`Suc num_of_children` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `i` `Suc num_of_children` \<^sub>F) \<and>\<^sub>F
    (((`Suc num_of_children` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `i` (`Suc num_of_children` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)
    \<in> set (vision_aux (Suc num_of_children) num_of_children)" using g1 goal2 vision_aux_contains1 
    by (metis le_less lessI list.set_intros(1) vision_aux.simps(2) zero_less_Suc)
    thus ?case unfolding j_def vision'.simps by simp
  next
  case goal3 
    with g1 have i_def: "i = Suc num_of_children" by simp
    with g1 goal3 obtain num' where num'_def: "num_of_children = Suc num'" using Suc_pred less_le_trans by metis
    then have "((`j` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `Suc num_of_children` `j` \<^sub>F) \<and>\<^sub>F
    (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `Suc num_of_children` (`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)
    \<in> set (vision_aux (Suc num_of_children) num_of_children)" using g1 goal3 vision_aux_contains2
    by (metis le_less lessI list.set_intros(1) list.set_intros(2) vision_aux.simps(2) zero_less_Suc) 
    thus ?case unfolding i_def vision'.simps by simp
  next
  case goal4 
    with g1 have False by simp
    thus ?case ..
  qed
qed

(* no expresses the ignorance of the children about their own status *)
fun no :: "nat \<Rightarrow> Formula" where
"no 0 = \<top>\<^sub>F"|
"no (Suc x) = ( ( fdiamK\<^sub>F (`Suc x`) (`Suc x`) \<^sub>F )
  \<and>\<^sub>F ( fdiamK\<^sub>F (`Suc x`) (( (`Suc x` ) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) ) ) \<and>\<^sub>F ( no x)"

lemma no_imp: 
  fixes loc
  assumes "0 < i \<and> i \<le> Suc( x)"
  shows " loc \<turnstile>d ( no (Suc x) ) \<^sub>S \<turnstile>\<^sub>S ( ( fdiamK\<^sub>F `i` (`i` ) \<^sub>F ) \<and>\<^sub>F ( fdiamK\<^sub>F `i` ( ( (`i` ) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )) ) \<^sub>S "
using assms apply(induction x)
apply (subst no.simps)+
proof -
case goal1
  have i0: "i = Suc 0" by (simp add: Suc_leI goal1 le_antisym)
  show ?case
  apply(subst i0)+
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  by (rule Id)
next
case goal2
  show ?case
  apply (subst no.simps)
  apply(cases "i\<le> (Suc x)")
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  using goal2(1) goal2(2) apply blast

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  using Id goal2(2) le_SucE by blast
qed

(* the first parameter n encodes the number of children - 
   the second parameter J encodes the list of dirty children which is a subset of {1..n} *)
definition dirty :: "nat \<Rightarrow> nat list \<Rightarrow> Formula " where
"dirty n J = (if \<forall>j \<in> (set J). n \<ge> j \<and> j > 0 then 
  \<And>\<^sub>F (map (Formula_Atprop \<circ> nat_to_string) J) @
     (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) (filter (\<lambda>x. x \<notin> set J) [[1 .. n]])) else \<top>\<^sub>F )"

lemma dirty_vision_der:
  fixes k n J J' j
assumes "0 \<le> (Suc k) \<and> (Suc k) \<le> n" 
  and "set J \<subseteq> {1..n}"
  and "j \<in> set J"
  and "set J' \<equiv> set J - {j}"
  and cut: "\<And>f. CutFormula f \<in> set loc"
shows "loc \<turnstile>d (dirty n J \<^sub>S) ;\<^sub>S (vision n \<^sub>S) \<turnstile>\<^sub>S (fboxK\<^sub>F `j` (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F dirty n J')) \<^sub>S"
proof -
case goal1
  from assms have cond: "\<forall>j\<in>set J. j \<le> n \<and> 0 < j" "\<forall>j\<in>set J'. j \<le> n \<and> 0 < j" by auto

  have 1: "loc \<turnstile>d (\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J') @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J]))) \<^sub>S \<turnstile>\<^sub>S 
    ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J') @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J']))) \<^sub>S"
  apply(rule_tac f= "(\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J'))) \<and>\<^sub>F 
    ((\<And>\<^sub>F (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])))" in derivable.SingleCut)
  using cut apply blast
  apply(rule_tac conj_unfold_2)
  using cut apply blast
  apply(rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply(rule_tac f= "(\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J'))) \<and>\<^sub>F 
    ((\<And>\<^sub>F (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J'])))" in derivable.SingleCut)
  using cut apply blast
  defer
  apply(rule_tac conj_unfold_2b)
  using cut apply blast
  apply (rule_tac derivable.Comma_impR_disp2)
  apply(rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp)
  apply(rule_tac derivable.E_L)
  apply(rule_tac derivable.A_L2)
  apply(rule_tac derivable.And_R)
  defer
  apply(rule_tac conj_der2)
  using cut apply simp
  apply(rule_tac Id)
  using assms apply auto[1]
  apply(rule_tac conj_der1b)
  apply rule
  proof -
  case goal1 thus ?case
    apply (cases "f \<in> set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])")
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    apply(rule_tac f=f in conj_der1)
    apply(rule Id)
    apply blast
    proof -
    case goal1
      then have 0: "f \<in> set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J']) - set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" using Set.DiffI by blast
      from assms have "set [[1 ..n ]] = {1..n}" by simp
      with assms have 1: "set [x\<leftarrow> [[1 .. n]] . x \<notin> set J'] = {1..n} - (set J - {j})" and 2: "set [x\<leftarrow> [[1 .. n]] . x \<notin> set J] = {1..n} - (set J)" by auto
      
      
      from assms have "set J - {j} \<subseteq> {1..n}" "{j} \<subseteq> {1..n}" by auto
      with assms(2,3) have 3: "set [x\<leftarrow> [[1 .. n]] . x \<notin> set J'] - set [x\<leftarrow> [[1 .. n]] . x \<notin> set J] = {j}"
      apply(subst 1)
      apply(subst 2)
      by auto
      
      have "set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J']) - set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J]) =
      image ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) ((set [x\<leftarrow> [[1 .. n]] . x \<notin> set J']) - set [x\<leftarrow> [[1 .. n]] . x \<notin> set J])"
      proof -
        have "\<forall>F f. F \<noteq> {} \<or> (f\<Colon>Formula) \<notin> F"
          by blast
        hence f1: "set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J]) \<noteq> {}"
          using "0" by blast
        have f2: "set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J]) - insert (((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j) (((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) ` {}) = {}"
          by (metis (no_types) Diff_eq_empty_iff `set [x\<leftarrow> [[1 .. n]] . x \<notin> set J'] - set [x\<leftarrow> [[1 .. n]] . x \<notin> set J] = {j}` image_diff_subset image_insert image_set)
        hence f3: "insert (((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j) (set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J]) - {((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j}) = ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) ` {j}"
          by blast
        have "((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j \<in> set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow> [[1 .. n]] . n \<notin> set J])"
          using f2 f1 by blast
        thus ?thesis
          using f3 by (metis `set [x\<leftarrow> [[1 .. n]] . x \<notin> set J'] - set [x\<leftarrow> [[1 .. n]] . x \<notin> set J] = {j}` insert_Diff)
      qed
      
      with 0 3 have f_def: "f = (`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F" by (metis (no_types, lifting) comp_apply imageE singletonD)
      thus ?case
      unfolding f_def
      apply (rule_tac derivable.Comma_impL_disp2)
      apply (rule_tac derivable.W_impL_L)
      by (rule_tac Id)
    qed
  qed

  have subst1: "map ((\<lambda>x. fboxK\<^sub>F `j` x \<^sub>F) \<circ> nat_to_string) J' @ map ((\<lambda>x. fboxK\<^sub>F `j` ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J] = 
    map (\<lambda>x. fboxK\<^sub>F `j` x) (map ((\<lambda>x. x \<^sub>F) \<circ> nat_to_string) J' @ map ((\<lambda>x. ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] .  x \<notin> set J])" by simp

  have subst2: "((\<lambda>x. ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) = ((\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" by (meson comp_apply)
  have subst3: "((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) = (\<lambda>x. (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)" by auto
  have subst4: "((\<lambda>x. fboxK\<^sub>F `j` ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) = (\<lambda>x. fboxK\<^sub>F `j` ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" by (meson comp_apply)
  have subst5: "((\<lambda>x. fboxK\<^sub>F `j` x \<^sub>F) \<circ> nat_to_string) = (\<lambda>x. fboxK\<^sub>F `j` `x` \<^sub>F)" by (meson comp_apply)

  have "loc \<turnstile>d ((\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J) @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J]))) \<^sub>S) ;\<^sub>S (vision n \<^sub>S) \<turnstile>\<^sub>S 
    (fboxK\<^sub>F `j` (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J') @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J']))))) \<^sub>S"
  apply(rule_tac f ="fboxK\<^sub>F `j` (\<And>\<^sub>F map (Formula_Atprop \<circ> nat_to_string) J' @ map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" in SingleCut)
  using cut apply blast
  defer
  using FboxK_L FboxK_R 1 apply blast
  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. fboxK\<^sub>F `j` (x \<^sub>F)) \<circ> nat_to_string) J' @ map ((\<lambda>x. fboxK\<^sub>F `j` ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" in SingleCut)
  using cut apply simp
  defer
  apply(subst subst1)
  apply(rule_tac conj_box_distrib)
  using cut apply simp
  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. fboxK\<^sub>F `j` (x \<^sub>F)) \<circ> nat_to_string) J') \<and>\<^sub>F (\<And>\<^sub>F map ((\<lambda>x. fboxK\<^sub>F `j` ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" in SingleCut)
  using cut apply simp
  defer
  apply(rule_tac conj_unfold_2b)
  using cut apply simp
  apply (rule_tac derivable.Comma_impL_disp2)
  apply(rule_tac f ="(\<And>\<^sub>F map (Formula_Atprop \<circ> nat_to_string) J) \<and>\<^sub>F (\<And>\<^sub>F map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" in SingleCut)
  using cut apply simp
  apply(rule_tac conj_unfold_2)
  using cut apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.A_L2)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.A_L)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.A_L2)
  apply (rule_tac derivable.And_R)

  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. n]] . x \<notin> set J]) \<and>\<^sub>F (\<And>\<^sub>F map ((\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F)) \<and>\<^sub>F (((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" in SingleCut)
  using cut apply simp
  apply (rule_tac derivable.And_R)
  defer
  apply (rule Id)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)

  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F)))) [x\<leftarrow> [[1 .. n]] . x \<notin> set J]) \<and>\<^sub>F (\<And>\<^sub>F map (\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" in SingleCut)
  using cut apply simp
  apply(rule conj_fold)
  using cut apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac derivable.Comma_impR_disp)

  apply(subst subst3)
  apply(subst subst4)
  
  apply(rule_tac conj_impl_fold)
  using cut apply simp

  apply(rule_tac f ="(\<And>\<^sub>F map (\<lambda>x. (`x` \<^sub>F)) J') \<and>\<^sub>F (\<And>\<^sub>F map ((\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F)) \<and>\<^sub>F (((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))) J')" in SingleCut)
  using cut apply simp
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.And_R)
  defer
  apply (rule_tac conj_der2)
  using cut apply simp
  apply (rule Id)
  using assms apply auto[1]
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)

  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F)))) J') \<and>\<^sub>F (\<And>\<^sub>F map (\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` ((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) J')" in SingleCut)
  using cut apply simp
  apply(rule conj_fold)
  using cut apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  apply (rule_tac derivable.Comma_impR_disp)

  apply(subst subst5)
  apply(rule_tac conj_impl_fold)
  using cut apply simp
  unfolding vision_def
  apply(rule_tac conj_der1b)
  apply rule
  apply(rule_tac conj_der1)
  apply(rule Id)
  defer
  apply(rule_tac conj_der1b)
  apply rule
  apply(rule_tac conj_der1)
  apply(rule Id)
  proof -
  case goal1 
    then have 0: "f \<in> image (\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F) \<and>\<^sub>F (((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) (set J')" by (metis list.set_map)
    from assms have "\<forall>x \<in> set J'. 0 < x \<and> x \<le> n" "\<forall>x \<in> set J'. x \<noteq> j" by auto
    then have "\<forall>x \<in> (set J'). ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F) \<and>\<^sub>F (((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<in> set (vision' n)" by (metis (no_types, lifting) assms(3) cond(1) vision_contains)
    with 0 show ?case by blast
  next
  case goal2
    then have 0: "f \<in> image (\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F) \<and>\<^sub>F (((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) (set [x\<leftarrow> [[1 .. n]] . x \<notin> set J])" by (metis list.set_map)
    from assms have "\<forall>x \<in> set [x\<leftarrow> [[1 .. n]] . x \<notin> set J]. 0 < x \<and> x \<le> n" "\<forall>x \<in> set [x\<leftarrow> [[1 .. n]] . x \<notin> set J]. x \<noteq> j" 
    apply (metis One_nat_def Suc_eq_plus1 atLeastAtMost_iff atLeastatMost_empty_iff discrete filter_is_subset insert_Diff insert_not_empty subsetCE upto'_simp1)
    using assms(3) by auto
    then have "\<forall>x \<in> set [x\<leftarrow> [[1 .. n]] . x \<notin> set J]. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F) \<and>\<^sub>F (((`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<in> set (vision' n)" by (metis (no_types, lifting) assms(3) cond(1) vision_contains)
    with 0 show ?case by blast
  qed

  thus ?case unfolding dirty_def using cond by simp
qed

definition preFormula_father :: "nat \<Rightarrow> Locale" where
"preFormula_father n = PreFormula (''father''@`n`) (father n)"

definition preFormula_no :: "nat \<Rightarrow> Locale" where
"preFormula_no n = PreFormula (''no''@`n`) (no n)"

lemma dirtyChildren:
  fixes J::"nat list" and j and n
  assumes "(Suc k) \<le> (Suc n)"
  and "set J \<subseteq> {1..Suc n}"
  and "card (set J) = Suc k"
  and "j \<in> set J"  
  assumes preFather: "\<And>n. preFormula_father (Suc n) \<in> set loc"
  and preNo: "\<And>n. preFormula_no (Suc n) \<in> set loc"
  and rel_refl: "RelAKA rel \<in> set loc" "\<And> alpha a. rel alpha a = ([alpha]::Action list)" 
  and cut: "\<And>f. CutFormula f \<in> set loc"
  and agent: "\<And>agent. LAgent agent \<in> set loc"
  shows "loc \<turnstile>d ((dirty (Suc n) J) \<and>\<^sub>F (k_apply (E (Suc n)) (Suc k) (vision (Suc n))))\<^sub>S \<turnstile>\<^sub>S 
    (fboxA\<^sub>F (''father'' @ `Suc n`) (k_apply (Formula_FboxA (''no'' @ `Suc n`)) k (fboxK\<^sub>F `j` `j` \<^sub>F)) )\<^sub>S"
using assms(1,2,3,4)
proof(induct k arbitrary:j J)
case 0 (* k=0, hence there is Suc k = 1 dirty child, called j, J={j} *)
  then have J_contains: "set J = {j}" using card_eq_SucD by fastforce
  
  have set_eq: "{1..Suc n} - {j} = set ([x \<leftarrow>  [[1 .. Suc n]]. x\<noteq>j])" by auto
  
  have list_eq: "[x\<leftarrow> [[1 .. Suc n]] . x \<notin> set J] = [x\<leftarrow> [[1 .. Suc n]] . x \<noteq> j]" using J_contains by simp
  with 0 have j_range: "0 < j \<and> j \<le> Suc n" by (simp add: J_contains)
  
  have f_subst: "((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) = ((\<lambda>x. (`x` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" by auto
  
  have f_subst2: "\<And>j. (\<lambda>h. ((`h` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `h` \<^sub>F) \<and>\<^sub>F (((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) =
  (\<lambda>h. (\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F)) h \<and>\<^sub>F (\<lambda>y. (((`y` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`y` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) h )" by simp
  
  have f_subst3: "\<And>j. (\<lambda>h. (\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F)) h \<and>\<^sub>F (\<lambda>y. (((`y` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`y` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) h ) = 
  (\<lambda>h. ((`h` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `h` \<^sub>F) \<and>\<^sub>F (((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" by simp
  
  def left \<equiv> "(\<lambda>x. ((`x` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `x` \<^sub>F))"
  def right \<equiv> "(\<lambda>y. (((`y` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`y` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))"
  
  have 1: "\<forall>h \<in> {1..Suc n} - {j}.
    loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S ((fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F)))  \<^sub>S)"
  apply rule (* Display 4 on page 21 of [MPS] *)
  apply(rule_tac FboxK_R)
  apply(rule_tac Back_forw_K2)
  apply(rule_tac ImpR_R)
  apply(rule_tac Back_forw_K)
  apply(rule_tac FS_K_R)
  apply (rule_tac derivable.Comma_impR_disp) (* Display 6 on page 21 of [MPS] *)

  apply (rule_tac f="fdiamK\<^sub>F `j` (((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<and>\<^sub>F (`h` \<^sub>F))" in derivable.SingleCut)
  using cut apply blast
  defer
  apply (rule_tac derivable.FdiamK_L)
  apply (rule_tac derivable.Forw_back_K2)
  apply (rule_tac f="\<bottom>\<^sub>F" in derivable.SingleCut)
  using cut apply blast
  apply (rule_tac derivable.Bot_R)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac derivable.Bot_L)
  apply (rule_tac derivable.Id)
  apply (rule_tac derivable.IW_R)
  apply (rule_tac derivable.Bot_L) (* Display 8 on page 21 of [MPS] *)
  
  apply (rule_tac f="(fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<and>\<^sub>F (fdiamK\<^sub>F `j` (`h` \<^sub>F))" in derivable.SingleCut)
  using cut apply blast
  defer 

  (* Display 11/12 on page 21 of [MPS] *)
  
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.FdiamK_L)
  apply (rule_tac derivable.Forw_back_K2)
  apply (rule_tac derivable.K_FS_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.Forw_back_K)
  apply (rule_tac derivable.FdiamK_R)
  apply (rule_tac derivable.And_R)
  apply (rule_tac Id)  
  apply (rule_tac Id)
  
  (* Display 10/11 on page 21 of [MPS] *)
  
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.And_R)
  apply (rule_tac derivable.FdiamK_R)
  apply (rule_tac Id)
  
  (* Display 9 on page 21 of [MPS] *)

  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)    
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)

  apply (rule_tac f="vision (Suc n)" in derivable.SingleCut)
  using cut apply blast

  apply(rule E_der_simp2)
  using agent apply simp

  apply (rule_tac derivable.Comma_impR_disp)

  apply (rule_tac f="\<And>\<^sub>F map (\<lambda>h. fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) [h\<leftarrow> [[1 .. (Suc n)]] .  h \<noteq> j]" in derivable.SingleCut)
  using cut apply blast
  defer
  apply(rule_tac f="fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)" in conj_der1)
  apply(rule Id)
  using set_eq apply fastforce
  apply (rule_tac derivable.Comma_impR_disp2)
  thm conj_der2
  unfolding vision_def
  
  apply(rule_tac l'="map (\<lambda>x. (left x) \<and>\<^sub>F (right x) ) [h\<leftarrow> [[1 .. (Suc n)]] . h \<noteq> j]" in conj_der2)
  using cut apply simp
  
  apply(rule_tac f="(\<And>\<^sub>F map left [h\<leftarrow> [[1 .. (Suc n)]] . h \<noteq> j]) \<and>\<^sub>F (\<And>\<^sub>F map right [h\<leftarrow> [[1 .. (Suc n)]] . h \<noteq> j])" in SingleCut)
  using cut apply simp
  
  apply(rule_tac conj_fold)
  using cut apply simp
  unfolding right_def
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  unfolding dirty_def

  apply(rule_tac f="\<And>\<^sub>F map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. (Suc n)]] . x \<noteq> j]" in SingleCut)
  using cut apply simp
  apply(subst list_eq)
  
  apply(rule_tac l="map (Formula_Atprop \<circ> nat_to_string) J @ map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow> [[1 .. (Suc n)]] . x \<noteq> j]" in conj_der2b)
  using cut apply simp
  using j_range J_contains using Id apply auto[1]
  apply simp
  apply (rule_tac derivable.Comma_impR_disp)
  
  apply(subst f_subst)
    
  apply (rule_tac E_L)
  apply (simp add: conj_impl_fold cut)
  proof -
  case goal1
    have "set [h\<leftarrow> [[1 .. Suc n]] . h \<noteq> j] = { h. 0 < h \<and> h \<le> Suc n \<and> h\<noteq>j }" by auto
    
    then have a: "set (map (\<lambda>h. ((`h` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `h` \<^sub>F) \<and>\<^sub>F 
      (((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) [h\<leftarrow> [[1 .. (Suc n)]] . h \<noteq> j]) =
      image (\<lambda>h. ((`h` \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` `h` \<^sub>F) \<and>\<^sub>F 
      (((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) { h. 0 < h \<and> h \<le> Suc n \<and> h\<noteq>j }" by simp
    then have b: "\<dots> = { (((`h`) \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`h`) \<^sub>F) \<and>\<^sub>F 
      (((`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F `j` (`h` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) | h. 0 < h \<and> h \<le> Suc n \<and> h\<noteq>j }" by blast
    
    then have "\<dots> \<subseteq> set (vision' (Suc n))" using vision_contains j_range by blast
    with a b show ?case by (simp add: left_def)
  qed
    
  with set_eq have 2: "\<forall>h \<in> set ([x \<leftarrow>  [[1 .. Suc n]]. x\<noteq>j]).
    loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S ((fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F)))  \<^sub>S)" by simp

  then have 3: "\<forall>f\<in>set (map (\<lambda>x. fboxK\<^sub>F `j` ((`x` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F))) [x \<leftarrow>  [[1 .. Suc n]]. x\<noteq>j]).
    loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S (f \<^sub>S)" using  imageE set_map
  proof -
    have f1: "\<forall>h. h \<in>  set ([x \<leftarrow>  [[1 .. Suc n]]. x\<noteq>j]) \<longrightarrow>
    loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S ((fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F)))  \<^sub>S)"
      by (metis 2)
    thus ?thesis
      using set_map by (metis (no_types, lifting) imageE)
  qed
        
  have fboxK_map_subst: "\<And>list. map (\<lambda>h. fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F))) list =  map (Formula_FboxK `j`)  (map (\<lambda>h. ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F))) list)" by simp
  have map_subst2: "map (\<lambda>h. (`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F)) ( [[1 .. Suc n]]) = map (\<lambda>B. B \<rightarrow>\<^sub>F (`j` \<^sub>F)) (map (Formula_Atprop \<circ> nat_to_string) ( [[1 .. Suc n]]))" by simp
  have map_subs1: "set ( [[1 .. Suc n]]) = set ([h\<leftarrow> [[1 .. Suc n]] .  h \<noteq> j]) \<union> {j}" 
  by (metis "0.prems"(1) "0.prems"(2) J_contains One_nat_def Un_insert_right `{1..Suc n} - {j} = set [x\<leftarrow> [[1 .. Suc n]] . x \<noteq> j]` insert_Diff insert_subset sup_bot.right_neutral upto'_simp1)

  then have map_subs2: "set [[1 .. Suc n]] = set (j#[h\<leftarrow> [[1 .. Suc n]] .  h \<noteq> j])" by simp

  thus ?case
  apply (subst k_apply.simps(1))
   
  (* Display 1 on page 21 of [MPS] *)

  apply (rule_tac derivable.FboxA_R)
  apply (rule_tac derivable.Back_forw_A2)
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.Back_forw_A)
  apply (rule_tac derivable.Reduce_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.I_impL2)
  apply (rule_tac derivable.Bigcomma_Nil_L)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Bigcomma_Cons_L)
  apply (rule_tac rel=rel and beta="(''father'' @ `Suc n`)" in Swapout_R_1)
  using rel_refl apply (simp, simp)
  apply (rule_tac derivable.Back_forw_K2)

  apply (rule_tac f = "(One\<^sub>F (''father'' @ `Suc n`)) \<rightarrow>\<^sub>F (`j` \<^sub>F)" in derivable.SingleCut)
  using cut apply simp

  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac f="(father (Suc n))" in derivable.Pre_L)
  using preFather unfolding preFormula_father_def apply blast

  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac f = "One\<^sub>F (''father'' @ `Suc n`)" in derivable.SingleCut)
  using cut apply simp
  apply (rule_tac derivable.One_R)

  apply (rule_tac f="father (Suc n)" in derivable.Pre_L)
  using preFather unfolding preFormula_father_def apply blast
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.Comma_impR_disp2)
  
  defer

  (* Display 2 on page 21 of [MPS] *)

  apply (rule_tac derivable.Reduce_R)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac derivable.Atom)
  apply simp
  
  apply (rule_tac derivable.One_R)
  
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.E_L)
  
  (* Display 3 on page 21 of [MPS] *)

  apply (rule_tac f = "\<And>\<^sub>F map (\<lambda>h. fboxK\<^sub>F `j` ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F))) [h \<leftarrow>  [[1 .. Suc n]]. h\<noteq>j]" in derivable.SingleCut)
  using cut apply simp
  apply(rule_tac conj_der1b)
  using 3 apply blast

  apply (rule_tac f = "fboxK\<^sub>F `j` (\<And>\<^sub>F map (\<lambda>h. ((`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F))) [h \<leftarrow>  [[1 .. Suc n]]. h\<noteq>j])" in derivable.SingleCut)
  using cut apply simp

  apply(subst fboxK_map_subst)
  apply(rule_tac conj_box_distrib)

  using cut apply blast
  apply (rule_tac derivable.FboxK_L)
  unfolding father_def

  apply (rule_tac f = "(\<And>\<^sub>F map (\<lambda>h. (`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F)) ( [[1 .. Suc n]]))" in derivable.SingleCut)
  using cut apply simp

  defer
  apply(subst map_subst2)
  apply(rule_tac disj_lub)
  using cut apply simp
  
  apply(rule_tac l="map (\<lambda>h. (`h` \<^sub>F) \<rightarrow>\<^sub>F (`j` \<^sub>F)) (j#[h\<leftarrow> [[1 .. Suc n]] .  h \<noteq> j])" in conj_der2b)
  using cut apply simp
  apply(subst conj_unfold_1a)
  
  apply (rule_tac derivable.I_impR2)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.And_R)
  apply(rule Id)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.W_impR_R)
  apply (rule_tac derivable.Id)
  using map_subs2 by (metis (mono_tags, lifting) set_eq_subset set_map)

next
(* -------------------- successor case for k  --------------------  *)
case (Suc k) (* the number of dirty children is Suc(Suc k) *)

  then obtain J' where J'_def: "set J' = set J - {j}" by (meson set_removeAll)
  then obtain j' where j'_def: "j' \<in> set J'" by (metis Diff_empty List.finite_set Suc(4) Suc.prems(4) card_Diff_insert card_eq_SucD diff_Suc_1 empty_iff insert_subset order_refl)
  
  with Suc J'_def have "card (set J') = Suc k" by simp
  with Suc have ih: " \<forall>j\<in>set J'. loc \<turnstile>d (dirty (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )\<^sub>S \<turnstile>\<^sub>S 
    (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j` (`j` \<^sub>F)) \<^sub>S" using Diff_subset Suc_leD J'_def subsetCE subsetI
  proof -
    have "set J' \<subseteq> {1..Suc n}"
      by (metis (no_types) Diff_subset Suc.prems(2) J'_def subsetCE subsetI)
    thus ?thesis
      by (meson Suc.hyps Suc.prems(1) Suc_leD `card (set J') = Suc k`)
  qed


(* ------------------ start of claim 1 ------------------ *)

  have claim10: "loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc (Suc k) vision (Suc n)) \<^sub>S \<turnstile>\<^sub>S 
  (dirty (Suc n) J \<and>\<^sub>F ( vision (Suc n) \<and>\<^sub>F fboxK\<^sub>F `j` ( E (Suc n) \<^sup>Suc k vision (Suc n))))\<^sub>S"
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.And_R)
  defer
  apply(rule Id)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.And_R)
  apply(subst k_apply.simps)
  apply (rule E_der_simp)
  using Suc j'_def apply auto[1]
  apply(rule E_der_simp2)
  using assms by simp



  have claim11:  "loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F ( vision (Suc n) \<and>\<^sub>F fboxK\<^sub>F `j` ( E (Suc n) \<^sup>Suc k vision (Suc n))))\<^sub>S \<turnstile>\<^sub>S 
  ( (fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' )) \<and>\<^sub>F (fboxK\<^sub>F `j` ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.A_L)
  apply (rule_tac derivable.And_R)
  apply (rule_tac Id)
  
  apply(rule_tac dirty_vision_der)
  using Suc(2,3,5) J'_def cut by auto

  have claim12: "loc \<turnstile>d ( (fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' )) \<and>\<^sub>F (fboxK\<^sub>F `j` ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
  ( fboxK\<^sub>F `j` (( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' ) \<and>\<^sub>F ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Back_forw_K2)
  apply (rule_tac derivable.K_mon_L)
  apply (rule_tac derivable.And_R)
  
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac Id)
  
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac Id)
  by (rule_tac Id)

  have claim13: "loc \<turnstile>d ( fboxK\<^sub>F `j` (( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' ) \<and>\<^sub>F ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
  ( fboxK\<^sub>F `j` (( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' ) \<and>\<^sub>F ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"

  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.And_R)
  
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac Id)
  
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac Id)
  by (rule_tac Id)
  
  have claim14: "loc \<turnstile>d ( fboxK\<^sub>F `j` (( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' ) \<and>\<^sub>F ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
  ( fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( dirty (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.A_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.A_L2)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.A_L)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.And_R)
  
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac Id)
  apply (rule_tac Id)
  
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac Id)
  by (rule_tac Id)
  

  
  have claim15: "loc \<turnstile>d ( fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( dirty (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
  ( fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) )) )\<^sub>S"
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  defer
  apply (rule Id)
  using ih Id j'_def by simp
  
  
  have claim16: "loc \<turnstile>d ( fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S 
  ( fboxK\<^sub>F `j` ( (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) )) )\<^sub>S"
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac Id)
  
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  by (rule_tac Id)


  have claim1: "loc \<turnstile>d (dirty (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc (Suc k) vision (Suc n)) \<^sub>S \<turnstile>\<^sub>S 
   ( fboxK\<^sub>F `j` ( (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
       `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) )) )\<^sub>S"
  apply (rule_tac f="dirty (Suc n) J \<and>\<^sub>F (vision (Suc n) \<and>\<^sub>F fboxK\<^sub>F `j` E (Suc n) \<^sup>Suc k vision (Suc n))" in derivable.SingleCut)
  using cut apply simp
  using claim10 apply simp
  
  apply (rule_tac f="fboxK\<^sub>F `j` ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F dirty (Suc n) J' \<and>\<^sub>F
    fboxK\<^sub>F `j` E (Suc n) \<^sup>Suc k vision (Suc n)" in derivable.SingleCut)
  using cut apply simp
  using claim11 apply simp
  
  apply (rule_tac f="fboxK\<^sub>F `j` (( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' ) \<and>\<^sub>F ( E (Suc n) \<^sup>Suc k vision (Suc n) ))" in derivable.SingleCut)
  using cut apply simp
  using claim12 apply simp
  
  apply (rule_tac f=" fboxK\<^sub>F `j` (( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty (Suc n) J' ) \<and>\<^sub>F ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) ))" in derivable.SingleCut)
  using cut apply simp
  using claim13 apply simp
  
  apply (rule_tac f="fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( dirty (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) ))" in derivable.SingleCut)
  using cut apply simp
  using claim14 apply simp
  
  apply (rule_tac f="fboxK\<^sub>F `j` ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
       `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp
  using claim15 apply simp
  
  apply (rule_tac f="fboxK\<^sub>F `j` ( (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
       `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp
  using claim16 apply simp
  
  by (rule_tac Id)

(* ------------------- end of claim 1 ------------------- *)

(* ------------------ start of claim 2 ------------------ *)


(* In lem363_ we prove the different steps of Lemma 36.3 -- see p23 of the paper Ma Pal Sad*) 
    
  have lem363a: "loc \<turnstile>d ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ))) \<and>\<^sub>F 
   (fdiamA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k (no (Suc n) )) )\<^sub>S
   \<turnstile>\<^sub>S ( ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ) ) )\<and>\<^sub>F (
   ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F
   (fdiamA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k(no (Suc n) )) ) )
   )\<^sub>S" 
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.And_R)
  
  defer
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  apply (rule Id)
  
  apply (rule Id)
  
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule Id)
  done
  
  
  have lem363b: "loc \<turnstile>d
   ( ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ) ) )\<and>\<^sub>F (
   ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F
   (fdiamA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k (no (Suc n) )) ) )
   )\<^sub>S
   \<turnstile>\<^sub>S 
   ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ) \<and>\<^sub>F 
   (fdiamA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k(no (Suc n) )) )
  ) )\<^sub>S" 
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.Comma_impL_disp)
  apply (rule_tac derivable.A_L2)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.A_L2)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.A_L)
  apply (rule_tac derivable.And_R)
  
  defer
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule Id)
  apply (rule Id)
  
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule Id)
  apply (rule Id)
  done

  have lem363c: "loc \<turnstile>d
  ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( 
    (fboxA\<^sub>F (''father'' @ `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ) \<and>\<^sub>F 
    (fdiamA\<^sub>F (''father'' @ `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k(no (Suc n))) )
  ) )\<^sub>S \<turnstile>\<^sub>S 
  ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( 
    (fboxA\<^sub>F (''father'' @ `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ) \<and>\<^sub>F 
    (fdiamA\<^sub>F (''father'' @ `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )
  ) )\<^sub>S" 
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  defer
  apply (rule Id)
  
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.And_R)
  defer
  apply (rule Id)
  
  apply (rule_tac derivable.FdiamA_L)
  apply (rule_tac derivable.FdiamA_R)
  
  apply(subst k_apply_elim_diamA)
  defer apply(simp)
  apply (rule_tac f = "(fdiamK\<^sub>F `j'` ( (`j'` \<^sub>F) )) \<and>\<^sub>F (fdiamK\<^sub>F `j'` ( (`j'` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ))" in derivable.SingleCut)
  using cut apply simp
  defer
  
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule Id)
  apply(rule no_imp)

  using j'_def J'_def Suc(3) by force
  
  
  have lem363d: "loc \<turnstile>d
   ( ( (fboxA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ) \<and>\<^sub>F 
   (fdiamA\<^sub>F (''father'' @
   `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )
  ) )\<^sub>S \<turnstile>\<^sub>S ( (fdiamA\<^sub>F (''father'' @
   `Suc n`) ( ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) 
   \<and>\<^sub>F ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )) )\<^sub>S" 
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.FdiamA_L)
  apply (rule_tac derivable.Forw_back_A2)
  apply (rule_tac derivable.A_FS_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Forw_back_A)
  apply (rule_tac derivable.FdiamA_R)
  apply (rule_tac derivable.And_R)
  defer
  apply (rule_tac derivable.Back_forw_A)
  apply (rule_tac derivable.FboxA_L)
  apply (rule Id)
  apply (rule Id)
  done
  
  
  have lem363e: "loc \<turnstile>d
   ( ( ( ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k ( fboxK\<^sub>F `j'` (`j'` \<^sub>F)) )) \<and>\<^sub>F 
   ( ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k (fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F))) )
  ) )\<^sub>S \<turnstile>\<^sub>S ( ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k ( ( fboxK\<^sub>F `j'` (`j'` \<^sub>F)) 
   \<and>\<^sub>F ( fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )) )\<^sub>S" 
  
  apply (subst k_apply_BoxDiam)
  using cut apply simp
  apply simp
  done
  
  have lem363f: "loc \<turnstile>d
   ( ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k ( ( fboxK\<^sub>F `j'` (`j'` \<^sub>F)) 
   \<and>\<^sub>F ( fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k ( \<bottom>\<^sub>F )) \<^sub>S" 
  apply (rule k_apply_elim_diamA )
  apply (rule_tac derivable.Bot_R)
  apply (rule_tac derivable.Refl_ForwK)
  using agent apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.FdiamK_L)
  apply (rule_tac derivable.Forw_back_K2)
  apply (rule_tac derivable.K_FS_R)
  apply (rule_tac derivable.ImpR_L)
  defer
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac derivable.FboxK_L)
  apply (rule Id)
  apply (rule_tac derivable.IW_R)
  apply (rule_tac derivable.Bot_L) 
  done
  
  have lem363: "loc \<turnstile>d ( ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( 
    (fboxA\<^sub>F (''father'' @  `Suc n`) ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ))) \<and>\<^sub>F 
    (fdiamA\<^sub>F (''father'' @ `Suc n`) ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k (no (Suc n) )) )\<^sub>S
  \<turnstile>\<^sub>S ( ((`j` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F )\<^sub>S" 
  apply(rule_tac f=" (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
    fboxA\<^sub>F (''father'' @  `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` `j'` \<^sub>F) \<and>\<^sub>F
    (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
        fdiamA\<^sub>F (''father'' @ `Suc n`) Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k no (Suc n))" in derivable.SingleCut)
  using cut apply simp
  using lem363a apply simp
  
  
  apply (rule_tac f="((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
    ( (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` )\<^sub>F ) \<and>\<^sub>F
    ( fdiamA\<^sub>F (''father'' @ `Suc n`) Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k no (Suc n)))" in derivable.SingleCut)
  using cut apply simp
  using lem363b apply simp
  
  apply (rule_tac f=" ((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
   ( (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` `j'` \<^sub>F ) \<and>\<^sub>F
   ( fdiamA\<^sub>F (''father'' @ `Suc n`) Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k fdiamK\<^sub>F `j'` ( (`j'` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) )) " in derivable.SingleCut)
  using cut apply simp
  using lem363c apply simp
  
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_L)
  defer
  apply (rule Id)
  
  apply (rule_tac f="(fdiamA\<^sub>F (''father'' @ `Suc n`) ( ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) \<and>\<^sub>F
    ( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp

  using lem363d apply simp
  
  apply (rule_tac derivable.FdiamA_L)
  apply (rule_tac derivable.Forw_back_A2)
  
      
  apply (rule_tac f="( Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k ( ( fboxK\<^sub>F `j'` (`j'` \<^sub>F)) \<and>\<^sub>F
    ( fdiamK\<^sub>F `j'` ((`j'` \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp
  using lem363e apply simp
      
  apply (rule_tac f="Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k \<bottom>\<^sub>F" in derivable.SingleCut)
  using cut apply simp
  using lem363f apply simp
  
  
  apply (rule_tac derivable.Forw_back_A)
  apply (rule_tac derivable.Bot_R)
  apply (rule_tac derivable.Forw_back_A2)
  apply (rule_tac derivable.A_nec_R)
  by (rule_tac k_apply_DiamBot)
   
  
  have claim2: "loc \<turnstile>d ( fboxK\<^sub>F `j` ( (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( 
    (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S 
    (fboxK\<^sub>F `j` (( father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k (`j` \<^sub>F)) )) )\<^sub>S"
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac f = "(father (Suc n)) \<rightarrow>\<^sub>F ((((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) ) \<rightarrow>\<^sub>F ( 
    (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.A_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule Id)
  apply (rule_tac derivable.And_R)
  apply (rule Id)
  apply (rule Id)
  
  apply (rule_tac derivable.ImpR_L)
  defer
  apply (rule_tac Id)
  
  apply (rule_tac derivable.FboxA_R)
  apply (rule_tac derivable.Back_forw_A2)
  
  
  apply(subst k_apply_unfold_bis)
  apply(subst k_apply_S_display_1)
  using cut apply simp
  apply(subst k_apply_S_display_2)
  
  apply (rule_tac derivable.FboxA_R)
  apply (rule_tac f="(One\<^sub>F ((''no'' @ `Suc n`))) \<rightarrow>\<^sub>F ( `j` \<^sub>F) " in derivable.SingleCut)
  using cut apply simp
  defer
  
  apply (rule_tac derivable.Reduce_R)
  apply (rule_tac derivable.ImpR_L)
  defer
  apply (rule_tac derivable.One_R)
  defer
  apply (rule_tac derivable.Atom)
  apply (simp)
  


  apply (rule_tac derivable.ImpR_R)
  apply(subst k_apply_S_display_2back)

  apply (rule_tac k_apply_S_FS)


  apply (rule_tac derivable.Back_forw_A)
  apply (rule_tac derivable.FS_A_R)
  apply (rule_tac derivable.Comma_impR_disp)

  apply (rule_tac derivable.E_L)
  
  
  apply (rule_tac f= "(((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` `j'` \<^sub>F) \<and>\<^sub>F
    fdiamA\<^sub>F (''father'' @ `Suc n`) Formula_FdiamA (''no'' @ `Suc n`) \<^sup>k no (Suc n)" in derivable.SingleCut)
  using cut apply blast
  apply (rule_tac derivable.And_R)
  apply (rule_tac derivable.FdiamA_R)

  apply (rule_tac k_apply_S_F_forw_diam)
  apply (rule_tac f="no (Suc n)" in derivable.Pre_L)
  using preNo unfolding preFormula_no_def apply blast
  apply(rule Id)+
  
  apply(rule_tac f = "((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F" in derivable.SingleCut)
  using cut apply simp
  using lem363 apply simp
  apply (rule_tac f="`j` \<^sub>F" in derivable.SingleCut)
  using cut apply blast
  defer
  apply (rule k_apply_S_Atom)
  using cut apply simp
  apply (rule_tac derivable.C_R)
  apply (rule_tac derivable.I_impR2)
  apply (rule_tac derivable.Grishin_R2)
  apply (rule_tac derivable.E_R)
  apply (rule_tac derivable.ImpR_comma_disp2)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.E_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.ImpR_L)
  apply (rule_tac derivable.IW_R)
  apply (rule_tac derivable.Bot_L)

  apply (rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.ImpR_comma_disp)
  apply (rule_tac derivable.E_R)
  apply (rule_tac derivable.Grishin_R)
  apply (rule_tac derivable.W_impR_R)
  apply (rule_tac derivable.ImpL_comma_disp2)
  apply (rule_tac derivable.W_impL_R)
  apply (rule_tac derivable.Id)
  done

(* ------------------- end of claim 2 ------------------- *)

(* ------------------ start of claim 3 ------------------ *)

  have claim3: "loc \<turnstile>d ( fboxK\<^sub>F `j` (( father (Suc n) ) \<rightarrow>\<^sub>F ( 
    (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k (`j` \<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( (fboxA\<^sub>F (''father'' @  `Suc n`) fboxK\<^sub>F `j` ( Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k (`j` \<^sub>F)) ) )\<^sub>S"
  apply (rule_tac derivable.FboxA_R)
  apply (rule_tac derivable.Back_forw_A2)
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.Back_forw_A)
  apply (rule_tac derivable.I_impR2)
  apply (rule_tac derivable.Bigcomma_Nil_L)
  apply (rule_tac derivable.Comma_impR_disp)
  apply (rule_tac derivable.Bigcomma_Cons_L)
  apply(rule_tac rel=rel and beta="''father'' @ `Suc n`" in Swapout_R_1)
  using rel_refl apply (simp,simp)
  
  
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac derivable.Reduce_R)
  apply (rule_tac derivable.ImpR_L)
  
  apply (rule_tac derivable.FboxA_L)
  apply (rule_tac Id)
  apply (rule_tac f="One\<^sub>F (''father'' @ `Suc n`)" in derivable.SingleCut)
  using cut apply simp
  apply (rule_tac derivable.One_R)
  
  apply (rule_tac f="father (Suc n)" in derivable.Pre_L)
  using preFather unfolding preFormula_father_def apply blast
  by (rule_tac Id)

(* ------------------- end of claim 3 ------------------- *)

(* ------------------ start of claim 4 ------------------ *)

  have claim4: "loc \<turnstile>d 
    ( (fboxA\<^sub>F (''father'' @ `Suc n`)  fboxK\<^sub>F `j` (  Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k (`j` \<^sub>F)) ) )\<^sub>S \<turnstile>\<^sub>S 
    (fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k fboxK\<^sub>F `j` `j` \<^sub>F) \<^sub>S"
  apply (rule_tac derivable.FboxA_R)
  apply (rule_tac derivable.FboxA_L)
  
  apply (subst k_apply_S_display_1)
  using cut apply simp
  apply (subst k_apply_S_display_2)
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac k_apply_S_display_2a)
  apply (rule_tac rel=rel in Swapout_R_2)
  using cut rel_refl by simp+
  
(* ------------------- end of claim 4 ------------------- *)

  show ?case
  apply (rule_tac f="fboxK\<^sub>F `j` ( (((`j` \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
    `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>k fboxK\<^sub>F `j'` (`j'` \<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp
  using claim1 Suc apply blast

  apply (rule_tac f="fboxK\<^sub>F `j` (( father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
    `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k (`j` \<^sub>F)) ))" in derivable.SingleCut)
  using cut apply simp
  using claim2 Suc apply blast

  apply (rule_tac f="(fboxA\<^sub>F (''father'' @
    `Suc n`)  fboxK\<^sub>F `j` ( (Formula_FboxA (''no'' @ `Suc n`)) \<^sup>Suc k (`j` \<^sub>F)) )" in derivable.SingleCut)
  using cut apply simp
  using claim3 apply simp

  apply (rule_tac f="fboxA\<^sub>F (''father'' @ `Suc n`) Formula_FboxA (''no'' @ `Suc n`) \<^sup>Suc k fboxK\<^sub>F `j` `j` \<^sub>F" in derivable.SingleCut)
  using cut apply simp
  using claim4 apply simp
  using Id by blast
qed
end