theory DEAKDerivedRules
imports Main "calculus/src/isabelle/DEAK_SE" NatToString
begin

(* The Id rule where for every formula f, f \<^sub>S \<turnstile>\<^sub>S f \<^sub>S is derivable *)
lemma Id:
  fixes f :: Formula
  shows "loc \<turnstile>d f \<^sub>S \<turnstile>\<^sub>S f \<^sub>S"
apply(induct f)
apply (rule_tac derivable.FboxA_R)
apply (rule_tac derivable.FboxA_L)
apply simp
apply (rule_tac derivable.FdiamA_L)
apply (rule_tac derivable.FdiamA_R)
apply simp
apply (rule_tac derivable.BboxA_R)
apply (rule_tac derivable.BboxA_L)
apply simp
apply (rule_tac derivable.BdiamA_L)
apply (rule_tac derivable.BdiamA_R)
apply simp
apply (rule_tac derivable.FboxK_R)
apply (rule_tac derivable.FboxK_L)
apply simp
apply (rule_tac derivable.FdiamK_L)
apply (rule_tac derivable.FdiamK_R)
apply simp
apply (rule_tac derivable.BboxK_R)
apply (rule_tac derivable.BboxK_L)
apply simp
apply (rule_tac derivable.BdiamK_L)
apply (rule_tac derivable.BdiamK_R)
apply simp
apply (rule_tac derivable.Id)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
apply simp
apply simp
apply (rule_tac derivable.ImpL_R)
apply (rule_tac derivable.ImpL_L)
apply simp
apply simp
apply (rule_tac derivable.DImpL_L)
apply (rule_tac derivable.DImpL_R)
apply simp
apply simp
apply (rule_tac derivable.DImpR_L)
apply (rule_tac derivable.DImpR_R)
apply simp
apply simp
apply (rule_tac derivable.Or_R)
apply (rule_tac derivable.Or_L)
apply simp
apply simp
apply (rule_tac derivable.ImpR_R)
apply (rule_tac derivable.ImpR_L)
apply simp
apply simp
apply (rule_tac derivable.One_L)
apply (rule_tac derivable.One_R)
apply (rule_tac derivable.Top_L)
apply (rule_tac derivable.Top_R)
apply (rule_tac derivable.Bot_R)
apply (rule_tac derivable.Bot_L)
done

definition disj :: "Formula list \<Rightarrow> Formula" ("\<Or>\<^sub>F _" 300) where
"disj list = foldr (Formula_Or) list \<bottom>\<^sub>F"

lemma disj_unfold_1: "(\<Or>\<^sub>F (x#list)) = x \<or>\<^sub>F (\<Or>\<^sub>F list)" unfolding disj_def by simp

definition conj :: "Formula list \<Rightarrow> Formula" ("\<And>\<^sub>F _" 300) where
"conj list = foldr (Formula_And) list \<top>\<^sub>F"

lemma conj_unfold_1: "(\<And>\<^sub>F (x#list)) = x \<and>\<^sub>F (\<And>\<^sub>F list)" unfolding conj_def by simp

lemma conj_unfold_1a: "(\<And>\<^sub>F (map f (x#list))) = (f x) \<and>\<^sub>F (\<And>\<^sub>F map f list)" unfolding conj_def by simp

lemma conj_unfold_2:
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d (\<And>\<^sub>F (list1@list2)) \<^sub>S \<turnstile>\<^sub>S ((\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)) \<^sub>S"
apply (induct list1)
apply(subst conj_def)+
apply simp
apply (rule_tac derivable.C_L)
apply (rule_tac derivable.And_R)
apply (rule Id)
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
proof goal_cases
  case (1 a list1)
  have 2: "(a # list1) @ list2 = a # (list1 @ list2)" by simp
  show ?case unfolding 2
  apply(subst conj_unfold_1)
  apply(subst conj_unfold_1)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.And_R)

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac f="(\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)" in derivable.SingleCut)
  using cut apply simp
  using 1 apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac Id)

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.And_R)

  apply (rule_tac f="(\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)" in derivable.SingleCut)
  using cut apply simp
  using 1 apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  apply (rule_tac Id)

  by (rule_tac Id)
qed

lemma conj_unfold_2b:
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ((\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)) \<^sub>S \<turnstile>\<^sub>S (\<And>\<^sub>F (list1@list2)) \<^sub>S"
apply(induct list1)
apply(subst conj_def)+
apply simp
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac Id)
proof goal_cases
  case (1 a list1)
  have 2: "(a # list1) @ list2 = a # (list1 @ list2)" by simp
  show ?case unfolding 2
  apply(subst conj_unfold_1)
  apply(subst conj_unfold_1)

  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.And_R)

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)

  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac derivable.Comma_impL_disp)

  apply (rule_tac f="(\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)" in derivable.SingleCut)
  using cut apply simp
  apply (rule_tac derivable.And_R)
  apply (rule_tac Id)
  apply (rule_tac Id)

  using 1 apply simp

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)

  apply (rule_tac derivable.W_impR_R)
  by (rule_tac Id)
qed

lemma conj_fold:
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d (\<And>\<^sub>F map (\<lambda>x. f x \<and>\<^sub>F f' x) l) \<^sub>S \<turnstile>\<^sub>S ((\<And>\<^sub>F map f l) \<and>\<^sub>F (\<And>\<^sub>F map f' l)) \<^sub>S"
apply(induct l)
apply simp
apply(subst conj_def)+
apply simp
apply (rule_tac derivable.Top_L)
apply (rule_tac derivable.C_L)
apply (rule_tac derivable.And_R)
apply (rule_tac derivable.Top_R)
apply (rule_tac derivable.Top_R)
apply(subst conj_unfold_1a)+

apply (rule_tac f="(f a \<and>\<^sub>F f' a) \<and>\<^sub>F ((\<And>\<^sub>F map f l) \<and>\<^sub>F (\<And>\<^sub>F map f' l))" in derivable.SingleCut)
using cut apply simp
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
apply simp
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
apply (rule_tac Id)
apply (rule_tac Id)

apply (rule_tac derivable.C_L)
apply (rule_tac derivable.And_R)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
apply (rule_tac derivable.And_L)

apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac Id)

apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac Id)

apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac Id)

apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac Id)
done

lemma conj_impl_fold:
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ((\<And>\<^sub>F map f list) \<^sub>S) ;\<^sub>S ((\<And>\<^sub>F map (\<lambda>y. f y \<rightarrow>\<^sub>F f' y) list) \<^sub>S) \<turnstile>\<^sub>S (\<And>\<^sub>F map f' list) \<^sub>S"
apply(induct list)
apply simp
apply(subst conj_def)+
apply simp
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)

apply(subst conj_unfold_1a)+

apply (rule_tac derivable.C_L)
apply (rule_tac derivable.And_R)
defer
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac derivable.Comma_impL_disp)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac derivable.ImpR_L)
apply (rule_tac Id)
apply (rule_tac Id)

apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac derivable.Comma_impL_disp)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac derivable.Comma_impR_disp)
by simp

lemma conj_der1: "loc \<turnstile>d ( f )\<^sub>S \<turnstile>\<^sub>S X \<Longrightarrow> f \<in> set list \<Longrightarrow> loc \<turnstile>d ( \<And>\<^sub>F list )\<^sub>S \<turnstile>\<^sub>S X"
apply(induct list)
proof (simp, goal_cases)
  case (1 a list)
  thus ?case
  apply(cases "f \<in> set list")
  apply simp
  apply (subst conj_unfold_1)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply simp
  proof goal_cases
    case 1 
    then have "f = a" by simp
    thus ?case
    apply (subst conj_unfold_1)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    using 1 Id by simp
  qed
qed

lemma conj_der1b: " \<forall>f \<in> set list. loc \<turnstile>d X  \<turnstile>\<^sub>S ( f )\<^sub>S \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S ( \<And>\<^sub>F list )\<^sub>S"
apply(induct list)
apply simp 
using IW_L Top_R conj_def apply simp
proof (simp, goal_cases)
  case (1 a list)
  show ?case
  apply(subst conj_unfold_1)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.And_R)
  defer
  using 1 apply simp
  using 1 using IW_L Top_R conj_def by fastforce
qed

lemma conj_der2_aux: 
  fixes l'
  shows "\<And> l. set l' \<subseteq> set l \<Longrightarrow> loc \<turnstile>d ( \<And>\<^sub>F l )\<^sub>S \<turnstile>\<^sub>S ( \<And>\<^sub>F l' )\<^sub>S"
apply(induct l')
apply(subst (2) conj_def)
apply simp
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
proof (simp, goal_cases)
  case (1 a l' l)
  then have "loc \<turnstile>d (\<And>\<^sub>F l) \<^sub>S \<turnstile>\<^sub>S (\<And>\<^sub>F l') \<^sub>S" by simp
  thus ?case
  apply (rule_tac derivable.C_L)
  apply (subst conj_unfold_1)
  apply (rule_tac derivable.And_R)
  apply simp
  apply(rule_tac f=a in conj_der1)
  apply (rule Id)
  using 1 by simp
qed

lemma conj_der2: 
  fixes l'
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  and "loc \<turnstile>d ( \<And>\<^sub>F l' )\<^sub>S \<turnstile>\<^sub>S X"
  shows "\<And> l. set l' \<subseteq> set l \<Longrightarrow> loc \<turnstile>d ( \<And>\<^sub>F l )\<^sub>S \<turnstile>\<^sub>S X"
using assms(2) proof (induct l')
case Nil 
  have 1: "(\<And>\<^sub>F []) = \<top>\<^sub>F" unfolding conj_def by simp
  with Nil have "loc \<turnstile>d \<top>\<^sub>F \<^sub>S \<turnstile>\<^sub>S X" by simp
  then have "loc \<turnstile>d I\<^sub>S \<turnstile>\<^sub>S X"
  apply (rule_tac f="\<top>\<^sub>F" in derivable.SingleCut)
  using cut apply simp
  apply (rule_tac derivable.Top_R)
  by simp
  thus ?case
  apply (rule_tac derivable.IW_L)
  by simp
next
case (Cons x xs)
  show ?case
  apply (rule_tac f="(\<And>\<^sub>F (x#xs))" in derivable.SingleCut)
  using cut apply simp
  using conj_der2_aux cut Cons.prems(1) apply blast
  using Cons by simp
qed

lemma conj_der2b: 
  fixes l'
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  and "loc \<turnstile>d X \<turnstile>\<^sub>S ( \<And>\<^sub>F l )\<^sub>S"
  shows "\<And> l'. set l' \<subseteq> set l \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S ( \<And>\<^sub>F l' )\<^sub>S"
using assms(2) 
apply (induct l)
apply simp

apply (rule_tac f="(\<And>\<^sub>F a # l)" in derivable.SingleCut)
  using cut apply simp
apply simp
using conj_der2_aux cut apply blast
done

lemma conj_box_distrib : 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ( \<And>\<^sub>F map (Formula_FboxK (nat_to_string i)) l )\<^sub>S \<turnstile>\<^sub>S fboxK\<^sub>F (nat_to_string i) ( \<And>\<^sub>F l )\<^sub>S" 
proof (induct l)
case Nil
  have 1: "map (Formula_FboxK (nat_to_string i)) [] = []" by simp
  have 2: "foldr op \<and>\<^sub>F [] \<top>\<^sub>F = \<top>\<^sub>F" by simp
  thus ?case
  unfolding conj_def
  unfolding 1 2
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.Back_forw_K2)
  apply (rule_tac derivable.IW_L)
  by (rule_tac derivable.Top_R)
next
case (Cons x xs)
  have 1: "map (Formula_FboxK (nat_to_string i)) (x # xs) = (fboxK\<^sub>F nat_to_string i x) # (map (Formula_FboxK (nat_to_string i)) xs)" by simp
  show ?case
  apply (subst conj_unfold_1)
  unfolding 1
  apply (subst conj_unfold_1)
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Back_forw_K2)
  apply (rule_tac derivable.K_mon_L)
  apply (rule_tac derivable.And_R)

  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac f="fboxK\<^sub>F nat_to_string i (\<And>\<^sub>F xs)" in derivable.SingleCut)
  using cut apply simp
  using Cons apply simp
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac Id)

  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac derivable.FboxK_L)
  by (rule_tac Id)
qed

lemma conj_All: 
 shows "(\<And>x. x \<in> set List \<Longrightarrow> (loc \<turnstile>d X \<turnstile>\<^sub>S (x \<^sub>S))) \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S (\<And>\<^sub>F List)\<^sub>S"
apply (induct List arbitrary:X)
apply (subst conj_def)
apply simp 
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
apply (subst conj_unfold_1)
apply (rule_tac derivable.C_L)
apply (rule_tac derivable.And_R)
by simp+

lemma conj_FboxK_distrib : 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d (\<And>\<^sub>F (map (Formula_FboxK aa) list))\<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F aa (\<And>\<^sub>F list))\<^sub>S"
apply (induct list)
apply (subst conj_def)+
apply simp
apply (rule_tac derivable.FboxK_R)
apply (rule_tac derivable.Back_forw_K2)
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
proof -
case goal1 
  have conj_unfold_map: "(\<And>\<^sub>F map (Formula_FboxK aa) (a # list)) = (fboxK\<^sub>F aa a) \<and>\<^sub>F (\<And>\<^sub>F (map (Formula_FboxK aa) list))" using conj_unfold_1 by auto
  show ?case
  apply(subst conj_unfold_1)
  apply(subst conj_unfold_map)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.FboxK_R)
  apply (rule_tac derivable.Back_forw_K2)
  apply (rule_tac derivable.K_mon_L)
  apply (rule_tac derivable.And_R)
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac f="fboxK\<^sub>F aa (\<And>\<^sub>F list)" in derivable.SingleCut)
  using cut goal1 apply simp+
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac Id)
  by (simp add: Back_forw_K FboxK_L Id)
qed

lemma disj_lub : 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ( \<And>\<^sub>F map (\<lambda>B. B \<rightarrow>\<^sub>F A) list )\<^sub>S \<turnstile>\<^sub>S ((\<Or>\<^sub>F list)\<^sub>S) \<rightarrow>\<^sub>S (A \<^sub>S)" 
apply(induct list)
apply(subst conj_def)
apply(subst disj_def)
apply simp
apply (rule_tac derivable.W_impR_R)
apply (rule_tac derivable.IW_R)
apply (rule_tac derivable.Bot_L)
apply(subst conj_unfold_1a)
apply(subst disj_unfold_1)

apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac derivable.E_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.C_R)
apply (rule_tac derivable.Or_L)

apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac derivable.Comma_impL_disp)
apply (rule_tac derivable.E_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply simp

apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac derivable.Comma_impL_disp)
apply (rule_tac derivable.E_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.ImpR_L)
apply (rule_tac Id)

apply (rule_tac Id)
done

fun k_apply :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<^sup>_ _") where 
"k_apply Fun 0 f = f" |
"k_apply Fun (Suc x) f = Fun (k_apply Fun x f)"

lemma k_apply_unfold_bis: "k_apply Fun (Suc k) f = k_apply Fun k (Fun f) "
apply(induction k)
unfolding k_apply.simps by simp+

lemma k_apply_S_Formula_FboxA_Structure_ForwA:
  fixes loc 
  shows "loc \<turnstile>d (k_apply (Formula_FboxA a) k form)\<^sub>S \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k (form \<^sub>S) "
apply(induction k)
apply simp
apply (rule Id)
unfolding k_apply.simps
apply (rule_tac derivable.FboxA_L)
by simp

lemma k_apply_S_display_1:
  fixes loc 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d X \<turnstile>\<^sub>S (k_apply (Formula_FboxA a) k form)\<^sub>S \<longleftrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k (form \<^sub>S) "
apply rule
apply(induction k arbitrary: X)
apply simp
unfolding k_apply.simps
apply (rule_tac f="fboxA\<^sub>F a Formula_FboxA a \<^sup>k form" in derivable.SingleCut)
using cut apply simp
apply simp
using k_apply_S_Formula_FboxA_Structure_ForwA
apply (simp add: k_apply_S_Formula_FboxA_Structure_ForwA FboxA_L)

apply (induct k arbitrary: X)
apply simp
unfolding k_apply.simps
proof -
case goal1
  have assms: "loc \<turnstile>d backA\<^sub>S a X \<turnstile>\<^sub>S Structure_ForwA a \<^sup>k form \<^sub>S" by (simp add: Back_forw_A goal1(1) goal1(2))
  thus ?case
  apply (rule_tac derivable.FboxA_R)
  apply (rule_tac derivable.Back_forw_A2)
  by (simp add: goal1(1))
qed

lemma k_apply_S_display_1a:
  fixes loc 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d X \<turnstile>\<^sub>S (k_apply (Formula_FboxA a) k form)\<^sub>S \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k (form \<^sub>S) "
using k_apply_S_display_1 using cut by blast

lemma k_apply_S_display_1b:
  fixes loc 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k (form \<^sub>S) \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S (k_apply (Formula_FboxA a) k form)\<^sub>S"
using k_apply_S_display_1 using cut by blast

lemma k_apply_S_display_1diam:
  fixes loc 
  shows "loc \<turnstile>d (Structure_ForwA a) \<^sup>k (form \<^sub>S) \<turnstile>\<^sub>S X \<Longrightarrow> loc \<turnstile>d ((Formula_FdiamA a) \<^sup>k form)\<^sub>S \<turnstile>\<^sub>S X"
apply(induct k arbitrary:X)
unfolding k_apply.simps
apply simp
proof -
case goal1
  then have "loc \<turnstile>d Structure_ForwA a \<^sup>k form \<^sub>S \<turnstile>\<^sub>S backA\<^sub>S a X"
  apply (rule_tac derivable.Forw_back_A)
  by simp
 
  with goal1 have "loc \<turnstile>d Formula_FdiamA a \<^sup>k form \<^sub>S \<turnstile>\<^sub>S backA\<^sub>S a X" by simp
  thus ?case
  apply (rule_tac derivable.FdiamA_L)
  apply (rule_tac derivable.Forw_back_A2)
  by simp
qed

lemma k_apply_S_F_forw_diam:
  fixes loc
  shows "loc \<turnstile>d  X \<^sub>S \<turnstile>\<^sub>S Y \<^sub>S \<Longrightarrow> loc \<turnstile>d Structure_ForwA a \<^sup>k X \<^sub>S \<turnstile>\<^sub>S Formula_FdiamA a \<^sup>k Y \<^sub>S"
apply(induct k arbitrary:X Y)
apply simp
apply simp
apply (rule_tac derivable.FdiamA_R)
by simp

lemma k_apply_S_display_2:
  fixes loc 
  shows "loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k Y \<longleftrightarrow> loc \<turnstile>d k_apply (Structure_BackA a) k X \<turnstile>\<^sub>S Y"
apply rule
apply (induct k arbitrary: X)
apply simp
apply (metis Back_forw_A k_apply.simps(2) k_apply_unfold_bis)
apply (induct k arbitrary: X)
apply simp
by (metis Back_forw_A2 k_apply.simps(2) k_apply_unfold_bis)

lemma k_apply_S_display_2a:
  fixes loc 
  shows "loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k Y \<Longrightarrow> loc \<turnstile>d k_apply (Structure_BackA a) k X \<turnstile>\<^sub>S Y"
by (simp add: k_apply_S_display_2)

lemma k_apply_S_display_2b:
  fixes loc 
  shows "loc \<turnstile>d k_apply (Structure_BackA a) k X \<turnstile>\<^sub>S Y \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k Y"
by (simp add: k_apply_S_display_2)

lemma k_apply_S_display_2back:
  fixes loc 
  shows "loc \<turnstile>d k_apply (Structure_BackA a) k X \<turnstile>\<^sub>S Y \<longleftrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k Y"
apply rule
apply (induct k arbitrary: X)
apply simp
using k_apply_S_display_2 apply blast
apply (induct k arbitrary: X)
apply simp
using k_apply_S_display_2 by blast

lemma k_apply_elim_diamA:
  fixes loc 
  shows "loc \<turnstile>d forma \<^sub>S \<turnstile>\<^sub>S formb \<^sub>S \<Longrightarrow> loc \<turnstile>d (k_apply (Formula_FdiamA a) k forma)\<^sub>S \<turnstile>\<^sub>S (k_apply (Formula_FdiamA a) k formb)\<^sub>S "
apply (induct k)
apply simp
using FdiamA_L FdiamA_R by auto

lemma k_apply_DiamBot: 
  fixes loc
  shows "loc \<turnstile>d ( k_apply ( Formula_FdiamA A ) k \<bottom>\<^sub>F ) \<^sub>S \<turnstile>\<^sub>S I\<^sub>S "
apply (induct k)
unfolding k_apply.simps
apply (rule_tac derivable.Bot_L)
apply (rule_tac derivable.FdiamA_L)
apply (rule_tac derivable.Forw_back_A2)
apply (rule_tac derivable.A_nec_R)
by simp

lemma k_apply_DiamBot_Is: 
  fixes loc
  shows "loc \<turnstile>d ( k_apply ( Formula_FdiamA A ) k \<bottom>\<^sub>F ) \<^sub>S \<turnstile>\<^sub>S I\<^sub>S"
apply (induct k)
unfolding k_apply.simps
apply (rule_tac derivable.Bot_L)
apply (rule_tac derivable.FdiamA_L)
apply (rule_tac derivable.Forw_back_A2)
apply (rule_tac derivable.A_nec_R)
by simp

lemma k_apply_BoxDiam: 
  fixes loc
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ( k_apply ( Formula_FboxA A ) k p ) \<and>\<^sub>F ( k_apply ( Formula_FdiamA A ) k q) \<^sub>S \<turnstile>\<^sub>S ( k_apply ( Formula_FdiamA A ) k ( p\<and>\<^sub>Fq ) ) \<^sub>S "
apply (induct k)
apply simp
apply (rule Id)

apply (subst k_apply.simps)+
apply (rule_tac f="Formula_FdiamA A ( ((Formula_FboxA A) \<^sup>k p )\<and>\<^sub>F ((Formula_FdiamA A) \<^sup>k q))" in derivable.SingleCut)
using cut apply simp
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
defer
apply (rule Id)

apply (rule_tac derivable.FdiamA_L)
apply (rule_tac derivable.FdiamA_R)
by simp

lemma k_apply_S_FS:
  fixes loc 
  shows "loc \<turnstile>d X \<turnstile>\<^sub>S (k_apply (Structure_ForwA a) k Y) \<rightarrow>\<^sub>S (k_apply (Structure_ForwA a) k Z) \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S k_apply (Structure_ForwA a) k (Y \<rightarrow>\<^sub>S Z)"
apply(induct k arbitrary: X Y Z)
apply simp
apply simp
using Back_forw_A Back_forw_A2 FS_A_R by blast

lemma k_apply_S_Atom:
  fixes loc 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d X \<^sub>F \<^sub>S \<turnstile>\<^sub>S forwA\<^sub>S b (k_apply (Structure_ForwA a) k (X \<^sub>F \<^sub>S))"
apply (rule_tac f="fboxA\<^sub>F b (X \<^sub>F)" in derivable.SingleCut)
using cut apply blast
apply (rule_tac derivable.FboxA_R)
apply (rule_tac derivable.Atom)
apply simp

apply (rule_tac derivable.FboxA_L)
apply(induct k arbitrary: X a b)
apply simp
apply (rule_tac Atom)
apply simp+
apply (rule_tac derivable.Back_forw_A2)
apply (rule_tac f="X \<^sub>F" in derivable.SingleCut)
using cut apply simp
apply (rule_tac Atom)
by simp+

lemma k_apply_F_FboxA:
  fixes loc 
  shows "loc \<turnstile>d X \<^sub>S \<turnstile>\<^sub>S (Formula_FboxA a X) \<^sub>S \<Longrightarrow> loc \<turnstile>d (k_apply (Formula_FboxA a) k X) \<^sub>S \<turnstile>\<^sub>S (k_apply (Formula_FboxA a) (Suc k) X) \<^sub>S"
apply(induct k)
unfolding k_apply.simps
apply simp
apply (rule_tac derivable.FboxA_R)
apply (rule_tac derivable.FboxA_L)
by simp

lemma Swapout_R_1:
  fixes loc
  assumes "RelAKA rel \<in> set loc" and "rel alpha a = [beta]"
  shows "loc \<turnstile>d Y \<turnstile>\<^sub>S forwK\<^sub>S a forwA\<^sub>S beta X \<Longrightarrow> loc \<turnstile>d ;;\<^sub>S [Y] \<turnstile>\<^sub>S forwA\<^sub>S alpha forwK\<^sub>S a X"
apply (rule derivable.Swapout_R)
using assms by auto

lemma Bot_imp_all: "loc \<turnstile>d \<bottom>\<^sub>F \<^sub>S \<turnstile>\<^sub>S X"
apply (rule_tac derivable.IW_R)
apply (rule_tac derivable.Bot_L)
done

lemma Swapout_R_2aux:
  fixes loc
  assumes refl_rel: "RelAKA rel \<in> set loc" and "rel alpha a = [alpha]"
  shows "loc \<turnstile>d Y  \<turnstile>\<^sub>S  (Structure_ForwA alpha) \<^sup>k (forwK\<^sub>S a forwA\<^sub>S alpha X)  \<Longrightarrow> loc \<turnstile>d Y \<turnstile>\<^sub>S Structure_ForwA alpha \<^sup>(Suc k) (forwK\<^sub>S a X)"
apply(induct k arbitrary: X Y)
apply simp
apply (rule_tac derivable.I_impR2)
apply (rule_tac derivable.Bigcomma_Nil_L)
apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac derivable.Bigcomma_Cons_L)
apply (rule_tac rel=rel and beta=alpha in Swapout_R_1)
using assms apply (simp,simp, simp)

apply(rule_tac k_apply_S_display_2b)
apply(subst k_apply.simps)
apply (rule_tac derivable.Back_forw_A)
apply (rule_tac derivable.I_impR2)
apply (rule_tac derivable.Bigcomma_Nil_L)
apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac derivable.Bigcomma_Cons_L)
apply (rule_tac rel=rel and beta=alpha in Swapout_R_1)
using assms apply (simp,simp)
apply(rule_tac k_apply_S_display_2a)
by simp

lemma Swapout_R_2:
  fixes loc
  assumes refl_rel: "RelAKA rel \<in> set loc" and "rel alpha a = [alpha]"
  and cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d (fboxK\<^sub>F a (Formula_FboxA alpha \<^sup>k X))\<^sub>S  \<turnstile>\<^sub>S Structure_ForwA alpha \<^sup>k (forwK\<^sub>S a X \<^sub>S)"
apply(induct k arbitrary: X)
apply(subst k_apply.simps)+
apply (rule_tac FboxK_L)
apply (rule_tac Id)
proof - 
case goal1 
  have cut_f: "loc \<turnstile>d Formula_FboxA alpha \<^sup>k fboxK\<^sub>F a fboxA\<^sub>F alpha X \<^sub>S \<turnstile>\<^sub>S Structure_ForwA alpha \<^sup>k forwK\<^sub>S a forwA\<^sub>S alpha X \<^sub>S"
  apply (induct k)
  apply(subst k_apply.simps)+
  apply (rule_tac FboxK_L)
  apply (rule_tac FboxA_L)
  apply (rule_tac Id)
  apply(subst k_apply.simps)+
  apply (rule_tac FboxA_L)
  by simp
  
  have subst1: "fboxA\<^sub>F alpha Formula_FboxA alpha \<^sup>k X = Formula_FboxA alpha \<^sup>k fboxA\<^sub>F alpha X" by (metis k_apply.simps(2) k_apply_unfold_bis)
  show ?case
  apply(subst k_apply.simps)
  
  apply (rule_tac Swapout_R_2aux)
  using assms apply (simp,simp)
  apply(subst subst1)
  apply(rule_tac f="Formula_FboxA alpha \<^sup>k fboxK\<^sub>F a fboxA\<^sub>F alpha X" in derivable.SingleCut)
  using cut apply simp
  defer
  using cut_f apply simp
  apply(rule_tac k_apply_S_display_1b)
  using cut apply simp
  using goal1 FboxK_R k_apply_S_display_2back by blast
qed
end