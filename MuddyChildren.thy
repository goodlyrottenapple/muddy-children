theory MuddyChildren
imports Main "calculus/src/isabelle/DEAK_SE"
begin

(*
We consider classical logic, we take being dirty as the primary definition and we define being clean as the negation of being dirty.
*)



lemma Id:
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


definition digit_char_list :: "string" where
"digit_char_list = ''0123456789''"


lemma digit_char_list_length[simp]:
  shows "length digit_char_list = (10::nat)"
by (metis One_nat_def Suc_eq_plus1 digit_char_list_def eval_nat_numeral(2) eval_nat_numeral(3) list.size(3) list.size(4) nat_1_add_1 semiring_norm(26) semiring_norm(27) semiring_norm(28))


lemma digit_char_list_distinct:
  shows "distinct digit_char_list"
unfolding digit_char_list_def using distinct.simps(2)
by simp


fun nat_to_string :: "nat \<Rightarrow> string"
where
"nat_to_string n = (if n < (length digit_char_list) then [digit_char_list ! n] else 
nat_to_string (n div (length digit_char_list)) @ [digit_char_list ! (n mod (length digit_char_list))])"


lemma nEq_exE:
  fixes s s'
  shows "(\<exists>e \<in> s . e \<notin> s') \<or> (\<exists>e \<in> s'. e \<notin> s) \<Longrightarrow> (s::'a set) \<noteq> s'"
by auto

lemma digit_char_list_inject:
  fixes i j
  defines "list \<equiv> digit_char_list"
  assumes "i \<noteq> j"
  and "i < length list" "j < length list"
  shows "set (filter (\<lambda>x. x \<noteq> list ! i) list) \<noteq> set (filter (\<lambda>x. x \<noteq> list ! j) list)"
using assms(2,3,4) digit_char_list_distinct unfolding list_def digit_char_list_def 
proof -
case goal1
  then have assms: "i \<le> 9" "j \<le> 9" using digit_char_list_length by simp+
  have set_expand: "{0..9::nat} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}" by auto

  have "\<forall>ii \<in> {0,1,2,3,4,5,6,7,8,9}::nat set. \<forall>jj \<in> {0,1,2,3,4,5,6,7,8,9}::nat set. ii\<noteq>jj \<longrightarrow> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! ii) ''0123456789'') \<noteq> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! jj) ''0123456789'')"
  unfolding digit_char_list_def
  apply simp
  by ((rule conjI)?, rule nEq_exE, simp)+
  then have "\<forall>ii \<in> {0..9::nat}. \<forall>jj \<in> {0..9::nat}. ii\<noteq>jj \<longrightarrow> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! ii) ''0123456789'') \<noteq> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! jj) ''0123456789'')"
  apply(subst set_expand)+ by blast
  then have res: "\<And>ii jj. ii \<in> {0..9::nat} \<Longrightarrow> jj \<in> {0..9::nat} \<Longrightarrow> ii\<noteq>jj \<Longrightarrow> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! ii) ''0123456789'') \<noteq> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! jj) ''0123456789'')"
  by simp
 
  with assms have "i \<in> {0..9::nat}" "i \<notin> -{0..9::nat}" "j \<in> {0..9::nat}" "j \<notin> -{0..9::nat}" by auto
  show ?case
  apply(cases "i \<in> {0..9::nat}")
  apply(cases "j \<in> {0..9::nat}")
  using res goal1(1) set_expand apply simp
  using assms by simp+
qed

lemma digit_char_list_inject2:
  fixes i::nat
  shows "\<And>j. digit_char_list ! (i mod 10) = digit_char_list ! (j mod 10) \<Longrightarrow> (i mod 10) = (j mod 10)"
proof -
  case goal1
  have "i mod 10 < 10" "j mod 10 < 10" by simp+
  thus ?case using digit_char_list_inject goal1 by fastforce
qed

lemma nat_to_string_inject:
  fixes i::nat
  shows "\<And>j::nat. nat_to_string i = nat_to_string j \<Longrightarrow> i = j"
proof (induct i rule: nat_to_string.induct)
case (1 i)
  thus ?case 
  proof (cases "i < length digit_char_list")
  case goal1 
    thus ?case
    apply (cases "j < length digit_char_list")
    apply simp
    using digit_char_list_inject apply force
    apply simp
    using digit_char_list_inject by (metis (no_types, lifting) append_is_Nil_conv list.distinct(1))
  next
  case goal2
    thus ?case
    apply (cases "j < length digit_char_list")
    apply simp
    using digit_char_list_inject apply (metis append_is_Nil_conv list.distinct(1))
    apply simp
    apply(cases "j div 10 < 10")
    apply simp
    proof -
    case goal1 
      from goal1(2) have "(i div 10) = (j div 10)" "(i mod 10) = (j mod 10)" 
      apply (simp add: goal1(1) goal1(5)) using digit_char_list_inject2 goal1(2) by blast
      thus ?case by (metis mod_div_equality)
    next
    case goal2 
      then have 0: "nat_to_string (i div 10 div length digit_char_list) @ [digit_char_list ! (i div 10 mod length digit_char_list)] =
      nat_to_string (j div 10 div length digit_char_list) @ [digit_char_list ! (j div 10 mod length digit_char_list)]" by presburger
      from goal2 have 1: "nat_to_string (i div 10 div length digit_char_list) = nat_to_string (j div 10 div length digit_char_list)" by presburger
   
      with 0 have "digit_char_list ! (i div 10 mod length digit_char_list) = digit_char_list ! (j div 10 mod length digit_char_list)" by simp
      with 0 1 have "i div 10 = j div 10" "i mod 10 = j mod 10" using digit_char_list_inject2 using goal2 by blast+
      thus ?case by (metis mod_div_equality)
    qed
  qed
qed

(*fun string_to_nat_option :: "string \<Rightarrow> nat option"
where
"string_to_nat_option [] = None" |
"string_to_nat_option [x] = (if nat_of_char x \<ge> 48 \<and> nat_of_char x \<le> 48+9 then Some (nat_of_char x - 48) else None)"|
"*)


fun E :: "nat \<Rightarrow> Formula \<Rightarrow> Formula" where
"E 0 formula = \<top>\<^sub>F" |
"E (Suc x) formula = (fboxK\<^sub>F (nat_to_string (Suc x)) formula) \<and>\<^sub>F (E x formula)"


fun upto' :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"upto' x 0 = (if x = 0 then [0] else [])" |
"upto' x (Suc y) = (if x \<le> (Suc y) then (if x = (Suc y) then [(Suc y)] else (Suc y)#(upto' x y)) else [])"


definition disj :: "Formula list \<Rightarrow> Formula" ("\<Or>\<^sub>F _" 300) where
"disj list = foldr (Formula_Or) list \<bottom>\<^sub>F"

fun father' :: "nat \<Rightarrow> Formula" where
"father' 0 = \<bottom>\<^sub>F" |
"father' (Suc x) = (nat_to_string (Suc x)\<^sub>F) \<or>\<^sub>F (father' x)"



definition father :: "nat \<Rightarrow> Formula" where
"father n = \<Or>\<^sub>F map (Formula_Atprop \<circ> nat_to_string) (upto' 1 n)"


fun vision_aux :: "nat \<Rightarrow> nat \<Rightarrow> Formula" where
"vision_aux _ 0 = \<top>\<^sub>F" |
"vision_aux m (Suc n) = ((
  (((nat_to_string m) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (m-(Suc n))) ((nat_to_string m) \<^sub>F))) \<and>\<^sub>F 
  ((((nat_to_string m) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (m-(Suc n))) (((nat_to_string m) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
)
 \<and>\<^sub>F 

(
  (((nat_to_string (m-(Suc n))) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string m) ((nat_to_string (m-(Suc n))) \<^sub>F))) \<and>\<^sub>F 
  ((((nat_to_string (m-(Suc n))) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string m) (((nat_to_string (m-(Suc n))) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
)
)
  \<and>\<^sub>F vision_aux m n"


definition conj :: "Formula list \<Rightarrow> Formula" ("\<And>\<^sub>F _" 300) where
"conj list = foldr (Formula_And) list \<top>\<^sub>F"

lemma conj_unfold_1: "\<And>\<^sub>F x#list = x \<and>\<^sub>F (\<And>\<^sub>F list)" unfolding conj_def by simp

lemma conj_unfold_1a: "\<And>\<^sub>F (map f (x#list)) = (f x) \<and>\<^sub>F (\<And>\<^sub>F map f list)" unfolding conj_def by simp

lemma disj_unfold_1: "\<Or>\<^sub>F x#list = x \<or>\<^sub>F (\<Or>\<^sub>F list)" unfolding disj_def by simp


lemma conj_unfold_2:
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d (\<And>\<^sub>F list1@list2) \<^sub>S \<turnstile>\<^sub>S ((\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)) \<^sub>S"
apply (induct list1)
apply(subst conj_def)+
apply simp
apply (rule_tac derivable.C_L)
apply (rule_tac derivable.And_R)
apply (rule Id)
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
proof -
case goal1 
  have 1: "(a # list1) @ list2 = a # (list1 @ list2)" by simp
  show ?case unfolding 1
  apply(subst conj_unfold_1)
  apply(subst conj_unfold_1)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.And_R)

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac f="(\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)" in derivable.SingleCut)
  using cut apply simp
  using goal1 apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply (rule_tac Id)

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.And_R)

  apply (rule_tac f="(\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)" in derivable.SingleCut)
  using cut apply simp
  using goal1 apply simp
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  apply (rule_tac Id)

  by (rule_tac Id)
qed


lemma conj_unfold_2b:
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ((\<And>\<^sub>F list1) \<and>\<^sub>F (\<And>\<^sub>F list2)) \<^sub>S \<turnstile>\<^sub>S (\<And>\<^sub>F list1@list2) \<^sub>S"
apply(induct list1)
apply(subst conj_def)+
apply simp
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac Id)
proof -
case goal1 
  have 1: "(a # list1) @ list2 = a # (list1 @ list2)" by simp
  show ?case unfolding 1
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

  using goal1 apply simp

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
proof simp
case goal1 
  thus ?case
  apply(cases "f \<in> set list")
  apply simp
  apply (subst conj_unfold_1)
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  apply simp
  proof -
  case goal1 then have "f = a" by simp
    thus ?case
    apply (subst conj_unfold_1)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    using goal1 Id by simp
  qed
qed


lemma conj_der1b: " \<forall>f \<in> set list. loc \<turnstile>d X  \<turnstile>\<^sub>S ( f )\<^sub>S \<Longrightarrow> loc \<turnstile>d X \<turnstile>\<^sub>S ( \<And>\<^sub>F list )\<^sub>S"
apply(induct list)
apply simp 
using IW_L Top_R conj_def apply simp
proof simp
case goal1
  show ?case
  apply(subst conj_unfold_1)
  apply (rule_tac derivable.C_L)
  apply (rule_tac derivable.And_R)
  defer
  using goal1 apply simp
  using goal1 using IW_L Top_R conj_def by fastforce
qed




lemma conj_der2_aux: 
  fixes l'
  shows "\<And> l. set l' \<subseteq> set l \<Longrightarrow> loc \<turnstile>d ( \<And>\<^sub>F l )\<^sub>S \<turnstile>\<^sub>S ( \<And>\<^sub>F l' )\<^sub>S"
apply(induct l')
apply(subst (2) conj_def)
apply simp
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
proof -
case goal1
  then have "loc \<turnstile>d (\<And>\<^sub>F l) \<^sub>S \<turnstile>\<^sub>S (\<And>\<^sub>F l') \<^sub>S" by simp
  thus ?case
  apply (rule_tac derivable.C_L)
  apply (subst conj_unfold_1)
  apply (rule_tac derivable.And_R)
  apply simp
  apply(rule_tac f=a in conj_der1)
  apply (rule Id)
  using goal1 by simp
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
  apply (rule_tac f="(\<And>\<^sub>F x # xs)" in derivable.SingleCut)
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


thm conj_unfold_1
fun vision' :: "nat \<Rightarrow> Formula" where
"vision' 0 = \<top>\<^sub>F" |
"vision' (Suc x) = vision_aux (Suc x) x \<and>\<^sub>F (vision' x)"


fun vision'_aux :: "nat \<Rightarrow> nat \<Rightarrow> Formula list" where
"vision'_aux _ 0 = []" |
"vision'_aux m (Suc n) = (
  (((nat_to_string m) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (Suc n)) ((nat_to_string m) \<^sub>F))) \<and>\<^sub>F 
  ((((nat_to_string m) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (Suc n)) (((nat_to_string m) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
)
#
(
  (((nat_to_string (Suc n)) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string m) ((nat_to_string (Suc n)) \<^sub>F))) \<and>\<^sub>F 
  ((((nat_to_string (Suc n)) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string m) (((nat_to_string (Suc n)) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
)
# vision'_aux m n"


fun vision'' :: "nat \<Rightarrow> Formula list" where
"vision'' 0 = []" |
"vision'' (Suc x) = (vision'_aux (Suc x) x)@(vision'' x)"


definition vision :: "nat \<Rightarrow> Formula" where
"vision x = \<And>\<^sub>F (vision'' x)"



value "vision 3"
value "vision'_aux 3 4"
value "vision'_aux 4 3"



lemma vision'_aux_contains1 :
  assumes "0 < i \<and> i < (Suc x)"
  shows "\<And> ii. 0 < ii \<and> ii < i \<Longrightarrow> (
   (((nat_to_string (Suc x)) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string ii) ((nat_to_string (Suc x)) \<^sub>F))) \<and>\<^sub>F 
   ((((nat_to_string (Suc x)) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string ii) (((nat_to_string (Suc x)) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
  )
   \<in> set (vision'_aux (Suc x) i)"
using assms proof (induction x i rule: vision'_aux.induct)
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
    unfolding i_def vision'_aux.simps
    apply(subst (9) n'_def)
    unfolding vision'_aux.simps using n'_def by simp
  qed
qed

lemma vision'_aux_contains2 :
  assumes "0 < i \<and> i < (Suc x)"
  shows "\<And> ii. 0 < ii \<and> ii < i \<Longrightarrow> (
   (((nat_to_string ii) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (Suc x)) ((nat_to_string ii) \<^sub>F))) \<and>\<^sub>F 
   ((((nat_to_string ii) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (Suc x)) (((nat_to_string ii) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))
  )
   \<in> set (vision'_aux (Suc x) i)"
using assms proof (induction x i rule: vision'_aux.induct)
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
    unfolding i_def vision'_aux.simps
    apply(subst (9) n'_def)
    unfolding vision'_aux.simps using n'_def by simp
  qed
qed

lemma vision_contains :
  fixes i j dirty_children num_of_children
  assumes "0 < i \<and> i \<le> num_of_children" "0 < j \<and> j \<le> num_of_children"
  and "i \<noteq> j"
  shows "(((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) ((nat_to_string j) \<^sub>F))) \<and>\<^sub>F 
  ((((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) (((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))) \<in> set (vision'' num_of_children)"
using assms apply (induct num_of_children)
apply simp
proof -
case goal1 
  note g1 = goal1
  show ?case
  proof (cases "i \<le> num_of_children" ; cases "j \<le> num_of_children")
  case goal1 
    with g1 have "((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string i nat_to_string j \<^sub>F) \<and>\<^sub>F (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string i (nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)
    \<in> set (vision'' num_of_children)" by simp
    thus ?case unfolding vision''.simps by simp
  next
  case goal2 
    with g1 have j_def: "j = Suc num_of_children" by simp
    with g1 goal2 obtain num' where num'_def: "num_of_children = Suc num'" using Suc_pred less_le_trans by metis
    then have "((nat_to_string (Suc num_of_children) \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string i nat_to_string (Suc num_of_children) \<^sub>F) \<and>\<^sub>F
    (((nat_to_string (Suc num_of_children) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string i (nat_to_string (Suc num_of_children) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)
    \<in> set (vision'_aux (Suc num_of_children) num_of_children)" using g1 goal2 vision'_aux_contains1 
    by (metis le_less lessI list.set_intros(1) vision'_aux.simps(2) zero_less_Suc)
    thus ?case unfolding j_def vision''.simps by simp
  next
  case goal3 
    with g1 have i_def: "i = Suc num_of_children" by simp
    with g1 goal3 obtain num' where num'_def: "num_of_children = Suc num'" using Suc_pred less_le_trans by metis
    then have "((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string (Suc num_of_children) nat_to_string j \<^sub>F) \<and>\<^sub>F
    (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string (Suc num_of_children) (nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)
    \<in> set (vision'_aux (Suc num_of_children) num_of_children)" using g1 goal3 vision'_aux_contains2
    by (metis le_less lessI list.set_intros(1) list.set_intros(2) vision'_aux.simps(2) zero_less_Suc) 
    thus ?case unfolding i_def vision''.simps by simp
  next
  case goal4 
    with g1 have False by simp
    thus ?case ..
  qed
qed



fun no :: "nat \<Rightarrow> Formula" where
"no 0 = \<top>\<^sub>F"|
"no (Suc x) = ( ( fdiamK\<^sub>F (nat_to_string (Suc x)) (nat_to_string (Suc x)) \<^sub>F )
\<and>\<^sub>F ( fdiamK\<^sub>F (nat_to_string (Suc x)) (( (nat_to_string (Suc x) ) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) ) ) \<and>\<^sub>F ( no x)"

lemma no_suc:
  fixes loc
  shows " loc \<turnstile>d ( no (Suc (Suc x)) ) \<^sub>S \<turnstile>\<^sub>S( no (Suc x)) \<^sub>S "
apply(induction x)
apply (subst no.simps)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule Id)

apply (subst no.simps)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
by (rule Id)


lemma no_imp: 
  fixes loc
  assumes "0 < i \<and> i \<le> Suc( x)"
  shows " loc \<turnstile>d ( no (Suc x) ) \<^sub>S \<turnstile>\<^sub>S ( ( fdiamK\<^sub>F (nat_to_string i) (nat_to_string i ) \<^sub>F ) \<and>\<^sub>F ( fdiamK\<^sub>F (nat_to_string i) ( ( (nat_to_string i ) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )) ) \<^sub>S "
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
  print_facts
  apply (subst no.simps)
  apply(cases "i\<le> (Suc x)")
  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impL_disp2)
  apply (rule_tac derivable.W_impL_L)
  using goal2(1) goal2(2) apply blast

  apply (rule_tac derivable.And_L)
  apply (rule_tac derivable.Comma_impR_disp2)
  apply (rule_tac derivable.W_impR_R)
  using MuddyChildren.Id goal2(2) le_SucE by blast
qed


(* the first parameter encodes n - the number of children - 
and the second encodes j - the number of dirty children *)

fun dirty_aux :: "nat \<Rightarrow> nat \<Rightarrow> Formula" where
"dirty_aux 0 _ = \<top>\<^sub>F " |
"dirty_aux (Suc x) 0 = ((nat_to_string (Suc x) ) \<^sub>F ) \<and>\<^sub>F ( dirty_aux x 0)" |
"dirty_aux (Suc x) (Suc y) = ( ( (nat_to_string (Suc x) ) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F (dirty_aux x y )"

definition dirty' :: "nat \<Rightarrow> nat \<Rightarrow> Formula " where
"dirty' n j = (if n > j then dirty_aux n (n-j) else dirty_aux n 0)"


(* the first parameter encodes n - the number of children - 
and the second encodes j - the number of dirty children except the first one (dirty' does not say whether the first child is clean or dirty) *)

fun dirty'_aux :: "nat \<Rightarrow> nat \<Rightarrow> Formula list" where
"dirty'_aux 0 _ = []" |
"dirty'_aux (Suc x) 0 = ((nat_to_string (Suc x) ) \<^sub>F ) # (dirty'_aux x 0)" |
"dirty'_aux (Suc x) (Suc y) = ( ( (nat_to_string (Suc x) ) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) # (dirty'_aux x y)"

definition dirty :: "nat \<Rightarrow> nat \<Rightarrow> Formula " where
"dirty n j = (if n \<ge> j then \<And>\<^sub>F (dirty'_aux n (n-j)) else \<And>\<^sub>F (dirty'_aux n 0) )"  (*  else \<bottom>\<^sub>F )"  *)


value "upto' 4 4"
value "{3::nat..0}"

lemma upto'_simp1: "x \<le> y \<Longrightarrow> set (upto' x y) = {x..y}"
apply (induct y)
by auto

lemma upto'_simp2: "x > y \<Longrightarrow> set (upto' x y) = {x..y}"
apply (induct y)
by auto


definition dirty2 :: "nat \<Rightarrow> nat list \<Rightarrow> Formula " where
"dirty2 n J = (if \<forall>j \<in> (set J). n \<ge> j \<and> j > 0 then 
  \<And>\<^sub>F (map (Formula_Atprop \<circ> nat_to_string) J)@
     (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) (filter (\<lambda>x. x \<notin> set J) (upto' 1 n))) else \<top>\<^sub>F )"

value "dirty 5 4"
value "dirty2 5 [2,3,4, 5]"


fun k_apply :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<^sup>_ _") where 
"k_apply Fun 0 f = f" |
"k_apply Fun (Suc x) f = Fun (k_apply Fun x f)" 


value "PreFormula ''father'' (father n)"
value "PreFormula ''no'' (no n)"


lemma k_apply_unfold_bis: "k_apply Fun (Suc k) f = k_apply Fun k (Fun f) "
apply(induction k)
unfolding k_apply.simps by simp+


(*lemma k_apply_unfold_1:
 assumes "
 shows "k_apply f k form \<Longrightarrow> f (k_apply f (k-1) form)"


lemma minus_1_equiv: 
 assumes "k > 0"
 shows"Suc k - 1 = Suc (k - 1)"
using assms apply(induct k)
apply auto
done*)



(* to prove by induction that X |- [no^k] Y is derivable from X |- {no}^k Y is equivalent to {backward no}^k X |- Y *)
(* I wrote an implication in the lemma to be able to go on with the Muddy Children proof ! ! ! *)

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

(*************************************************************NEW****************************************)

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

(*************************************************************NEW****************************************)



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

(************************************************************* NEW *************************************************************)

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
apply (rule_tac f="(X \<^sub>F)" in derivable.SingleCut)
using cut apply blast
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


(************************************************************* NEW *************************************************************)


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



lemma vision_0:
  assumes "x > (Suc 0)"
  shows "loc \<turnstile>d ((((nat_to_string x) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (Suc 0)) ((nat_to_string x) \<^sub>F))) \<and>\<^sub>F 
  ( (((nat_to_string x) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string (Suc 0)) (((nat_to_string x) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))) )\<^sub>S \<turnstile>\<^sub>S Y \<Longrightarrow> loc \<turnstile>d (vision x)\<^sub>S \<turnstile>\<^sub>S Y"
unfolding vision_def
apply(rule_tac f="(((nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string (Suc 0) nat_to_string x \<^sub>F) \<and>\<^sub>F
(((nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string (Suc 0) (nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" in conj_der1)
apply simp
using vision'_aux_contains1
by (metis One_nat_def Suc_lessD assms le_eq_less_or_eq nat_neq_iff vision_contains zero_less_one)




lemma vision_suc_impl_vision: 
  assumes cut: "\<And>f. CutFormula f \<in> set loc"
  shows "\<And>x. loc \<turnstile>d ( vision (Suc x) )\<^sub>S \<turnstile>\<^sub>S ( vision x )\<^sub>S"
unfolding vision_def
unfolding vision''.simps
apply(rule_tac l'= "vision'' x" in conj_der2)
using cut apply simp
apply (rule_tac Id)
by simp



lemma E_impl: "\<And>x A B. loc \<turnstile>d A \<^sub>S \<turnstile>\<^sub>S B \<^sub>S \<Longrightarrow> loc \<turnstile>d ( E x A )\<^sub>S \<turnstile>\<^sub>S ( E x B )\<^sub>S"
apply (induct_tac x)
apply (subst E.simps)+
apply (rule_tac derivable.Top_L)
apply (rule_tac derivable.Top_R)

apply (subst E.simps)+

apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
apply simp

apply (rule_tac derivable.FboxK_R)
apply (rule_tac derivable.FboxK_L)
by simp

lemma E_impl2: "\<And>x A. loc \<turnstile>d ( E (Suc x) A )\<^sub>S \<turnstile>\<^sub>S ( E x A )\<^sub>S"
apply (case_tac x)
apply simp
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
apply (subst E.simps)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
by (rule_tac Id)


lemma E_impl2a: "\<And>x A B. loc \<turnstile>d ( E x A )\<^sub>S \<turnstile>\<^sub>S ( E x B )\<^sub>S \<Longrightarrow> loc \<turnstile>d ( E (Suc x) A )\<^sub>S \<turnstile>\<^sub>S ( E x B )\<^sub>S"
apply (case_tac x)
apply simp
apply (rule_tac derivable.IW_L)
apply (rule_tac derivable.Top_R)
apply (subst E.simps)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
by simp




lemma E_impl3: 
  fixes x A
  shows "\<And>i. 0 < i \<and> i \<le> (Suc x) \<Longrightarrow> loc \<turnstile>d ( E (Suc x) A )\<^sub>S \<turnstile>\<^sub>S ( fboxK\<^sub>F (nat_to_string i) A )\<^sub>S"
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
    then have assm: "loc \<turnstile>d E (Suc x) A \<^sub>S \<turnstile>\<^sub>S fboxK\<^sub>F nat_to_string i A \<^sub>S" by simp
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

lemma E_impl4:
  assumes "\<And>ag. LAgent ag \<in> set loc"
  shows "\<And>x A. loc \<turnstile>d ( E (Suc x)\<^sup>y A )\<^sub>S \<turnstile>\<^sub>S ( A )\<^sub>S"
apply(induct y)
unfolding k_apply.simps
apply (rule Id)
apply (subst E.simps)
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)
apply (rule_tac a="nat_to_string (Suc x)" in derivable.Refl_ForwK)
using assms apply simp
apply (rule_tac derivable.FboxK_L)
by simp



lemma dirty_0_simp : "\<And>i. 0 < i \<and> i \<le> x \<Longrightarrow> nat_to_string i \<^sub>F \<in> set (dirty'_aux (Suc x) 0)"
apply (induct x)
apply auto[1]
unfolding dirty'_aux.simps
by (metis le_Suc_eq list.set_intros(1) list.set_intros(2))


lemma dirty_contains :
  assumes "0 \<le> dirty_children \<and> dirty_children \<le> num_of_children"
  and "0 < i \<and> i \<le> num_of_children"
  shows "(i \<le> dirty_children \<longrightarrow> (nat_to_string i)\<^sub>F \<in> set (dirty'_aux num_of_children (num_of_children-dirty_children))) \<and>
  (i > dirty_children \<longrightarrow> (((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<in> set (dirty'_aux num_of_children (num_of_children-dirty_children)))"
apply (rule, rule)
defer
apply rule
defer
using assms apply(induct num_of_children)
apply auto[1]
proof -
case goal1
  note g1 = goal1
  show ?case
  proof (cases "dirty_children \<le> num_of_children"; cases "i \<le> num_of_children")
  case goal1 
    with g1 have assm: "nat_to_string i \<^sub>F \<in> set (dirty'_aux num_of_children (num_of_children - dirty_children))" by simp
    with goal1 g1 obtain x where Suc_x_def: "(Suc num_of_children - dirty_children) = Suc x" by (simp add: Suc_diff_le)
    then have x_def: "x = num_of_children - dirty_children" by simp
    thus ?case 
    apply(subst Suc_x_def) 
    unfolding dirty'_aux.simps
    apply(subst x_def)
    using assm by simp
  next
  case goal2 
    with g1 have False by simp
    thus ?case ..
  next
  case goal3 
    with g1 have "Suc num_of_children \<ge> dirty_children \<and> dirty_children > num_of_children" by simp
    then have "Suc num_of_children = dirty_children" by simp
    then have "nat_to_string i \<^sub>F \<in> set (dirty'_aux (Suc num_of_children) 0)" unfolding dirty'_aux.simps using dirty_0_simp
    using assms(2) goal3(2) by force
    thus ?case by (simp add: `Suc num_of_children = dirty_children`)
  next
  case goal4
    with g1 have "Suc num_of_children \<ge> dirty_children \<and> dirty_children > num_of_children" by simp
    then have "Suc num_of_children = dirty_children" by simp
    from goal4 g1 have "i = Suc num_of_children" by simp
    then have "nat_to_string (Suc num_of_children) \<^sub>F \<in> set (dirty'_aux (Suc num_of_children) 0)" unfolding dirty'_aux.simps using dirty_0_simp
    by simp
    thus ?case by (simp add: `Suc num_of_children = dirty_children` `i = Suc num_of_children`)
  qed
next
case goal2
  note g2 = goal2
  thus ?case
  using assms 
  proof (induct num_of_children)
  case goal1 thus ?case by auto[1]
  next
  case goal2
    note g2 = goal2
    show ?case
    proof (cases "dirty_children \<le> num_of_children"; cases "i \<le> num_of_children")
    case goal1
      with g2 have assm: "(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F \<in> set (dirty'_aux num_of_children (num_of_children - dirty_children))" by simp
      with goal1 g2 obtain x where Suc_x_def: "(Suc num_of_children - dirty_children) = Suc x" by (simp add: Suc_diff_le)
      then have x_def: "x = num_of_children - dirty_children" by simp
      thus ?case 
      apply(subst Suc_x_def) 
      unfolding dirty'_aux.simps
      apply(subst x_def)
      using assm by simp
    next
    case goal2
      with g2 have i_def: "i = Suc num_of_children" by simp
      with goal2 g2 obtain x where Suc_x_def: "(Suc num_of_children - dirty_children) = Suc x" by (metis Suc_diff_Suc)
      then have x_def: "x = num_of_children - dirty_children" by simp
      thus ?case 
      apply(subst Suc_x_def) 
      apply(subst i_def)+
      unfolding dirty'_aux.simps
      apply(subst x_def)
      by simp
    next
    case goal3
      with g2 have False by simp
      thus ?case ..
    next
    case goal4 
      with g2 have False by simp
      thus ?case ..
    qed
  qed
qed


lemma dirty_set:
  assumes "0 \<le> k \<and> k \<le> n"
  shows "set (dirty'_aux n (n - k)) = {(nat_to_string i)\<^sub>F | i . 0 < i \<and> i \<le> k} \<union> {((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . k < i \<and> i \<le> n}"
proof -
case goal1 
  have "{nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<subseteq> set (dirty'_aux n (n - k))" "{((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . k < i \<and> i \<le> n} \<subseteq> set (dirty'_aux n (n - k))" 
  using dirty_contains assms subsetI by fastforce+
  then have 1: "{nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . k < i \<and> i \<le> n} \<subseteq> set (dirty'_aux n (n - k))" by simp

  have "set (dirty'_aux n (n - k)) \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . k < i \<and> i \<le> n}"
  using assms apply(induct n arbitrary: k)
  apply auto[1]
  proof -
  case goal1
    note g1 = goal1
    have subset2: "{nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> n} \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> Suc n}" using Collect_mono le_SucI by fast
    have "{(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> n} \<subseteq> {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> Suc n}" using Collect_mono le_SucI by fast
    then have subset: "{nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> n} \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> Suc n}" by blast
    show ?case
    proof (cases "k \<le> n")
    case goal1
      with g1 have ih: "set (dirty'_aux n (n - k)) \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> n}" by simp
      have assm: "(nat_to_string (Suc n) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F \<in> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> Suc n}" by (metis (mono_tags, lifting) Suc_leI UnI2 goal1 le_imp_less_Suc lessI mem_Collect_eq) 
      have repl: "set ((nat_to_string (Suc n) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F # dirty'_aux n (n - k)) = {(nat_to_string (Suc n) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F} \<union> set (dirty'_aux n (n - k))" by simp
     
      from goal1 g1 obtain x where Suc_x_def: "(Suc n - k) = Suc x" using Suc_diff_le by blast
      then have x_def: "x = n - k" by simp
      thus ?case 
      apply(subst Suc_x_def) 
      unfolding dirty'_aux.simps
      apply(subst x_def)
      apply(subst repl)
      using ih assm subset by blast
    next
    case goal2
      thus ?case
      proof (cases "0 < n")
      case goal1
        with g1 have k_def: "k = Suc n" by simp
        have 0: "{(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. n < i \<and> i \<le> n}= {}" by simp
        have 1: "nat_to_string (Suc n)\<^sub>F \<in> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> Suc n}" by blast
        from g1 goal1 have "set (dirty'_aux n (n - n)) \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> n} \<union> {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. n < i \<and> i \<le> n}" by blast
        then have "set (dirty'_aux n 0) \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> n}" using 0 by (metis (mono_tags, lifting) diff_self_eq_0 sup_bot.right_neutral)
       
        then have 2: "set (dirty'_aux (Suc n) 0) \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> Suc n}"
        unfolding dirty'_aux.simps using 1 subset2 by simp
        show ?case 
        apply (subst k_def)+ using 2 by (metis (mono_tags, lifting) UnI1 diff_self_eq_0 subsetCE subsetI)
      next
      case goal2 
        with g1 assms have 0: "n = 0" "k = Suc 0" by simp+
        have "set (dirty'_aux (Suc 0) 0) \<subseteq> {nat_to_string 1 \<^sub>F}" unfolding dirty'_aux.simps by simp
        thus ?case unfolding 0 by fastforce 
      qed
    qed
  qed

  then have "set (dirty'_aux n (n - k)) \<subseteq> {nat_to_string i \<^sub>F |i. 0 < i \<and> i \<le> k} \<union> {((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . k < i \<and> i \<le> n}" by blast
  with 1 show ?case by blast
qed

lemma dirty_vision_der : 
  fixes dirty_children num_of_children i j
  assumes "0 \<le> dirty_children \<and> dirty_children \<le> num_of_children"
  and "0 < i \<and> i \<le> num_of_children" "0 < j \<and> j \<le> num_of_children"
  and "i \<noteq> j"
  shows "(j \<le> dirty_children \<longrightarrow> loc \<turnstile>d ( dirty num_of_children dirty_children \<and>\<^sub>F vision num_of_children )\<^sub>S \<turnstile>\<^sub>S fboxK\<^sub>F (nat_to_string i) ( (nat_to_string j)\<^sub>F )\<^sub>S) \<and>
  (j > dirty_children \<longrightarrow> loc \<turnstile>d ( dirty num_of_children dirty_children \<and>\<^sub>F vision num_of_children )\<^sub>S \<turnstile>\<^sub>S fboxK\<^sub>F (nat_to_string i) ( ((nat_to_string j)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )\<^sub>S)"
apply rule
apply rule
defer
proof rule
case goal1 
  thus ?case
  proof (cases "dirty_children < num_of_children")
  case goal1
    have 1: "loc \<turnstile>d ((\<And>\<^sub>F dirty'_aux num_of_children (num_of_children - dirty_children)) \<and>\<^sub>F
    vision num_of_children) \<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F (nat_to_string i) ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<^sub>S"
    unfolding dirty_def unfolding vision_def
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impL_disp2)
    apply(rule_tac f="(nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F" in conj_der1)
   
    apply (rule_tac derivable.Comma_impL_disp)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply(rule_tac f="(((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) ((nat_to_string j) \<^sub>F))) \<and>\<^sub>F 
    ((((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) (((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))" in conj_der1)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impL_disp2)
    apply (rule_tac derivable.W_impL_L)
    apply (rule_tac derivable.ImpR_L)
    apply (rule_tac Id)+
    using vision_contains assms goal1 apply simp
  
    using dirty_contains assms goal1 by auto
  
    then show ?case unfolding dirty_def using goal1 by simp
  next
  case goal2 
    then have False using less_le_trans assms(3) by blast
    thus ?case ..
  qed
next
case goal2 
  thus ?case
  proof (cases "dirty_children < num_of_children")
  case goal1
    have 1: "loc \<turnstile>d ((\<And>\<^sub>F dirty'_aux num_of_children (num_of_children - dirty_children)) \<and>\<^sub>F
    vision num_of_children) \<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F (nat_to_string i) (nat_to_string j \<^sub>F)) \<^sub>S"
    unfolding dirty_def unfolding vision_def
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impL_disp2)
    apply(rule_tac f="(nat_to_string j \<^sub>F)" in conj_der1)
   
    apply (rule_tac derivable.Comma_impL_disp)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply(rule_tac f="(((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) ((nat_to_string j) \<^sub>F))) \<and>\<^sub>F 
    ((((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) (((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))" in conj_der1)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    apply (rule_tac derivable.ImpR_L)
    apply (rule_tac Id)+
    using vision_contains assms goal1 apply simp
  
    using dirty_contains assms goal1 by auto
  
    then show ?case unfolding dirty_def using goal1 by simp
  next
  case goal2
    then have 0: "dirty_children = num_of_children" using antisym_conv2 assms(1) by blast
    have 1: "loc \<turnstile>d ((\<And>\<^sub>F (dirty'_aux num_of_children 0)) \<and>\<^sub>F (vision num_of_children)) \<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F nat_to_string i (nat_to_string j \<^sub>F)) \<^sub>S"
    unfolding dirty_def unfolding vision_def
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impL_disp2)
    apply(rule_tac f="(nat_to_string j \<^sub>F)" in conj_der1)
   
    apply (rule_tac derivable.Comma_impL_disp)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply(rule_tac f="(((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) ((nat_to_string j) \<^sub>F))) \<and>\<^sub>F 
    ((((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (fboxK\<^sub>F (nat_to_string i) (((nat_to_string j) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)))" in conj_der1)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    apply (rule_tac derivable.ImpR_L)
    apply (rule_tac Id)+
    using vision_contains assms goal2 apply simp
  
    using dirty_contains assms goal2 0 by (metis diff_is_0_eq)
    then show ?case unfolding dirty_def using goal2 by (simp add: "0")
  qed
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
  by (simp add: Back_forw_K FboxK_L MuddyChildren.Id)
qed


lemma dirty2_vision_der:
  fixes k n J J' j
assumes "0 \<le> (Suc k) \<and> (Suc k) \<le> n" 
  and "set J \<subseteq> {1..n}"
  and "j \<in> set J"
  and "set J' \<equiv> set J - {j}"
  and cut: "\<And>f. CutFormula f \<in> set loc"
shows "loc \<turnstile>d (dirty2 n J \<^sub>S) ;\<^sub>S (vision n \<^sub>S) \<turnstile>\<^sub>S (fboxK\<^sub>F nat_to_string j (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F dirty2 n J')) \<^sub>S"
proof -
case goal1
  from assms have cond: "\<forall>j\<in>set J. j \<le> n \<and> 0 < j" "\<forall>j\<in>set J'. j \<le> n \<and> 0 < j" by auto

  have 1: "loc \<turnstile>d (\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J) @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J]))) \<^sub>S \<turnstile>\<^sub>S ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J') @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J']))) \<^sub>S"
  apply(rule_tac f= "(\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J))) \<and>\<^sub>F ((\<And>\<^sub>F (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])))" in derivable.SingleCut)
  using cut apply blast
  apply(rule_tac conj_unfold_2)
  using cut apply blast
  apply(rule_tac derivable.ImpR_R)
  apply (rule_tac derivable.Comma_impR_disp)
  apply(rule_tac f= "(\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J'))) \<and>\<^sub>F ((\<And>\<^sub>F (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J'])))" in derivable.SingleCut)
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
    apply (cases "f \<in> set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])")
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    apply(rule_tac f=f in conj_der1)
    apply(rule Id)
    apply blast
    proof -
    case goal1
      then have 0: "f \<in> set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J']) - set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])" using Set.DiffI by blast
      from assms have "set (upto' 1 n) = {1..n}" using upto'_simp1 by simp
      with assms have 1: "set [x\<leftarrow>upto' 1 n . x \<notin> set J'] = {1..n} - (set J - {j})" and 2: "set [x\<leftarrow>upto' 1 n . x \<notin> set J] = {1..n} - (set J)" by auto
      
      
      from assms have "set J - {j} \<subseteq> {1..n}" "{j} \<subseteq> {1..n}" by auto
      with assms(2,3) have 3: "set [x\<leftarrow>upto' 1 n . x \<notin> set J'] - set [x\<leftarrow>upto' 1 n . x \<notin> set J] = {j}"
      apply(subst 1)
      apply(subst 2)
      by auto
      
      have "set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J']) - set (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J]) =
      image ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) ((set [x\<leftarrow>upto' 1 n . x \<notin> set J']) - set [x\<leftarrow>upto' 1 n . x \<notin> set J])"
      proof -
        have "\<forall>F f. F \<noteq> {} \<or> (f\<Colon>Formula) \<notin> F"
          by blast
        hence f1: "set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J]) \<noteq> {}"
          using "0" by blast
        have f2: "set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J]) - insert (((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j) (((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) ` {}) = {}"
          by (metis (no_types) Diff_eq_empty_iff `set [x\<leftarrow>upto' 1 n . x \<notin> set J'] - set [x\<leftarrow>upto' 1 n . x \<notin> set J] = {j}` image_diff_subset image_insert image_set)
        hence f3: "insert (((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j) (set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J]) - {((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j}) = ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) ` {j}"
          by blast
        have "((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) j \<in> set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J']) - set (map ((\<lambda>cs. (cs \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [n\<leftarrow>upto' 1 n . n \<notin> set J])"
          using f2 f1 by blast
        thus ?thesis
          using f3 by (metis `set [x\<leftarrow>upto' 1 n . x \<notin> set J'] - set [x\<leftarrow>upto' 1 n . x \<notin> set J] = {j}` insert_Diff)
      qed
      
      with 0 3 have f_def: "f = (nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F" by (metis (no_types, lifting) comp_apply imageE singletonD)
      thus ?case
      unfolding f_def
      apply (rule_tac derivable.Comma_impL_disp2)
      apply (rule_tac derivable.W_impL_L)
      by (rule_tac Id)
    qed
  qed


  have subst1: "map ((\<lambda>x. fboxK\<^sub>F nat_to_string j x \<^sub>F) \<circ> nat_to_string) J @ map ((\<lambda>x. fboxK\<^sub>F nat_to_string j ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J] = 
    map (\<lambda>x. fboxK\<^sub>F nat_to_string j x) (map ((\<lambda>x. x \<^sub>F) \<circ> nat_to_string) J @ map ((\<lambda>x. ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n .  x \<notin> set J])" by simp


  have "loc \<turnstile>d ((\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J) @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J]))) \<^sub>S) ;\<^sub>S (vision n \<^sub>S) \<turnstile>\<^sub>S 
    (fboxK\<^sub>F nat_to_string j (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F (\<And>\<^sub>F ((map (Formula_Atprop \<circ> nat_to_string) J') @ (map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J']))))) \<^sub>S"
  apply(rule_tac f ="fboxK\<^sub>F nat_to_string j (\<And>\<^sub>F map (Formula_Atprop \<circ> nat_to_string) J @ map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])" in SingleCut)
  using cut apply blast
  defer
  using FboxK_L FboxK_R 1 apply blast
  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. fboxK\<^sub>F nat_to_string j (x \<^sub>F)) \<circ> nat_to_string) J @ map ((\<lambda>x. fboxK\<^sub>F nat_to_string j ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])" in SingleCut)
  using cut apply simp
  defer
  apply(subst subst1)
  using cut conj_box_distrib apply blast
  apply(rule_tac f ="(\<And>\<^sub>F map ((\<lambda>x. fboxK\<^sub>F nat_to_string j (x \<^sub>F)) \<circ> nat_to_string) J) \<and>\<^sub>F (\<And>\<^sub>F map ((\<lambda>x. fboxK\<^sub>F nat_to_string j ((x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])" in SingleCut)
  using cut apply simp
  defer
  apply(rule_tac conj_unfold_2b)
  using cut apply simp
  apply (rule_tac derivable.Comma_impL_disp2)
  apply(rule_tac f ="(\<And>\<^sub>F map (Formula_Atprop \<circ> nat_to_string) J) \<and>\<^sub>F (\<And>\<^sub>F map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 n . x \<notin> set J])" in SingleCut)
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
unfolding vision_def
value "vision 2"
thm conj_der2b
  sorry
  
  thus ?case unfolding dirty2_def using cond by simp
qed

lemma dirty_vision_der2 : 
  assumes "0 \<le> (Suc k) \<and> (Suc k) \<le> n" 
  and cut: "\<And>f. CutFormula f \<in> set loc"
  shows "loc \<turnstile>d ((nat_to_string (Suc k) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F \<^sub>S) ;\<^sub>S
  (backK\<^sub>S nat_to_string (Suc k) (dirty n (Suc k) \<^sub>S) ;\<^sub>S (vision n \<^sub>S)) \<turnstile>\<^sub>S dirty n k \<^sub>S"
proof -
case goal1
  def dv_l1 \<equiv> "map (\<lambda>i. (nat_to_string i)\<^sub>F) (upto' 1 k)"
  def dv_l2 \<equiv> "map (\<lambda>i. (((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )) (upto' ((Suc k)+1) n)"

  have 0: "{i::nat. 0 < i \<and> i < (Suc k)} = {1::nat..k}" "{i::nat. (Suc k) < i \<and> i \<le> n} = {((Suc k)+1)..n}" by auto
  with goal1 have 1: "(set (upto' 1 k)) = {1::nat..k}" "(set (upto' ((Suc k)+1) n)) = {((Suc k)+1)..n}" using upto'_simp1
  apply (metis One_nat_def Suc_eq_plus1 atLeastatMost_empty discrete less_Suc_eq list.set(1) upto'.simps(1) zero_less_Suc)
  using upto'_simp1 upto'_simp2 by (metis assms(1) discrete le_eq_less_or_eq)

  obtain dv_s1 dv_s2 where d_and_v_set_def: "dv_s1 = {(nat_to_string i)\<^sub>F | i . 0 < i \<and> i < (Suc k)}" "dv_s2 = {((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . (Suc k) < i \<and> i \<le> n}" by simp
  then have 2: "set dv_l1 = image (\<lambda>i. nat_to_string i \<^sub>F) (set (upto' 1 k))" "set dv_l2 = image (\<lambda>i. (((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )) (set (upto' ((Suc k)+1) n))" unfolding dv_l1_def dv_l2_def by simp+
  with 0 1 have "image (\<lambda>i. nat_to_string i \<^sub>F) (set (upto' 1 k)) = dv_s1" "image (\<lambda>i. (((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )) (set (upto' ((Suc k)+1) n)) = dv_s2" unfolding d_and_v_set_def by blast+
  with 2 have "set dv_l1 = dv_s1" "set dv_l2 = dv_s2" by simp+
  then have 3: "set (dv_l1@dv_l2) = dv_s1 \<union> dv_s2" by simp

  have 30: "set (dirty'_aux n (n - k)) = {(nat_to_string i)\<^sub>F | i . 0 < i \<and> i \<le> k} \<union> {((nat_to_string i)\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F | i . k < i \<and> i \<le> n}"
  using assms dirty_set by simp

  have "{i . 0 < i \<and> i \<le> k} = {i . 0 < i \<and> i < Suc k}" by fastforce
  then have 31: "{nat_to_string i \<^sub>F | i . 0 < i \<and> i \<le> k} = {nat_to_string i \<^sub>F | i . 0 < i \<and> i < Suc k}" by blast

  from assms have "{i::nat. k < i \<and> i \<le> n} = {i::nat. Suc k < i \<and> i \<le> n} \<union> {(Suc k)}" by auto
  then have 32: "{(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. k < i \<and> i \<le> n} = {(nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F |i. Suc k < i \<and> i \<le> n} \<union> {(nat_to_string (Suc k) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F}" by blast
  with 30 31 have "set (dirty'_aux n (n - k)) = dv_s1 \<union> dv_s2 \<union> {(nat_to_string (Suc k) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F}" unfolding d_and_v_set_def by simp

  with 3 have 4: "set (dirty'_aux n (n - k)) = set (((nat_to_string (Suc k) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)#dv_l1@dv_l2)" by simp

  def bdv_s1 \<equiv> "image (Formula_FboxK (nat_to_string (Suc k))) dv_s1"
  def bdv_s2 \<equiv> "image (Formula_FboxK (nat_to_string (Suc k))) dv_s2"

  def bdv_l1 \<equiv> "map (Formula_FboxK (nat_to_string (Suc k))) dv_l1"
  def bdv_l2 \<equiv> "map (Formula_FboxK (nat_to_string (Suc k))) dv_l2"


  have "\<And>i. 0 < i \<and> i < (Suc k) \<Longrightarrow> loc \<turnstile>d dirty n (Suc k) \<and>\<^sub>F vision n \<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F nat_to_string (Suc k) (nat_to_string i \<^sub>F)) \<^sub>S" using assms dirty_vision_der
  proof -
    fix i :: nat
    assume a1: "0 < i \<and> i < Suc k"
    have "\<And>na. \<not> na < Suc k \<or> na < n" using assms
    by (meson goal1 less_imp_le_nat less_le_trans)
    hence "i < n" using a1 by blast
    thus "loc \<turnstile>d dirty n (Suc k) \<and>\<^sub>F vision n \<^sub>S \<turnstile>\<^sub>S fboxK\<^sub>F nat_to_string (Suc k) nat_to_string i \<^sub>F \<^sub>S"
    using a1 dirty_vision_der goal1 less_imp_le_nat nat_neq_iff assms by blast
  qed

  then have 5: "\<forall>x\<in>bdv_s1. (loc \<turnstile>d ((dirty n (Suc k)) \<and>\<^sub>F vision n) \<^sub>S \<turnstile>\<^sub>S (x \<^sub>S))"
  unfolding bdv_s1_def d_and_v_set_def by blast

  have "\<And>i. (Suc k) < i \<and> i \<le> n \<Longrightarrow> loc \<turnstile>d dirty n (Suc k) \<and>\<^sub>F vision n \<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F nat_to_string (Suc k) ((nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<^sub>S" using assms dirty_vision_der
  proof -
    fix i :: nat
    assume a1: "(Suc k) < i \<and> i \<le> n"
    thus "loc \<turnstile>d dirty n (Suc k) \<and>\<^sub>F vision n \<^sub>S \<turnstile>\<^sub>S (fboxK\<^sub>F nat_to_string (Suc k) ((nat_to_string i \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<^sub>S"
    using dirty_vision_der goal1 by (metis assms(1) le_less_trans nat_neq_iff zero_less_Suc)
  qed

  then have 6: "\<forall>x\<in>bdv_s2. (loc \<turnstile>d ((dirty n (Suc k)) \<and>\<^sub>F vision n) \<^sub>S \<turnstile>\<^sub>S (x \<^sub>S))"
  unfolding bdv_s2_def d_and_v_set_def by blast

  with 3 5 have "\<forall>x\<in>set (bdv_l1 @ bdv_l2).(loc \<turnstile>d ((dirty n (Suc k)) \<and>\<^sub>F vision n) \<^sub>S \<turnstile>\<^sub>S (x \<^sub>S))"
  by (metis UnE `set dv_l1 = dv_s1` `set dv_l2 = dv_s2` bdv_l1_def bdv_l2_def bdv_s1_def bdv_s2_def set_append set_map)

  then have 7: "loc \<turnstile>d (dirty n (Suc k) \<and>\<^sub>F vision n)\<^sub>S \<turnstile>\<^sub>S (\<And>\<^sub>F bdv_l1 @ bdv_l2)\<^sub>S" 
  apply(rule_tac conj_All) by simp

  show ?case
  apply (rule_tac f = "((nat_to_string (Suc k) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<and>\<^sub>F (\<And>\<^sub>F dv_l1@dv_l2)" in derivable.SingleCut)
  using cut apply simp
  apply (rule_tac derivable.And_R)
  defer
  apply (rule Id)
  defer
  apply (rule_tac derivable.Back_forw_K)
  apply (rule_tac f = "fboxK\<^sub>F nat_to_string (Suc k) (\<And>\<^sub>F dv_l1@dv_l2)" in derivable.SingleCut)
  using cut apply simp
  defer
  apply (rule_tac derivable.FboxK_L)
  apply (rule_tac Id)
  proof -
  case goal1 
    have "loc \<turnstile>d (\<And>\<^sub>F ((nat_to_string (Suc k) \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)#dv_l1 @ dv_l2) \<^sub>S \<turnstile>\<^sub>S dirty n k \<^sub>S"
    apply (rule_tac l'="dirty'_aux n (n - k)" in conj_der2)
    using cut apply simp unfolding dirty_def using assms 
    apply (simp add: MuddyChildren.Id)
    using 4 by simp
    thus ?case using conj_unfold_1 by simp
  next
  case goal2
    show ?case
    apply (rule_tac f="(\<And>\<^sub>F bdv_l1 @ bdv_l2)" in derivable.SingleCut)
    using cut apply simp
    apply (rule_tac f="dirty n (Suc k) \<and>\<^sub>F vision n" in derivable.SingleCut)
    using cut apply simp
    apply (rule_tac derivable.And_R)
    apply (rule_tac Id)+
    using 7 apply simp
    unfolding bdv_l1_def bdv_l2_def using conj_FboxK_distrib by (metis map_append cut)
  qed
qed


definition preFormula_father :: "nat \<Rightarrow> Locale" where
"preFormula_father n = PreFormula (''father''@(nat_to_string n)) (father n)"

definition preFormula_no :: "nat \<Rightarrow> Locale" where
"preFormula_no n = PreFormula (''no''@(nat_to_string n)) (no n)"



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
  shows "loc \<turnstile>d ((dirty2 (Suc n) J) \<and>\<^sub>F (k_apply (E (Suc n)) (Suc k) (vision (Suc n))))\<^sub>S \<turnstile>\<^sub>S 
    (fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) (k_apply (Formula_FboxA (''no'' @ nat_to_string (Suc n))) k (fboxK\<^sub>F (nat_to_string j) (nat_to_string j) \<^sub>F)) )\<^sub>S"
using assms(1,2,3,4)
proof(induct k arbitrary:j J)
case 0
then obtain j where J_contains: "set J = {j}" using card_eq_SucD by blast

have set_eq: "{1..Suc n} - {j} = set ([x \<leftarrow> upto' 1 (Suc n). x\<noteq>j])" using upto'_simp1 0(1) by auto

have list_eq: "[x\<leftarrow>upto' 1 (Suc n) . x \<notin> set J] = [x\<leftarrow>upto' 1 (Suc n) . x \<noteq> j]" using J_contains by simp
with 0 have j_range: "0 < j \<and> j \<le> Suc n" by (simp add: J_contains)

have f_subst: "((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) = ((\<lambda>x. (nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" by auto


have f_subst2: "\<And>j. (\<lambda>h. ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string h \<^sub>F) \<and>\<^sub>F (((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) =
(\<lambda>h. (\<lambda>x. ((nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string x \<^sub>F)) h \<and>\<^sub>F (\<lambda>y. (((nat_to_string y \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string y \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) h )" by simp

have f_subst3: "\<And>j. (\<lambda>h. (\<lambda>x. ((nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string x \<^sub>F)) h \<and>\<^sub>F (\<lambda>y. (((nat_to_string y \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string y \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) h ) = 
(\<lambda>h. ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string h \<^sub>F) \<and>\<^sub>F (((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))" by simp


def left \<equiv> "(\<lambda>x. ((nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string x \<^sub>F))"
def right \<equiv> "(\<lambda>y. (((nat_to_string y \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string y \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F))"

have 1: "\<forall>h \<in> {1..Suc n} - {j}.
  loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S ((fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)))  \<^sub>S)"
apply rule
apply(rule_tac FboxK_R)
apply(rule_tac Back_forw_K2)
apply(rule_tac ImpR_R)
apply(rule_tac Back_forw_K)
apply(rule_tac FS_K_R)
apply (rule_tac derivable.Comma_impR_disp)

apply (rule_tac f="fdiamK\<^sub>F nat_to_string j (((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<and>\<^sub>F (nat_to_string h \<^sub>F))" in derivable.SingleCut)
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
apply (rule_tac derivable.Bot_L)

apply (rule_tac f="(fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) \<and>\<^sub>F (fdiamK\<^sub>F nat_to_string j (nat_to_string h \<^sub>F))" in derivable.SingleCut)
using cut apply blast
defer

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

apply (rule_tac derivable.E_L)

apply (rule_tac derivable.And_R)
apply (rule_tac derivable.FdiamK_R)
apply (rule_tac Id)

apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac derivable.W_impR_R)


apply (rule_tac derivable.And_L)
apply (rule_tac derivable.Comma_impR_disp2)
apply (rule_tac f="vision (Suc n)" in derivable.SingleCut)
using cut apply blast
apply(rule E_impl4)
using agent apply simp
apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac f="\<And>\<^sub>F map (\<lambda>h. fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) [h\<leftarrow>upto' 1 (Suc n) .  h \<noteq> j]" in derivable.SingleCut)
using cut apply blast
defer
apply(rule_tac f="fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)" in conj_der1)
apply(rule Id)
using set_eq apply fastforce
apply (rule_tac derivable.Comma_impR_disp2)
thm conj_der2
unfolding vision_def

apply(rule_tac l'="map (\<lambda>x. (left x) \<and>\<^sub>F (right x) ) [h\<leftarrow>upto' 1 (Suc n) . h \<noteq> j]" in conj_der2)
using cut apply simp

apply(rule_tac f="(\<And>\<^sub>F map left [h\<leftarrow>upto' 1 (Suc n) . h \<noteq> j]) \<and>\<^sub>F (\<And>\<^sub>F map right [h\<leftarrow>upto' 1 (Suc n) . h \<noteq> j])" in SingleCut)
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
unfolding dirty2_def
apply(rule_tac f="\<And>\<^sub>F map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 (Suc n) . x \<noteq> j]" in SingleCut)
using cut apply simp
apply(subst list_eq)


apply(rule_tac l="map (Formula_Atprop \<circ> nat_to_string) J @ map ((\<lambda>x. (x \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<circ> nat_to_string) [x\<leftarrow>upto' 1 (Suc n) . x \<noteq> j]" in conj_der2b)
using cut apply simp
using j_range J_contains using MuddyChildren.Id apply auto[1]
apply simp
apply (rule_tac derivable.Comma_impR_disp)

apply(subst f_subst)

apply (rule_tac E_L)
apply (simp add: conj_impl_fold cut)

proof -
case goal1

have "set [h\<leftarrow>upto' 1 (Suc n) . h \<noteq> j] = { h. 0 < h \<and> h \<le> Suc n \<and> h\<noteq>j }" using upto'_simp1 by auto

then have a: "set (map (\<lambda>h. ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string h \<^sub>F) \<and>\<^sub>F 
  (((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) [h\<leftarrow>upto' 1 (Suc n) . h \<noteq> j]) =
  image (\<lambda>h. ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j nat_to_string h \<^sub>F) \<and>\<^sub>F 
  (((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F nat_to_string j (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F)) { h. 0 < h \<and> h \<le> Suc n \<and> h\<noteq>j }" by simp
then have b: "\<dots> = { (((nat_to_string h) \<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F (nat_to_string j) (nat_to_string h) \<^sub>F) \<and>\<^sub>F 
  (((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxK\<^sub>F (nat_to_string j) (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) | h. 0 < h \<and> h \<le> Suc n \<and> h\<noteq>j }" by blast

then have "\<dots> \<subseteq> set (vision'' (Suc n))" using vision_contains j_range by blast
with a b show ?case by (simp add: left_def)
qed

with set_eq have 2: "\<forall>h \<in> set ([x \<leftarrow> upto' 1 (Suc n). x\<noteq>j]).
  loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S ((fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)))  \<^sub>S)" by simp

then have 3: "\<forall>f\<in>set (map (\<lambda>x. fboxK\<^sub>F nat_to_string j ((nat_to_string x \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F))) [x \<leftarrow> upto' 1 (Suc n). x\<noteq>j]).
  loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S (f \<^sub>S)" using  imageE set_map
proof -
  have f1: "\<forall>h. h \<in>  set ([x \<leftarrow> upto' 1 (Suc n). x\<noteq>j]) \<longrightarrow>
  loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n) \<^sub>S) ;\<^sub>S (father (Suc n) \<^sub>S) \<turnstile>\<^sub>S ((fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)))  \<^sub>S)"
    by (metis 2)
  thus ?thesis
    using set_map by (metis (no_types, lifting) imageE)
qed


have fboxK_map_subst: "\<And>list. map (\<lambda>h. fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F))) list =  map (Formula_FboxK (nat_to_string j))  (map (\<lambda>h. ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F))) list)" by simp
have map_subst2: "map (\<lambda>h. (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)) (upto' 1 (Suc n)) = map (\<lambda>B. B \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)) (map (Formula_Atprop \<circ> nat_to_string) (upto' 1 (Suc n)))" by simp
have map_subs1: "set (upto' 1 (Suc n)) = set ([h\<leftarrow>upto' 1 (Suc n) .  h \<noteq> j]) \<union> {j}" using upto'_simp1
by (metis "0.prems"(1) "0.prems"(2) J_contains One_nat_def Un_insert_right `{1..Suc n} - {j} = set [x\<leftarrow>upto' 1 (Suc n) . x \<noteq> j]` insert_Diff insert_subset sup_bot.right_neutral)

then have map_subs2: "set (upto' 1 (Suc n)) = set (j#[h\<leftarrow>upto' 1 (Suc n) .  h \<noteq> j])" by simp

have "loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc 0 vision (Suc n)) \<^sub>S \<turnstile>\<^sub>S 
  (fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>0 fboxK\<^sub>F nat_to_string j (nat_to_string j \<^sub>F)) \<^sub>S"
 apply (subst k_apply.simps(1))


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
      apply (rule_tac rel=rel and beta="(''father'' @ nat_to_string (Suc n))" in Swapout_R_1)
      using rel_refl apply (simp, simp)

apply (rule_tac derivable.Back_forw_K2)
      apply (rule_tac f = "(One\<^sub>F (''father'' @ nat_to_string (Suc n))) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)" in derivable.SingleCut)
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
      apply (rule_tac f = "One\<^sub>F (''father'' @ nat_to_string (Suc n))" in derivable.SingleCut)
      using cut apply simp
apply (rule_tac derivable.One_R)

      apply (rule_tac f="(father (Suc n))" in derivable.Pre_L)
      using preFather unfolding preFormula_father_def apply blast
apply (rule_tac derivable.Comma_impL_disp)
apply (rule_tac derivable.Comma_impR_disp2)

defer
apply (rule_tac derivable.Reduce_R)
apply (rule_tac derivable.ImpR_L)

apply (rule_tac derivable.Atom)
apply simp

apply (rule_tac derivable.One_R)

apply (rule_tac derivable.Comma_impR_disp)
apply (rule_tac derivable.E_L)

      apply (rule_tac f = "\<And>\<^sub>F map (\<lambda>h. fboxK\<^sub>F nat_to_string j ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F))) [h \<leftarrow> upto' 1 (Suc n). h\<noteq>j]" in derivable.SingleCut)
      using cut apply simp
apply(rule_tac conj_der1b)
using 3 apply blast
      apply (rule_tac f = "fboxK\<^sub>F nat_to_string j (\<And>\<^sub>F map (\<lambda>h. ((nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F))) [h \<leftarrow> upto' 1 (Suc n). h\<noteq>j])" in derivable.SingleCut)
using cut apply simp
apply(subst fboxK_map_subst)
using cut conj_box_distrib apply blast
apply (rule_tac derivable.FboxK_L)
unfolding father_def
apply (rule_tac f = "(\<And>\<^sub>F map (\<lambda>h. (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)) (upto' 1 (Suc n)))" in derivable.SingleCut)
using cut apply simp
defer
apply(subst map_subst2)
using disj_lub
apply(rule_tac disj_lub)
using cut apply simp


apply(rule_tac l="map (\<lambda>h. (nat_to_string h \<^sub>F) \<rightarrow>\<^sub>F (nat_to_string j \<^sub>F)) (j#[h\<leftarrow>upto' 1 (Suc n) .  h \<noteq> j])" in conj_der2b)
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


thus ?case using J_contains 0 by simp

  next
(* -------------------- case N = suc, K = suc -------------------- 
 n children, k+1 dirty children *)
  case (Suc k)


then obtain J' where J'_def: "set J' = set J - {j}" by (meson set_removeAll)
then obtain j' where j'_def: "j' \<in> set J'" by (metis Diff_empty List.finite_set Suc(4) Suc.prems(4) card_Diff_insert card_eq_SucD diff_Suc_1 empty_iff insert_subset order_refl)

with Suc J'_def have "card (set J') = Suc k" by simp
with Suc have ih: " \<forall>j\<in>set J'. loc \<turnstile>d (dirty2 (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )\<^sub>S \<turnstile>\<^sub>S (
  fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j (nat_to_string j \<^sub>F)) \<^sub>S" using Diff_subset Suc_leD J'_def subsetCE subsetI
proof -
  have "set J' \<subseteq> {1..Suc n}"
    by (metis (no_types) Diff_subset Suc.prems(2) J'_def subsetCE subsetI)
  thus ?thesis
    by (meson Suc.hyps Suc.prems(1) Suc_leD `card (set J') = Suc k`)
qed

(*proof (cases "j \<in> set J'")
case goal1
show ?case
        apply (rule_tac f="fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j nat_to_string j \<^sub>F" in derivable.SingleCut)
        using cut apply simp
        defer
apply (rule_tac derivable.FboxA_R)
apply (rule_tac derivable.FboxA_L)
apply(rule_tac k_apply_F_FboxA)

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
    apply(rule_tac rel=rel and beta="(''no'' @ nat_to_string (Suc n))" in Swapout_R_1)
    using rel_refl apply (simp,simp)

apply (rule_tac derivable.Comma_impL_disp2)
apply (rule_tac derivable.W_impL_L)
apply (rule_tac derivable.FboxK_L)
apply (rule_tac derivable.Atom)
apply simp

apply (rule_tac f="dirty2 (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n)" in derivable.SingleCut)
        using cut apply simp
defer
using ih goal1 apply blast
apply (rule_tac derivable.And_L)
apply (rule_tac derivable.And_R)
unfolding k_apply.simps
thm E_impl4
value "dirty2 3 [1,2]"
value "dirty2 3 [1]"*)


(* ------------------ start of claim 1 ------------------ *)

    have claim10: "loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc (Suc k) vision (Suc n)) \<^sub>S \<turnstile>\<^sub>S 
    (dirty2 (Suc n) J \<and>\<^sub>F ( vision (Suc n) \<and>\<^sub>F fboxK\<^sub>F (nat_to_string j) ( E (Suc n) \<^sup>Suc k vision (Suc n))))\<^sub>S"
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.And_R)
    defer
    apply(rule Id)
    apply (rule_tac derivable.C_L)
    apply (rule_tac derivable.And_R)
    apply(subst k_apply.simps)
    apply (rule E_impl3)
    using Suc j'_def apply auto[1]
    apply(rule E_impl4)
    using assms by simp
  

  
    have claim11:  "loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F ( vision (Suc n) \<and>\<^sub>F fboxK\<^sub>F (nat_to_string j) ( E (Suc n) \<^sup>Suc k vision (Suc n))))\<^sub>S \<turnstile>\<^sub>S 
    ( (fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' )) \<and>\<^sub>F (fboxK\<^sub>F (nat_to_string j) ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"
  
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp)
    apply (rule_tac derivable.A_L)
    apply (rule_tac derivable.And_R)
    apply (rule_tac Id)
    
    apply(rule_tac dirty2_vision_der)
    using Suc(2,3,5) J'_def cut by auto
  
    have claim12: "loc \<turnstile>d ( (fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' )) \<and>\<^sub>F (fboxK\<^sub>F (nat_to_string j) ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( fboxK\<^sub>F (nat_to_string j) (( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' ) \<and>\<^sub>F ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"
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
  
    have claim13: "loc \<turnstile>d ( fboxK\<^sub>F (nat_to_string j) (( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' ) \<and>\<^sub>F ( E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( fboxK\<^sub>F (nat_to_string j) (( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' ) \<and>\<^sub>F ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"
  
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
    
    have claim14: "loc \<turnstile>d ( fboxK\<^sub>F (nat_to_string j) (( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' ) \<and>\<^sub>F ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( dirty2 (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S"
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
    

    
    have claim15: "loc \<turnstile>d ( fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( dirty2 (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) )) )\<^sub>S"
    apply (rule_tac derivable.FboxK_R)
    apply (rule_tac derivable.FboxK_L)
    apply (rule_tac derivable.ImpR_R)
    apply (rule_tac derivable.ImpR_L)
    defer
    apply (rule Id)
    using ih Id j'_def by simp
    
    
    have claim16: "loc \<turnstile>d ( fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( fboxK\<^sub>F (nat_to_string j) ( (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) )) )\<^sub>S"
    apply (rule_tac derivable.FboxK_R)
    apply (rule_tac derivable.FboxK_L)
    apply (rule_tac derivable.ImpR_R)
    apply (rule_tac derivable.ImpR_L)
    apply (rule_tac Id)
    
    apply (rule_tac derivable.And_L)
    apply (rule_tac derivable.Comma_impR_disp2)
    apply (rule_tac derivable.W_impR_R)
    by (rule_tac Id)


    have claim1: "loc \<turnstile>d (dirty2 (Suc n) J \<and>\<^sub>F E (Suc n) \<^sup>Suc (Suc k) vision (Suc n)) \<^sub>S \<turnstile>\<^sub>S 
     ( fboxK\<^sub>F (nat_to_string j) ( (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
         nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) )) )\<^sub>S"
    apply (rule_tac f="dirty2 (Suc n) J \<and>\<^sub>F (vision (Suc n) \<and>\<^sub>F fboxK\<^sub>F nat_to_string j E (Suc n) \<^sup>Suc k vision (Suc n))" in derivable.SingleCut)
    using cut apply simp
    using claim10 apply simp
    
    apply (rule_tac f="fboxK\<^sub>F nat_to_string j ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F dirty2 (Suc n) J' \<and>\<^sub>F
      fboxK\<^sub>F nat_to_string j E (Suc n) \<^sup>Suc k vision (Suc n)" in derivable.SingleCut)
    using cut apply simp
    using claim11 apply simp
    
    apply (rule_tac f="fboxK\<^sub>F (nat_to_string j) (( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' ) \<and>\<^sub>F ( E (Suc n) \<^sup>Suc k vision (Suc n) ))" in derivable.SingleCut)
    using cut apply simp
    using claim12 apply simp
    
    apply (rule_tac f=" fboxK\<^sub>F (nat_to_string j) (( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F dirty2 (Suc n) J' ) \<and>\<^sub>F ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) ))" in derivable.SingleCut)
    using cut apply simp
    using claim13 apply simp
    
    apply (rule_tac f="fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( dirty2 (Suc n) J' \<and>\<^sub>F E (Suc n) \<^sup>Suc k vision (Suc n) ))" in derivable.SingleCut)
    using cut apply simp
    using claim14 apply simp
    
    apply (rule_tac f="fboxK\<^sub>F (nat_to_string j) ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
         nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ))" in derivable.SingleCut)
    using cut apply simp
    using claim15 apply simp
    
    apply (rule_tac f="fboxK\<^sub>F (nat_to_string j) ( (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
         nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ))" in derivable.SingleCut)
    using cut apply simp
    using claim16 apply simp
    
    by (rule_tac Id)

(* ------------------- end of claim 1 ------------------- *)

(* ------------------ start of claim 2 ------------------ *)


(* In lem363_ we prove the different steps of Lemma 36.3 -- see p23 of the paper Ma Pal Sad*) 
    
    have lem363a: "loc \<turnstile>d ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ))) \<and>\<^sub>F 
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k (no (Suc n) )) )\<^sub>S
     \<turnstile>\<^sub>S ( ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ) ) )\<and>\<^sub>F (
     ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k(no (Suc n) )) ) )
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
     ( ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ) ) )\<and>\<^sub>F (
     ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k (no (Suc n) )) ) )
     )\<^sub>S
     \<turnstile>\<^sub>S 
     ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ) \<and>\<^sub>F 
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k(no (Suc n) )) )
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
  

(****************************************************************** NEW ******************************************************************)
    have lem363c: "loc \<turnstile>d
     ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ) \<and>\<^sub>F 
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k(no (Suc n))) )
    ) )\<^sub>S
     \<turnstile>\<^sub>S 
     ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ) \<and>\<^sub>F 
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )
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
    apply (rule_tac f = "( (fdiamK\<^sub>F (nat_to_string j') ( (nat_to_string j' \<^sub>F) )) \<and>\<^sub>F (fdiamK\<^sub>F (nat_to_string j') ( (nat_to_string j' \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F )) )" in derivable.SingleCut)
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
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ) \<and>\<^sub>F 
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )
    ) )\<^sub>S \<turnstile>\<^sub>S ( (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) 
     \<and>\<^sub>F ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )) )\<^sub>S" 
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
     ( ( ( ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k ( fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) )) \<and>\<^sub>F 
     ( ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k (fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F))) )
    ) )\<^sub>S \<turnstile>\<^sub>S ( ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k ( ( fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) 
     \<and>\<^sub>F ( fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )) )\<^sub>S" 
    
    apply (subst k_apply_BoxDiam)
    using cut apply simp
    apply simp
    done
    
    have lem363f: "loc \<turnstile>d
     ( ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k ( ( fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) 
     \<and>\<^sub>F ( fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k ( \<bottom>\<^sub>F )) \<^sub>S" 
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
    
    (*have LEM363: *)have lem363: "loc \<turnstile>d ( ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ))) \<and>\<^sub>F 
     (fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k (no (Suc n) )) )\<^sub>S
     \<turnstile>\<^sub>S ( ((nat_to_string j \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F
     )\<^sub>S" 
    apply(rule_tac f=" (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
          fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' nat_to_string j' \<^sub>F) \<and>\<^sub>F
         (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
          fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k no (Suc n))" in derivable.SingleCut)
    using cut apply simp
    using lem363a apply simp
    
    
    apply (rule_tac f="((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
     ( (fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F (nat_to_string j') (nat_to_string j' )\<^sub>F ) \<and>\<^sub>F
    ( fdiamA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k no (Suc n)))" in derivable.SingleCut)
    using cut apply simp
    using lem363b apply simp
    
    apply (rule_tac f=" ((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F
     ( (fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F (nat_to_string j') (nat_to_string j') \<^sub>F ) \<and>\<^sub>F
     ( fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k fdiamK\<^sub>F (nat_to_string j') ( (nat_to_string j' \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) )) " in derivable.SingleCut)
    using cut apply simp
    using lem363c apply simp
    
    apply (rule_tac derivable.ImpR_R)
    apply (rule_tac derivable.ImpR_L)
    defer
    apply (rule Id)
    
    thm lem363c
    thm lem363d
    
    apply (rule_tac f="(fdiamA\<^sub>F (''father'' @
     nat_to_string (Suc n)) ( ( Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) 
     \<and>\<^sub>F ( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) ))" in derivable.SingleCut)
    using cut apply simp

    using lem363d apply simp
    
    apply (rule_tac derivable.FdiamA_L)
    apply (rule_tac derivable.Forw_back_A2)
    
        
    apply (rule_tac f="( Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k ( ( fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) 
     \<and>\<^sub>F ( fdiamK\<^sub>F nat_to_string j' ((nat_to_string j' \<^sub>F)\<rightarrow>\<^sub>F \<bottom>\<^sub>F)) ))" in derivable.SingleCut)
    using cut apply simp
    using lem363e apply simp
        
    apply (rule_tac f=" Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k \<bottom>\<^sub>F " in derivable.SingleCut)
    using cut apply simp
    using lem363f apply simp
    
    
    apply (rule_tac derivable.Forw_back_A)
    apply (rule_tac derivable.Bot_R)
    apply (rule_tac derivable.Forw_back_A2)
    apply (rule_tac derivable.A_nec_R)
    by (rule_tac k_apply_DiamBot)
   

(****************************************************************** NEW ******************************************************************)


(* ----------------------------------- On going proof of claim 2 -- Work in progress -----------------------------------*)

  
    have claim2: "loc \<turnstile>d ( fboxK\<^sub>F (nat_to_string j) ( (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S 
    ( fboxK\<^sub>F (nat_to_string j) (( father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k (nat_to_string j \<^sub>F)) )) )\<^sub>S"
    apply (rule_tac derivable.FboxK_R)
    apply (rule_tac derivable.FboxK_L)
    apply (rule_tac derivable.ImpR_R)
    apply (rule_tac f = "(father (Suc n)) \<rightarrow>\<^sub>F ((((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
     nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ))" in derivable.SingleCut)
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
    (* to prove by induction that X |- [no^k] Y gives X |- {no}^k Y and X |- {no}^k Y is equivalent to {backward no}^k X |- Y *)
    apply(subst k_apply_S_display_1)
    using cut apply simp
    apply(subst k_apply_S_display_2)
    
    apply (rule_tac derivable.FboxA_R)
    apply (rule_tac f=" ( One\<^sub>F ((''no'' @ nat_to_string (Suc n)))) \<rightarrow>\<^sub>F ( nat_to_string j \<^sub>F) " in derivable.SingleCut)
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
    
    
    apply (rule_tac f= "(((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' nat_to_string j' \<^sub>F) \<and>\<^sub>F
      fdiamA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FdiamA (''no'' @ nat_to_string (Suc n)) \<^sup>k no (Suc n)" in derivable.SingleCut)
    using cut apply blast
    apply (rule_tac derivable.And_R)
    apply (rule_tac derivable.FdiamA_R)

    apply (rule_tac k_apply_S_F_forw_diam)
    apply (rule_tac f="no (Suc n)" in derivable.Pre_L)
    using preNo unfolding preFormula_no_def apply blast
    apply(rule Id)+
    
    apply(rule_tac f = "((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F" in derivable.SingleCut)
    using cut apply blast
    using lem363 apply simp
    apply (rule_tac f="( nat_to_string j \<^sub>F) " in derivable.SingleCut)
    using cut apply blast
    defer
    apply (rule k_apply_S_Atom)
    using cut apply blast
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

    have claim3: "loc \<turnstile>d ( fboxK\<^sub>F (nat_to_string j) (( father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
      nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k (nat_to_string j \<^sub>F)) )) )\<^sub>S \<turnstile>\<^sub>S 
      ( (fboxA\<^sub>F (''father'' @  nat_to_string (Suc n))  fboxK\<^sub>F (nat_to_string j) (  Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k (nat_to_string j \<^sub>F)) ) )\<^sub>S"
    apply (rule_tac derivable.FboxA_R)
    apply (rule_tac derivable.Back_forw_A2)
    apply (rule_tac derivable.FboxK_R)
    apply (rule_tac derivable.Back_forw_A)
    apply (rule_tac derivable.I_impR2)
    apply (rule_tac derivable.Bigcomma_Nil_L)
    apply (rule_tac derivable.Comma_impR_disp)
    apply (rule_tac derivable.Bigcomma_Cons_L)
    apply(rule_tac rel=rel and beta="''father'' @ nat_to_string (Suc n)" in Swapout_R_1)
    using rel_refl apply (simp,simp)
    
    
    apply (rule_tac derivable.FboxK_L)
    apply (rule_tac derivable.Reduce_R)
    apply (rule_tac derivable.ImpR_L)
    
    apply (rule_tac derivable.FboxA_L)
    apply (rule_tac Id)
    apply (rule_tac f="One\<^sub>F (''father'' @ nat_to_string (Suc n))" in derivable.SingleCut)
    using cut apply simp
    apply (rule_tac derivable.One_R)
    
    apply (rule_tac f="father (Suc n)" in derivable.Pre_L)
    using preFather unfolding preFormula_father_def apply blast
    by (rule_tac Id)

(* ------------------- end of claim 3 ------------------- *)

(* ------------------ start of claim 4 ------------------ *)

    have claim4: "loc \<turnstile>d 
      ( (fboxA\<^sub>F (''father'' @ nat_to_string (Suc n))  fboxK\<^sub>F (nat_to_string j) (  Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k (nat_to_string j \<^sub>F)) ) )\<^sub>S \<turnstile>\<^sub>S 
      (fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k fboxK\<^sub>F nat_to_string j nat_to_string j \<^sub>F) \<^sub>S"
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
        apply (rule_tac f="fboxK\<^sub>F (nat_to_string j) ( (((nat_to_string j \<^sub>F) \<rightarrow>\<^sub>F \<bottom>\<^sub>F ) \<and>\<^sub>F father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
          nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>k fboxK\<^sub>F nat_to_string j' (nat_to_string j' \<^sub>F)) ))" in derivable.SingleCut)
        using cut apply simp
        using claim1 Suc apply blast
      
        apply (rule_tac f="fboxK\<^sub>F (nat_to_string j) (( father (Suc n) ) \<rightarrow>\<^sub>F ( (fboxA\<^sub>F (''father'' @
          nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k (nat_to_string j \<^sub>F)) ))" in derivable.SingleCut)
        using cut apply simp
        using claim2 Suc apply blast

        apply (rule_tac f="(fboxA\<^sub>F (''father'' @
          nat_to_string (Suc n))  fboxK\<^sub>F (nat_to_string j) (  Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k (nat_to_string j \<^sub>F)) )" in derivable.SingleCut)
        using cut apply simp
        using claim3 apply simp
      
        apply (rule_tac f="fboxA\<^sub>F (''father'' @ nat_to_string (Suc n)) Formula_FboxA (''no'' @ nat_to_string (Suc n)) \<^sup>Suc k fboxK\<^sub>F nat_to_string j nat_to_string j \<^sub>F" in derivable.SingleCut)
        using cut apply simp
        using claim4 apply simp
        using Id by blast 
qed
end