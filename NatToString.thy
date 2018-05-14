theory NatToString
imports Main 
begin


definition digit_char_list :: "string" where
"digit_char_list = ''0123456789''"


lemma digit_char_list_length[simp]:
  shows "length digit_char_list = (10::nat)"
by (metis One_nat_def Suc_eq_plus1 digit_char_list_def eval_nat_numeral(2) eval_nat_numeral(3) list.size(3) list.size(4) nat_1_add_1 semiring_norm(26) semiring_norm(27) semiring_norm(28))


lemma digit_char_list_distinct:
  shows "distinct digit_char_list"
unfolding digit_char_list_def using distinct.simps(2)
by simp


fun nat_to_string :: "nat \<Rightarrow> string" ("`_`")
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
proof goal_cases
case 1
  then have assms2: "i \<le> 9" "j \<le> 9" using digit_char_list_length assms(2,3,4) digit_char_list_distinct unfolding list_def digit_char_list_def by simp+

  have set_expand: "{0..9::nat} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}" by auto

  have "\<forall>ii \<in> {0,1,2,3,4,5,6,7,8,9}::nat set. \<forall>jj \<in> {0,1,2,3,4,5,6,7,8,9}::nat set. ii\<noteq>jj \<longrightarrow> 
    set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! ii) ''0123456789'') \<noteq> 
    set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! jj) ''0123456789'')"
  unfolding digit_char_list_def
  apply simp
  apply (rule conjI, rule nEq_exE, simp)+
  by (rule nEq_exE, simp)

  then have "\<forall>ii \<in> {0..9::nat}. \<forall>jj \<in> {0..9::nat}. ii\<noteq>jj \<longrightarrow> 
    set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! ii) ''0123456789'') \<noteq> 
    set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! jj) ''0123456789'')"
  apply(subst set_expand)+ by blast
  then have res: "\<And>ii jj. ii \<in> {0..9::nat} \<Longrightarrow> jj \<in> {0..9::nat} \<Longrightarrow> ii\<noteq>jj \<Longrightarrow> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! ii) ''0123456789'') \<noteq> set (filter (\<lambda>x. x \<noteq> ''0123456789'' ! jj) ''0123456789'')"
  by simp
 
  with assms have "i \<in> {0..9::nat}" "i \<notin> -{0..9::nat}" "j \<in> {0..9::nat}" "j \<notin> -{0..9::nat}" by auto
  show ?case
  apply(cases "i \<in> {0..9::nat}")
  apply(cases "j \<in> {0..9::nat}")
  using res assms(2) set_expand apply simp
  using assms by simp+
qed

lemma digit_char_list_inject2:
  fixes i j :: nat
  assumes "digit_char_list ! (i mod 10) = digit_char_list ! (j mod 10)"
  shows "(i mod 10) = (j mod 10)"
proof -
  have "i mod 10 < 10" "j mod 10 < 10" by simp+
  thus ?thesis using digit_char_list_inject assms  by fastforce
qed


lemma nat_to_string_inject2:
  fixes i j :: nat
  assumes "nat_to_string i = nat_to_string j"
  shows "i = j"
  using assms 
  apply (induct i arbitrary: j rule: nat_to_string.induct)
  apply (rename_tac i j)
  apply (case_tac "i < length digit_char_list"; case_tac "j < length digit_char_list") 
proof goal_cases
  case (1 i j)
  then show ?case using digit_char_list_inject by force
next
  case (2 i j)
  then show ?case 
    apply simp
    using digit_char_list_inject by (metis (no_types) append_is_Nil_conv list.distinct(1))
next
  case (3 i j)
  then show ?case 
    apply simp
    using digit_char_list_inject by (metis append_is_Nil_conv list.distinct(1))
next
  case (4 i j)
  then show ?case 
    apply(cases "j div 10 < 10")
    apply simp
    proof goal_cases
    case 1 
      from 1(2) have "(i div 10) = (j div 10)" "(i mod 10) = (j mod 10)" 
      apply (simp add: 1) using digit_char_list_inject2 1(2,5) by blast
      thus ?case by (metis mult_div_mod_eq)
    next
    case 2 
      then have 0: "nat_to_string (i div 10 div length digit_char_list) @ [digit_char_list ! (i div 10 mod length digit_char_list)] =
      nat_to_string (j div 10 div length digit_char_list) @ [digit_char_list ! (j div 10 mod length digit_char_list)]"
        by (metis append1_eq_conv digit_char_list_length nat_to_string.simps)
      with 2 have 1: "nat_to_string (i div 10 div length digit_char_list) = nat_to_string (j div 10 div length digit_char_list)" by blast
   
      with 0 have "digit_char_list ! (i div 10 mod length digit_char_list) = digit_char_list ! (j div 10 mod length digit_char_list)" by simp
      with 0 1 2 have "i div 10 = j div 10" "i mod 10 = j mod 10" using digit_char_list_inject2 using 2 
        apply (metis append1_eq_conv digit_char_list_length nat_to_string.simps)
        using "4"(2,3,4) digit_char_list_inject2 by auto
      thus ?case by (metis mult_div_mod_eq)
    qed
qed


end