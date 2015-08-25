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

end