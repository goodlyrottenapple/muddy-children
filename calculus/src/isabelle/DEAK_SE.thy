theory (*calc_name_se-BEGIN*)DEAK_SE(*calc_name_se-END*)
imports Main (*calc_name_core_se-BEGIN*)DEAK_Core_SE(*calc_name_core_se-END*)
begin

datatype Locale = (*(*uncommentL?Formula?RuleCut-BEGIN*)*)(*uncommentL?Formula?RuleCut-END*)
                  CutFormula Formula |
                  (*uncommentR?Formula?RuleCut-BEGIN*)(*(*uncommentR?Formula?RuleCut-END*)*)
                  (*(*uncommentL?Sequent-BEGIN*)*)(*uncommentL?Sequent-END*)
                  Premise Sequent |
                  (*uncommentR?Sequent-BEGIN*)(*(*uncommentR?Sequent-END*)*)
                  (*(*uncommentL?Structure-BEGIN*)*)(*uncommentL?Structure-END*)
                  Part Structure |
                  (*uncommentR?Structure-BEGIN*)(*(*uncommentR?Structure-END*)*)
                  (*(*uncommentL?Action?Agent-BEGIN*)*)(*uncommentL?Action?Agent-END*)
                  RelAKA "Action \<Rightarrow> Agent \<Rightarrow> Action list" | 
                  (*uncommentR?Action?Agent-BEGIN*)(*(*uncommentR?Action?Agent-END*)*)
                  (*(*uncommentL?Action?Formula-BEGIN*)*)(*uncommentL?Action?Formula-END*)
                  PreFormula Action Formula |
                  (*uncommentR?Action?Formula-BEGIN*)(*(*uncommentR?Action?Formula-END*)*)
                  (*(*uncommentL?Agent-BEGIN*)*)(*uncommentL?Agent-END*)
                  LAgent Agent |
                  (*uncommentR?Agent-BEGIN*)(*(*uncommentR?Agent-END*)*)
                  Empty


(*(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-BEGIN*)*)(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-END*)
fun is_act_mod :: "Structure \<Rightarrow> Atprop option" where
"is_act_mod (Structure_Formula (Formula_Atprop p)) = Some p"|
"is_act_mod (Structure_ForwA _ s) = is_act_mod s"|
"is_act_mod (Structure_BackA _ s) = is_act_mod s"|

"is_act_mod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>S r) = ( (is_act_mod l) \<noteq> None \<and> (is_act_mod l) = (is_act_mod r) )"
(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-BEGIN*)(*(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-END*)*)


fun pairs :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
"pairs [] [] = []" |
"pairs [] Y = []" |
"pairs X [] = []" |
"pairs (X#Xs) (Y#Ys) = (X, Y)#(pairs Xs Ys)"

(*calc_structure_rules_se-BEGIN*)
inductive derivable :: "Locale list \<Rightarrow> Sequent \<Rightarrow> bool"  (infix "\<turnstile>d" 300) where
Bigcomma_Nil_R2: "l \<turnstile>d (Y \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S (;;\<^sub>S []))"|
Bigcomma_Nil_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S (;;\<^sub>S [])) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S I\<^sub>S)"|
Bigcomma_Nil_L2: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((;;\<^sub>S []) \<turnstile>\<^sub>S Y)"|
Bigcomma_Nil_L: "l \<turnstile>d ((;;\<^sub>S []) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S Y)"|
Bigcomma_Cons_R2: "l \<turnstile>d (Y \<turnstile>\<^sub>S X ;\<^sub>S (;;\<^sub>S Xs)) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S ;;\<^sub>S(X # Xs))"|
Bigcomma_Cons_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S ;;\<^sub>S(X # Xs)) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S X ;\<^sub>S (;;\<^sub>S Xs))"|
Bigcomma_Cons_L2: "l \<turnstile>d (X ;\<^sub>S (;;\<^sub>S Xs) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (;;\<^sub>S(X # Xs) \<turnstile>\<^sub>S Y)"|
Bigcomma_Cons_L: "l \<turnstile>d (;;\<^sub>S(X # Xs) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X ;\<^sub>S (;;\<^sub>S Xs) \<turnstile>\<^sub>S Y)"
| 
SingleCut: "(CutFormula f) \<in> set l \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S f \<^sub>S) \<Longrightarrow> l \<turnstile>d (f \<^sub>S \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"
| 
Comma_impL_disp: "l \<turnstile>d ((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (Z \<leftarrow>\<^sub>S Y))"|
Comma_impR_disp2: "l \<turnstile>d (Y \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Z)) \<Longrightarrow> l \<turnstile>d ((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z)"|
ImpL_comma_disp2: "l \<turnstile>d ((Z \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (X ;\<^sub>S Y))"|
ImpR_comma_disp2: "l \<turnstile>d ((X \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (X ;\<^sub>S Y))"|
ImpR_comma_disp: "l \<turnstile>d (Z \<turnstile>\<^sub>S (X ;\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d ((X \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>S Y)"|
ImpL_comma_disp: "l \<turnstile>d (Z \<turnstile>\<^sub>S (X ;\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d ((Z \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S X)"|
Comma_impR_disp: "l \<turnstile>d ((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Z))"|
Comma_impL_disp2: "l \<turnstile>d (X \<turnstile>\<^sub>S (Z \<leftarrow>\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d ((X ;\<^sub>S Y) \<turnstile>\<^sub>S Z)"
| 
Back_forw_A: "l \<turnstile>d (X \<turnstile>\<^sub>S (forwA\<^sub>S a Y)) \<Longrightarrow> l \<turnstile>d ((backA\<^sub>S a X) \<turnstile>\<^sub>S Y)"|
Forw_back_A2: "l \<turnstile>d (X \<turnstile>\<^sub>S (backA\<^sub>S a Y)) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S a X) \<turnstile>\<^sub>S Y)"|
Forw_back_A: "l \<turnstile>d ((forwA\<^sub>S a X) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (backA\<^sub>S a Y))"|
Back_forw_A2: "l \<turnstile>d ((backA\<^sub>S a X) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwA\<^sub>S a Y))"
| 
Back_forw_K2: "l \<turnstile>d ((backK\<^sub>S a X) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwK\<^sub>S a Y))"|
Back_forw_K: "l \<turnstile>d (X \<turnstile>\<^sub>S (forwK\<^sub>S a Y)) \<Longrightarrow> l \<turnstile>d ((backK\<^sub>S a X) \<turnstile>\<^sub>S Y)"|
Forw_back_K2: "l \<turnstile>d (X \<turnstile>\<^sub>S (backK\<^sub>S a Y)) \<Longrightarrow> l \<turnstile>d ((forwK\<^sub>S a X) \<turnstile>\<^sub>S Y)"|
Forw_back_K: "l \<turnstile>d ((forwK\<^sub>S a X) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (backK\<^sub>S a Y))"
| 
Grishin_R2: "l \<turnstile>d (W \<turnstile>\<^sub>S ((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z)) \<Longrightarrow> l \<turnstile>d (W \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)))"|
Grishin_R: "l \<turnstile>d (W \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z))) \<Longrightarrow> l \<turnstile>d (W \<turnstile>\<^sub>S ((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z))"|
Grishin_L: "l \<turnstile>d ((X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d (((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W)"|
Grishin_L2: "l \<turnstile>d (((X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d ((X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W)"
| 
Refl_ForwK: "(LAgent a) \<in> set l \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwK\<^sub>S a Y)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"
| 
Bot_R: "l \<turnstile>d (X \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (\<bottom>\<^sub>F \<^sub>S))"|
Top_L: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((\<top>\<^sub>F \<^sub>S) \<turnstile>\<^sub>S X)"|
DImpR_L: "l \<turnstile>d (((A \<^sub>S) \<rightarrow>\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (((A >-\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S Z)"|
ImpL_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((B \<^sub>S) \<leftarrow>\<^sub>S (A \<^sub>S))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S ((B \<leftarrow>\<^sub>F A) \<^sub>S))"|
DImpL_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S (B \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((Y \<leftarrow>\<^sub>S X) \<turnstile>\<^sub>S ((B -<\<^sub>F A) \<^sub>S))"|
And_L: "l \<turnstile>d (((A \<^sub>S) ;\<^sub>S (B \<^sub>S)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (((A \<and>\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S Z)"|
ImpR_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((A \<^sub>S) \<rightarrow>\<^sub>S (B \<^sub>S))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S ((A \<rightarrow>\<^sub>F B) \<^sub>S))"|
Or_L: "l \<turnstile>d ((B \<^sub>S) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((A \<or>\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S (X ;\<^sub>S Y))"|
Or_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((A \<^sub>S) ;\<^sub>S (B \<^sub>S))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S ((A \<or>\<^sub>F B) \<^sub>S))"|
ImpR_L: "l \<turnstile>d ((B \<^sub>S) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d (((A \<rightarrow>\<^sub>F B) \<^sub>S) \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Y))"|
DImpL_L: "l \<turnstile>d (((B \<^sub>S) \<leftarrow>\<^sub>S (A \<^sub>S)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (((B -<\<^sub>F A) \<^sub>S) \<turnstile>\<^sub>S Z)"|
And_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S (B \<^sub>S)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((X ;\<^sub>S Y) \<turnstile>\<^sub>S ((A \<and>\<^sub>F B) \<^sub>S))"|
DImpR_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S (B \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((X \<rightarrow>\<^sub>S Y) \<turnstile>\<^sub>S ((A >-\<^sub>F B) \<^sub>S))"|
ImpL_L: "l \<turnstile>d ((B \<^sub>S) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d (((B \<leftarrow>\<^sub>F A) \<^sub>S) \<turnstile>\<^sub>S (Y \<leftarrow>\<^sub>S X))"|
Top_R: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S (\<top>\<^sub>F \<^sub>S))"|
Bot_L: "l \<turnstile>d ((\<bottom>\<^sub>F \<^sub>S) \<turnstile>\<^sub>S I\<^sub>S)"
| 
FdiamA_L: "l \<turnstile>d ((forwA\<^sub>S alpha (A \<^sub>S)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((fdiamA\<^sub>F alpha A) \<^sub>S) \<turnstile>\<^sub>S X)"|
One_R: "l \<turnstile>d ((Phi\<^sub>S alpha) \<turnstile>\<^sub>S ((One\<^sub>F alpha) \<^sub>S))"|
BdiamA_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((backA\<^sub>S alpha X) \<turnstile>\<^sub>S ((bdiamA\<^sub>F alpha A) \<^sub>S))"|
FboxA_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (forwA\<^sub>S alpha (A \<^sub>S))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((fboxA\<^sub>F alpha A) \<^sub>S))"|
Pre_L: "(PreFormula alpha f) \<in> set l \<Longrightarrow> l \<turnstile>d (f \<^sub>S \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((One\<^sub>F alpha)\<^sub>S \<turnstile>\<^sub>S X)"|
BboxA_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (backA\<^sub>S alpha (A \<^sub>S))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((bboxA\<^sub>F alpha A) \<^sub>S))"|
BboxA_L: "l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((bboxA\<^sub>F alpha A) \<^sub>S) \<turnstile>\<^sub>S (backA\<^sub>S alpha X))"|
FboxA_L: "l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((fboxA\<^sub>F alpha A) \<^sub>S) \<turnstile>\<^sub>S (forwA\<^sub>S alpha X))"|
Pre_R: "(PreFormula alpha f) \<in> set l \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S f \<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (One\<^sub>F alpha)\<^sub>S)"|
BdiamA_L: "l \<turnstile>d ((backA\<^sub>S alpha (A \<^sub>S)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((bdiamA\<^sub>F alpha A) \<^sub>S) \<turnstile>\<^sub>S X)"|
One_L: "l \<turnstile>d ((Phi\<^sub>S alpha) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((One\<^sub>F alpha) \<^sub>S) \<turnstile>\<^sub>S X)"|
FdiamA_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S alpha X) \<turnstile>\<^sub>S ((fdiamA\<^sub>F alpha A) \<^sub>S))"
| 
BdiamK_L: "l \<turnstile>d ((backK\<^sub>S a (A \<^sub>S)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((bdiamK\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S X)"|
FdiamK_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((forwK\<^sub>S a X) \<turnstile>\<^sub>S ((fdiamK\<^sub>F a A) \<^sub>S))"|
FboxK_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (forwK\<^sub>S a (A \<^sub>S))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((fboxK\<^sub>F a A) \<^sub>S))"|
BboxK_L: "l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((bboxK\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S (backK\<^sub>S a X))"|
BboxK_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (backK\<^sub>S a (A \<^sub>S))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S ((bboxK\<^sub>F a A) \<^sub>S))"|
FboxK_L: "l \<turnstile>d ((A \<^sub>S) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((fboxK\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S (forwK\<^sub>S a X))"|
FdiamK_L: "l \<turnstile>d ((forwK\<^sub>S a (A \<^sub>S)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d (((fdiamK\<^sub>F a A) \<^sub>S) \<turnstile>\<^sub>S X)"|
BdiamK_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (A \<^sub>S)) \<Longrightarrow> l \<turnstile>d ((backK\<^sub>S a X) \<turnstile>\<^sub>S ((bdiamK\<^sub>F a A) \<^sub>S))"
| 
W_impL_R: "l \<turnstile>d (X \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((X \<leftarrow>\<^sub>S Z) \<turnstile>\<^sub>S Y)"|
ImpL_I: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((X \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S I\<^sub>S)"|
W_impL_L: "l \<turnstile>d (X \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S (Z \<leftarrow>\<^sub>S X))"|
ImpR_I2: "l \<turnstile>d ((Y \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
E_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (Y1 ;\<^sub>S Y2)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (Y2 ;\<^sub>S Y1))"|
IW_R: "l \<turnstile>d (X \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
IW_L: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
A_L2: "l \<turnstile>d ((X ;\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d (((X ;\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W)"|
E_L: "l \<turnstile>d ((X1 ;\<^sub>S X2) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((X2 ;\<^sub>S X1) \<turnstile>\<^sub>S Y)"|
A_R: "l \<turnstile>d (W \<turnstile>\<^sub>S ((X ;\<^sub>S Y) ;\<^sub>S Z)) \<Longrightarrow> l \<turnstile>d (W \<turnstile>\<^sub>S (X ;\<^sub>S (Y ;\<^sub>S Z)))"|
W_impR_R: "l \<turnstile>d (X \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Z))"|
C_L: "l \<turnstile>d ((X ;\<^sub>S X) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
C_R: "l \<turnstile>d (X \<turnstile>\<^sub>S (Y ;\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
ImpR_I: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((Y \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>S I\<^sub>S)"|
W_impR_L: "l \<turnstile>d (X \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((Z \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>S Y)"|
A_L: "l \<turnstile>d (((X ;\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>S W) \<Longrightarrow> l \<turnstile>d ((X ;\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>S W)"|
A_R2: "l \<turnstile>d (W \<turnstile>\<^sub>S (X ;\<^sub>S (Y ;\<^sub>S Z))) \<Longrightarrow> l \<turnstile>d (W \<turnstile>\<^sub>S ((X ;\<^sub>S Y) ;\<^sub>S Z))"|
I_impR2: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Y)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
I_impL: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S (Y \<leftarrow>\<^sub>S X))"|
I_impR: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S (X \<rightarrow>\<^sub>S Y))"|
ImpL_I2: "l \<turnstile>d ((X \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"|
I_impL2: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S (Y \<leftarrow>\<^sub>S X)) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S Y)"
| 
A_nec_L: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((backA\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X)"|
A_mon_L: "l \<turnstile>d (((backA\<^sub>S a X) ;\<^sub>S (backA\<^sub>S a Y)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((backA\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z)"|
Mon_A_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((forwA\<^sub>S a X) ;\<^sub>S (forwA\<^sub>S a Y))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (forwA\<^sub>S a (X ;\<^sub>S Y)))"|
Nec_A_L: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X)"|
FS_A_L: "l \<turnstile>d (((forwA\<^sub>S a Y) \<rightarrow>\<^sub>S (forwA\<^sub>S a Z)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X)"|
FS_A_R: "l \<turnstile>d (X \<turnstile>\<^sub>S ((forwA\<^sub>S a Y) \<rightarrow>\<^sub>S (forwA\<^sub>S a Z))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwA\<^sub>S a (Y \<rightarrow>\<^sub>S Z)))"|
A_mon_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((backA\<^sub>S a X) ;\<^sub>S (backA\<^sub>S a Y))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (backA\<^sub>S a (X ;\<^sub>S Y)))"|
A_FS_R: "l \<turnstile>d (X \<turnstile>\<^sub>S ((backA\<^sub>S a Y) \<rightarrow>\<^sub>S (backA\<^sub>S a Z))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (backA\<^sub>S a (Y \<rightarrow>\<^sub>S Z)))"|
Nec_A_R: "l \<turnstile>d (X \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwA\<^sub>S a I\<^sub>S))"|
Mon_A_L: "l \<turnstile>d (((forwA\<^sub>S a X) ;\<^sub>S (forwA\<^sub>S a Y)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z)"|
A_FS_L: "l \<turnstile>d (((backA\<^sub>S a Y) \<rightarrow>\<^sub>S (backA\<^sub>S a Z)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((backA\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X)"|
A_nec_R: "l \<turnstile>d (X \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (backA\<^sub>S a I\<^sub>S))"
| 
Reduce_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S ((Phi\<^sub>S a) \<rightarrow>\<^sub>S (forwA\<^sub>S a X))) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S (forwA\<^sub>S a X))"|
CompA_R: "l \<turnstile>d (Y \<turnstile>\<^sub>S (forwA\<^sub>S a (backA\<^sub>S a X))) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S ((Phi\<^sub>S a) \<rightarrow>\<^sub>S X))"|
Balance: "l \<turnstile>d (X \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S a X) \<turnstile>\<^sub>S (forwA\<^sub>S a Y))"|
CompA_L: "l \<turnstile>d ((forwA\<^sub>S a (backA\<^sub>S a X)) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d (((Phi\<^sub>S a) ;\<^sub>S X) \<turnstile>\<^sub>S Y)"|
Reduce_L: "l \<turnstile>d (((Phi\<^sub>S a) ;\<^sub>S (forwA\<^sub>S a X)) \<turnstile>\<^sub>S Y) \<Longrightarrow> l \<turnstile>d ((forwA\<^sub>S a X) \<turnstile>\<^sub>S Y)"
| 
K_nec_R: "l \<turnstile>d (X \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (backK\<^sub>S a I\<^sub>S))"|
Nec_K_L: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((forwK\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X)"|
K_mon_L: "l \<turnstile>d (((backK\<^sub>S a X) ;\<^sub>S (backK\<^sub>S a Y)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((backK\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z)"|
Mon_K_L: "l \<turnstile>d (((forwK\<^sub>S a X) ;\<^sub>S (forwK\<^sub>S a Y)) \<turnstile>\<^sub>S Z) \<Longrightarrow> l \<turnstile>d ((forwK\<^sub>S a (X ;\<^sub>S Y)) \<turnstile>\<^sub>S Z)"|
FS_K_L: "l \<turnstile>d (((forwK\<^sub>S a Y) \<rightarrow>\<^sub>S (forwK\<^sub>S a Z)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((forwK\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X)"|
FS_K_R: "l \<turnstile>d (X \<turnstile>\<^sub>S ((forwK\<^sub>S a Y) \<rightarrow>\<^sub>S (forwK\<^sub>S a Z))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwK\<^sub>S a (Y \<rightarrow>\<^sub>S Z)))"|
Mon_K_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((forwK\<^sub>S a X) ;\<^sub>S (forwK\<^sub>S a Y))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (forwK\<^sub>S a (X ;\<^sub>S Y)))"|
K_mon_R: "l \<turnstile>d (Z \<turnstile>\<^sub>S ((backK\<^sub>S a X) ;\<^sub>S (backK\<^sub>S a Y))) \<Longrightarrow> l \<turnstile>d (Z \<turnstile>\<^sub>S (backK\<^sub>S a (X ;\<^sub>S Y)))"|
K_FS_L: "l \<turnstile>d (((backK\<^sub>S a Y) \<rightarrow>\<^sub>S (backK\<^sub>S a Z)) \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((backK\<^sub>S a (Y \<rightarrow>\<^sub>S Z)) \<turnstile>\<^sub>S X)"|
Nec_K_R: "l \<turnstile>d (X \<turnstile>\<^sub>S I\<^sub>S) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (forwK\<^sub>S a I\<^sub>S))"|
K_FS_R: "l \<turnstile>d (X \<turnstile>\<^sub>S ((backK\<^sub>S a Y) \<rightarrow>\<^sub>S (backK\<^sub>S a Z))) \<Longrightarrow> l \<turnstile>d (X \<turnstile>\<^sub>S (backK\<^sub>S a (Y \<rightarrow>\<^sub>S Z)))"|
K_nec_L: "l \<turnstile>d (I\<^sub>S \<turnstile>\<^sub>S X) \<Longrightarrow> l \<turnstile>d ((backK\<^sub>S a I\<^sub>S) \<turnstile>\<^sub>S X)"
| 
Swapin_L: "(RelAKA rel) \<in> set l \<Longrightarrow> l \<turnstile>d (forwA\<^sub>S alpha (forwK\<^sub>S a X) \<turnstile>\<^sub>S Y) \<Longrightarrow> beta \<in> set (rel alpha a) \<Longrightarrow> l \<turnstile>d ((Phi\<^sub>S alpha) ;\<^sub>S (forwK\<^sub>S a (forwA\<^sub>S beta X)) \<turnstile>\<^sub>S Y)"|
Swapin_R: "(RelAKA rel) \<in> set l \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S forwA\<^sub>S alpha (forwK\<^sub>S a X)) \<Longrightarrow> beta \<in> set (rel alpha a) \<Longrightarrow> l \<turnstile>d (Y \<turnstile>\<^sub>S (Phi\<^sub>S alpha) \<rightarrow>\<^sub>S (forwK\<^sub>S a (forwA\<^sub>S beta X)))"
| 
Swapout_L: "(RelAKA rel) \<in> set l \<Longrightarrow> (\<forall> Y \<in> (set Ys). \<exists>beta \<in> set (rel alpha a). (l \<turnstile>d forwK\<^sub>S a (forwA\<^sub>S beta X) \<turnstile>\<^sub>S Y) ) \<Longrightarrow> l \<turnstile>d forwA\<^sub>S alpha (forwK\<^sub>S a X) \<turnstile>\<^sub>S ;;\<^sub>S Ys"|
Swapout_R: "(RelAKA rel) \<in> set l \<Longrightarrow> (\<forall> Y \<in> (set Ys). \<exists>beta \<in> set (rel alpha a). (l \<turnstile>d Y \<turnstile>\<^sub>S forwK\<^sub>S a (forwA\<^sub>S beta X)) ) \<Longrightarrow> l \<turnstile>d  ;;\<^sub>S Ys \<turnstile>\<^sub>S forwA\<^sub>S alpha (forwK\<^sub>S a X)"
| 
Id: "l \<turnstile>d (((p \<^sub>F) \<^sub>S) \<turnstile>\<^sub>S ((p \<^sub>F) \<^sub>S))"|
Atom: "atom seq \<Longrightarrow> l \<turnstile>d seq"
(*calc_structure_rules_se-END*)

end