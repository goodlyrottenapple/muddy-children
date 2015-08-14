theory (*calc_name-BEGIN*)DEAK(*calc_name-END*)
imports Main (*calc_name_core-BEGIN*)DEAK_Core(*calc_name_core-END*) "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Code_Char" "~~/src/HOL/Code_Numeral" (*always keep Code_char import last! its added for code generator to output Haskell strings instead of the isabelle nibble stuff *)
begin

(*calc_structure_rules-BEGIN*)
datatype RuleBigcomma = Bigcomma_Cons_L
                      | Bigcomma_Cons_L2
                      | Bigcomma_Cons_R
                      | Bigcomma_Cons_R2
                      | Bigcomma_Nil_L
                      | Bigcomma_Nil_L2
                      | Bigcomma_Nil_R
                      | Bigcomma_Nil_R2

datatype RuleCut = SingleCut

datatype RuleDisp = Comma_impL_disp
                  | Comma_impL_disp2
                  | Comma_impR_disp
                  | Comma_impR_disp2
                  | ImpL_comma_disp
                  | ImpL_comma_disp2
                  | ImpR_comma_disp
                  | ImpR_comma_disp2

datatype RuleDispAct = Back_forw_A
                     | Back_forw_A2
                     | Forw_back_A
                     | Forw_back_A2

datatype RuleDispK = Back_forw_K
                   | Back_forw_K2
                   | Forw_back_K
                   | Forw_back_K2

datatype RuleGrish = Grishin_L
                   | Grishin_L2
                   | Grishin_R
                   | Grishin_R2

datatype RuleKnowledge = Refl_ForwK

datatype RuleOp = And_L
                | And_R
                | Bot_L
                | Bot_R
                | DImpL_L
                | DImpL_R
                | DImpR_L
                | DImpR_R
                | ImpL_L
                | ImpL_R
                | ImpR_L
                | ImpR_R
                | Or_L
                | Or_R
                | Top_L
                | Top_R

datatype RuleOpAct = BboxA_L
                   | BboxA_R
                   | BdiamA_L
                   | BdiamA_R
                   | FboxA_L
                   | FboxA_R
                   | FdiamA_L
                   | FdiamA_R
                   | One_L
                   | One_R
                   | Pre_L
                   | Pre_R

datatype RuleOpK = BboxK_L
                 | BboxK_R
                 | BdiamK_L
                 | BdiamK_R
                 | FboxK_L
                 | FboxK_R
                 | FdiamK_L
                 | FdiamK_R

datatype RuleStruct = A_L
                    | A_L2
                    | A_R
                    | A_R2
                    | C_L
                    | C_R
                    | E_L
                    | E_R
                    | IW_L
                    | IW_R
                    | I_impL
                    | I_impL2
                    | I_impR
                    | I_impR2
                    | ImpL_I
                    | ImpL_I2
                    | ImpR_I
                    | ImpR_I2
                    | W_impL_L
                    | W_impL_R
                    | W_impR_L
                    | W_impR_R

datatype RuleStructAct = A_FS_L
                       | A_FS_R
                       | A_mon_L
                       | A_mon_R
                       | A_nec_L
                       | A_nec_R
                       | FS_A_L
                       | FS_A_R
                       | Mon_A_L
                       | Mon_A_R
                       | Nec_A_L
                       | Nec_A_R

datatype RuleStructEA = Balance
                      | CompA_L
                      | CompA_R
                      | Reduce_L
                      | Reduce_R

datatype RuleStructK = FS_K_L
                     | FS_K_R
                     | K_FS_L
                     | K_FS_R
                     | K_mon_L
                     | K_mon_R
                     | K_nec_L
                     | K_nec_R
                     | Mon_K_L
                     | Mon_K_R
                     | Nec_K_L
                     | Nec_K_R

datatype RuleSwapin = Swapin_L
                    | Swapin_R

datatype RuleSwapout = Swapout_L
                     | Swapout_R

datatype RuleZer = Atom
                 | Id
                 | Partial
                 | Prem

datatype Rule = RuleBigcomma RuleBigcomma
              | RuleCut RuleCut
              | RuleDisp RuleDisp
              | RuleDispAct RuleDispAct
              | RuleDispK RuleDispK
              | RuleGrish RuleGrish
              | RuleKnowledge RuleKnowledge
              | RuleOp RuleOp
              | RuleOpAct RuleOpAct
              | RuleOpK RuleOpK
              | RuleStruct RuleStruct
              | RuleStructAct RuleStructAct
              | RuleStructEA RuleStructEA
              | RuleStructK RuleStructK
              | RuleSwapin RuleSwapin
              | RuleSwapout RuleSwapout
              | RuleZer RuleZer
              | RuleMacro string Prooftree
              | Fail
     and Prooftree = Prooftree Sequent Rule "Prooftree list" ("_ \<Longleftarrow> PT ( _ ) _" [341,341] 350)
(*calc_structure_rules-END*)

fun concl :: "Prooftree \<Rightarrow> Sequent" where
"concl (a \<Longleftarrow> PT ( b ) c) = a"

datatype ruleder = ruleder      Sequent "Sequent \<Rightarrow> Sequent list option" (infix "\<Longrightarrow>RD" 300) |
                   ruleder_cond "Sequent \<Rightarrow> bool" Sequent "Sequent \<Rightarrow> Sequent list option" ("_ \<Longrightarrow>C _ \<Longrightarrow>RD _" 300)


(*(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-BEGIN*)*)(*uncommentL?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-END*)
fun is_act_mod :: "Structure \<Rightarrow> Atprop option" where
"is_act_mod (Structure_Formula (Formula_Atprop p)) = Some p"|
"is_act_mod (Structure_Action_Structure _ _ s) = is_act_mod s"|
"is_act_mod _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>S r) = ( (is_act_mod l) \<noteq> None \<and> (is_act_mod l) = (is_act_mod r) )"|
"atom _ = False"
(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-BEGIN*)(*(*uncommentR?Atprop?Formula?Formula_Atprop?Formula_Action_Formula-END*)*)

(*(*uncommentL?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent-BEGIN*)*)(*uncommentL?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent-END*)
fun relAKACheck :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> ((Sequent \<times> Sequent) list) \<Rightarrow> bool" where
"relAKACheck fun mlist = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) mlist of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) mlist of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> 
                            (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''beta'') \<^sub>S) ) mlist of 
                                Some (_, Sequent_Structure (Formula_Action beta \<^sub>S)) \<Rightarrow> (case List.find ( \<lambda>(x::Action). x = beta ) (fun alpha a) of Some res \<Rightarrow> True | None \<Rightarrow> False)
                              |  _ \<Rightarrow> False )
                       | _ \<Rightarrow> False)
                 | _ \<Rightarrow> False)"

fun betaList :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> ((Sequent \<times> Sequent) list) \<Rightarrow> (Action list)" where
"betaList fun mlist = (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure (Formula_Action (?\<^sub>Act ''alpha'') \<^sub>S) ) mlist of 
                   Some (_, Sequent_Structure (Formula_Action alpha \<^sub>S)) \<Rightarrow> 
                      (case List.find ( \<lambda>(x::Sequent \<times> Sequent). fst x = Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar ''a''))) ) mlist of 
                         Some (_, Sequent_Structure (Formula_Agent a \<^sub>S)) \<Rightarrow> fun alpha a
                       | _ \<Rightarrow> [])
                 | _ \<Rightarrow> [])"

fun swapin :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> bool" where
"swapin fun m s = relAKACheck fun (match m s)"
(*uncommentR?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent-BEGIN*)(*(*uncommentR?Action?Action_Freevar?Agent?Agent_Freevar?Formula_Action?Formula_Agent?Sequent_Structure?Sequent-END*)*)

(*(*uncommentL?Structure_Bigcomma-BEGIN*)*)(*uncommentL?Structure_Bigcomma-END*)
fun bigcomma_cons_L :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_L ( (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) \<turnstile>\<^sub>S Y ) = Some [(;;\<^sub>S (X#Xs) \<turnstile>\<^sub>S Y)]"|
"bigcomma_cons_L _ = None"

fun bigcomma_cons_L2 :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_L2 ( ;;\<^sub>S (X#Xs) \<turnstile>\<^sub>S Y ) = Some [((B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) \<turnstile>\<^sub>S Y)]"|
"bigcomma_cons_L2 _ = None"


fun bigcomma_cons_R :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_R ( Y \<turnstile>\<^sub>S (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)) ) = Some [(Y \<turnstile>\<^sub>S ;;\<^sub>S (X#Xs))]"|
"bigcomma_cons_R _ = None"

fun bigcomma_cons_R2 :: "Sequent \<Rightarrow> Sequent list option" where
"bigcomma_cons_R2 ( Y \<turnstile>\<^sub>S ;;\<^sub>S (X#Xs) ) = Some [(Y \<turnstile>\<^sub>S (B\<^sub>S X (;\<^sub>S) (;;\<^sub>S Xs)))]"|
"bigcomma_cons_R2 _ = None"
(*uncommentR?Structure_Bigcomma-BEGIN*)(*(*uncommentR?Structure_Bigcomma-END*)*)

(*
value"replaceAll (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#(match (ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) X))) (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))"
value"(AgS\<^sub>S (forwK\<^sub>S) (Agent ''a'') (ActS\<^sub>S (forwA\<^sub>S) (Action ''beta'') (((Atprop ''X'') \<^sub>F) \<^sub>S)))"
value"match (ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) (ActS\<^sub>S (forwA\<^sub>S) (Action ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''a'') (((Atprop ''X'') \<^sub>F) \<^sub>S)))"
value"(ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''alpha'') (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))"
*)

(*(*uncommentL?RuleSwapout-BEGIN*)*)(*uncommentL?RuleSwapout-END*)
fun swapout_L_aux :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> (Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L_aux relAKA [] seq ( X \<turnstile>\<^sub>S ;;\<^sub>S [] ) = Some []" |
"swapout_L_aux relAKA (b#list) seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) = (
  case ( swapout_L_aux relAKA list seq ( X \<turnstile>\<^sub>S ;;\<^sub>S Ys ) ) of (Some list) \<Rightarrow> 
    (case (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X)))) of mlist \<Rightarrow>
      (case (replaceAll mlist seq) of applied \<Rightarrow>
        (if (relAKACheck relAKA (List.union (match seq applied) mlist) ) then 
        Some (applied#list) else None)))
| None \<Rightarrow> None)"|
"swapout_L_aux relAKA _ _ _ = None"

fun swapout_L :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L relAKA seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) = 
    swapout_L_aux relAKA (betaList relAKA (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))) seq ( X \<turnstile>\<^sub>S ;;\<^sub>S ((Y::Structure) # Ys) ) " |
"swapout_L _ _ _ = None"

fun swapout_L' :: "Action list \<Rightarrow> Action \<Rightarrow> Agent \<Rightarrow> Structure \<Rightarrow> Structure list \<Rightarrow> Sequent list option" where
"swapout_L' [] alpha a X [] = Some ([])" |
"swapout_L' (beta#actionList) alpha a X [] = None" |
"swapout_L' [] alpha a X (Y # Ys) = None" |
"swapout_L' (beta#actionList) alpha a X (Y # Ys) = (case swapout_L' actionList alpha a X Ys of 
   Some list \<Rightarrow> Some ((AgS\<^sub>S forwK\<^sub>S a ActS\<^sub>S forwA\<^sub>S beta X \<turnstile>\<^sub>S Y) #list) | None \<Rightarrow> None )"

fun swapout_L'' :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_L'' relAKA ( ActS\<^sub>S forwA\<^sub>S alpha (AgS\<^sub>S forwK\<^sub>S a X ) \<turnstile>\<^sub>S ;;\<^sub>S list ) = swapout_L' (relAKA alpha a) alpha a X list" |
"swapout_L'' _ _ = None"


fun swapout_R_aux :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> (Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R_aux relAKA [] seq ( ;;\<^sub>S [] \<turnstile>\<^sub>S X ) = Some []" |
"swapout_R_aux relAKA (b#list) seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) = (
  case ( swapout_R_aux relAKA list seq ( ;;\<^sub>S Ys \<turnstile>\<^sub>S X ) ) of (Some list) \<Rightarrow> 
    (case (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X)))) of mlist \<Rightarrow>
      (case (replaceAll mlist seq) of applied \<Rightarrow>
        (if (relAKACheck relAKA (List.union (match seq applied) mlist) ) then 
        Some (applied#list) else None)))
| None \<Rightarrow> None)"|
"swapout_R_aux _ _ _ _ = None"


fun swapout_R :: "(Action \<Rightarrow> Agent => Action list) \<Rightarrow> Sequent \<Rightarrow> Sequent \<Rightarrow> Sequent list option" where
"swapout_R relAKA seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) = 
    swapout_R_aux relAKA (betaList relAKA (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))) seq ( ;;\<^sub>S ((Y::Structure) # Ys) \<turnstile>\<^sub>S X ) " |
"swapout_R _ _ _ = None"
(*uncommentR?RuleSwapout-BEGIN*)(*(*uncommentR?RuleSwapout-END*)*)


(*(*uncommentL?Pre_L-BEGIN*)*)(*uncommentL?Pre_L-END*)
fun pre_l :: "Action \<Rightarrow> Sequent \<Rightarrow> bool" where
"pre_l a ((One\<^sub>F alpha)\<^sub>S \<turnstile>\<^sub>S X) = (a = alpha)"|
"pre_l a _ = False"
(*uncommentR?Pre_L-BEGIN*)(*(*uncommentR?Pre_L-END*)*)

(*(*uncommentL?Pre_R-BEGIN*)*)(*uncommentL?Pre_R-END*)
fun pre_r :: "Action \<Rightarrow> Sequent \<Rightarrow> bool" where
"pre_r a (X \<turnstile>\<^sub>S (One\<^sub>F alpha)\<^sub>S) = (a = alpha)"|
"pre_r a _ = False"
(*uncommentR?Pre_R-BEGIN*)(*(*uncommentR?Pre_R-END*)*)

(*
fun relAKAA :: "Action \<Rightarrow> Agent \<Rightarrow> Action \<Rightarrow> bool" where
"relAKAA (Action x) (Agent a) (Action y) = ((x = y) \<or> (x=''ep'' \<and> a = ''c'' \<and> y=''ew''))" |
"relAKAA _ _ _ = False"

definition "const_seq = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))"
definition "seq_empty = ((;;\<^sub>S []) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S))))"
definition "seq = ((;;\<^sub>S [((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S)]) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S))))"
definition "seqO = (((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S) \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (Agent ''c'') ActS\<^sub>S forwA\<^sub>S (Action ''epa'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S) )"

definition "mtchList X b Y= (map (\<lambda>(x,y). (Sequent_Structure x, Sequent_Structure y)) (((Formula_Action (?\<^sub>Act ''beta'') \<^sub>S, Formula_Action b \<^sub>S)#((?\<^sub>S ''Y''), Y)# (match ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) X))))"

definition "mList = mtchList ((ActS\<^sub>S (forwA\<^sub>S) (Action ''epa'') (AgS\<^sub>S (forwK\<^sub>S) (Agent ''c'') (((Atprop ''Ga'') \<^sub>F) \<^sub>S)))) (Action(''epa'')) ((AgF\<^sub>F (fboxK\<^sub>F) (Agent ''c'') (B\<^sub>F (Pre\<^sub>F (Action ''epa'')) (\<rightarrow>\<^sub>F) ((Atprop ''Ga'') \<^sub>F))) \<^sub>S)"
value " match (((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))) seqO "
value "relAKACheck relAKAA (List.union (match (((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))) seqO) mList)"
value "swapout_R relAKAA [] const_seq seq_empty"
value "swapout_R relAKAA [Action(''epa'')] const_seq seq"


value"swapout_L rel blist ( (?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X'') )"
*)


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

(*rules_rule_fun-BEGIN*)
primrec ruleRuleBigcomma :: "Locale \<Rightarrow> RuleBigcomma \<Rightarrow> ruleder" where
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Nil_R2 = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (;;\<^sub>S [])) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Nil_R = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (;;\<^sub>S []))])" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Nil_L2 = ((;;\<^sub>S []) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Nil_L = ((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((;;\<^sub>S []) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Cons_R2 = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD bigcomma_cons_R2" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Cons_R = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD bigcomma_cons_R" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Cons_L2 = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD bigcomma_cons_L2" |
"ruleRuleBigcomma x RuleBigcomma.Bigcomma_Cons_L = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD bigcomma_cons_L"

primrec ruleRuleCut :: "Locale \<Rightarrow> RuleCut \<Rightarrow> ruleder" where
"ruleRuleCut x RuleCut.SingleCut = ( case x of (CutFormula f) \<Rightarrow>((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S f \<^sub>S),(f \<^sub>S \<turnstile>\<^sub>S (?\<^sub>S ''Y''))]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )"

primrec ruleRuleDisp :: "Locale \<Rightarrow> RuleDisp \<Rightarrow> ruleder" where
"ruleRuleDisp x RuleDisp.Comma_impL_disp = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Z'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleDisp x RuleDisp.Comma_impR_disp2 = ((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')))])" |
"ruleRuleDisp x RuleDisp.ImpL_comma_disp2 = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''Z'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleDisp x RuleDisp.ImpR_comma_disp2 = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleDisp x RuleDisp.ImpR_comma_disp = ((B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleDisp x RuleDisp.ImpL_comma_disp = ((B\<^sub>S (?\<^sub>S ''Z'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleDisp x RuleDisp.Comma_impR_disp = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z''))) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleDisp x RuleDisp.Comma_impL_disp2 = ((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Z'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Y'')))])"

primrec ruleRuleDispAct :: "Locale \<Rightarrow> RuleDispAct \<Rightarrow> ruleder" where
"ruleRuleDispAct x RuleDispAct.Back_forw_A = ((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y'')))])" |
"ruleRuleDispAct x RuleDispAct.Forw_back_A2 = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y'')))])" |
"ruleRuleDispAct x RuleDispAct.Forw_back_A = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleDispAct x RuleDispAct.Back_forw_A2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])"

primrec ruleRuleDispK :: "Locale \<Rightarrow> RuleDispK \<Rightarrow> ruleder" where
"ruleRuleDispK x RuleDispK.Back_forw_K2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleDispK x RuleDispK.Back_forw_K = ((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y'')))])" |
"ruleRuleDispK x RuleDispK.Forw_back_K2 = ((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y'')))])" |
"ruleRuleDispK x RuleDispK.Forw_back_K = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])"

primrec ruleRuleGrish :: "Locale \<Rightarrow> RuleGrish \<Rightarrow> ruleder" where
"ruleRuleGrish x RuleGrish.Grishin_R2 = ((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z'')))])" |
"ruleRuleGrish x RuleGrish.Grishin_R = ((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z''))))])" |
"ruleRuleGrish x RuleGrish.Grishin_L = ((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''W'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleGrish x RuleGrish.Grishin_L2 = ((B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''W'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])"

primrec ruleRuleKnowledge :: "Locale \<Rightarrow> RuleKnowledge \<Rightarrow> ruleder" where
"ruleRuleKnowledge x RuleKnowledge.Refl_ForwK = ( case x of (LAgent a) \<Rightarrow>((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) a (?\<^sub>S ''Y'')))]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )"

primrec ruleRuleOp :: "Locale \<Rightarrow> RuleOp \<Rightarrow> ruleder" where
"ruleRuleOp x RuleOp.Bot_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((Z\<^sub>F (\<bottom>\<^sub>F)) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleOp x RuleOp.Top_L = (((Z\<^sub>F (\<top>\<^sub>F)) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOp x RuleOp.DImpR_L = (((B\<^sub>F (?\<^sub>F ''A'') (>-\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (\<rightarrow>\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleOp x RuleOp.ImpL_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S ((B\<^sub>F (?\<^sub>F ''B'') (\<leftarrow>\<^sub>F) (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''B'') \<^sub>S) (\<leftarrow>\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)))])" |
"ruleRuleOp x RuleOp.DImpL_R = ((B\<^sub>S (?\<^sub>S ''Y'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S ((B\<^sub>F (?\<^sub>F ''B'') (-<\<^sub>F) (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')),((?\<^sub>S ''Y'') \<turnstile>\<^sub>S ((?\<^sub>F ''B'') \<^sub>S))])" |
"ruleRuleOp x RuleOp.And_L = (((B\<^sub>F (?\<^sub>F ''A'') (\<and>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (;\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleOp x RuleOp.ImpR_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<rightarrow>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (\<rightarrow>\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)))])" |
"ruleRuleOp x RuleOp.Or_L = (((B\<^sub>F (?\<^sub>F ''A'') (\<or>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')),(((?\<^sub>F ''B'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleOp x RuleOp.Or_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<or>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S ((?\<^sub>F ''A'') \<^sub>S) (;\<^sub>S) ((?\<^sub>F ''B'') \<^sub>S)))])" |
"ruleRuleOp x RuleOp.ImpR_L = (((B\<^sub>F (?\<^sub>F ''A'') (\<rightarrow>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S)),(((?\<^sub>F ''B'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleOp x RuleOp.DImpL_L = (((B\<^sub>F (?\<^sub>F ''B'') (-<\<^sub>F) (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S ((?\<^sub>F ''B'') \<^sub>S) (\<leftarrow>\<^sub>S) ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleOp x RuleOp.And_R = ((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (\<and>\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S)),((?\<^sub>S ''Y'') \<turnstile>\<^sub>S ((?\<^sub>F ''B'') \<^sub>S))])" |
"ruleRuleOp x RuleOp.DImpR_R = ((B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S ((B\<^sub>F (?\<^sub>F ''A'') (>-\<^sub>F) (?\<^sub>F ''B'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')),((?\<^sub>S ''Y'') \<turnstile>\<^sub>S ((?\<^sub>F ''B'') \<^sub>S))])" |
"ruleRuleOp x RuleOp.ImpL_L = (((B\<^sub>F (?\<^sub>F ''B'') (\<leftarrow>\<^sub>F) (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S)),(((?\<^sub>F ''B'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleOp x RuleOp.Top_R = ((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S ((Z\<^sub>F (\<top>\<^sub>F)) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [])" |
"ruleRuleOp x RuleOp.Bot_L = (((Z\<^sub>F (\<bottom>\<^sub>F)) \<^sub>S) \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S))) \<Longrightarrow>RD (\<lambda>x. Some [])"

primrec ruleRuleOpAct :: "Locale \<Rightarrow> RuleOpAct \<Rightarrow> ruleder" where
"ruleRuleOpAct x RuleOpAct.FdiamA_L = (((ActF\<^sub>F (fdiamA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpAct x RuleOpAct.One_R = ((Phi\<^sub>S (?\<^sub>Act ''alpha'')) \<turnstile>\<^sub>S ((One\<^sub>F (?\<^sub>Act ''alpha'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [])" |
"ruleRuleOpAct x RuleOpAct.BdiamA_R = ((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''alpha'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S ((ActF\<^sub>F (bdiamA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S))])" |
"ruleRuleOpAct x RuleOpAct.FboxA_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((ActF\<^sub>F (fboxA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') ((?\<^sub>F ''A'') \<^sub>S)))])" |
"ruleRuleOpAct x RuleOpAct.Pre_L = ( case x of (PreFormula alpha f) \<Rightarrow>pre_l alpha \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [(f \<^sub>S \<turnstile>\<^sub>S (?\<^sub>S ''Y''))]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleOpAct x RuleOpAct.BboxA_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((ActF\<^sub>F (bboxA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''alpha'') ((?\<^sub>F ''A'') \<^sub>S)))])" |
"ruleRuleOpAct x RuleOpAct.BboxA_L = (((ActF\<^sub>F (bboxA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''alpha'') (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpAct x RuleOpAct.FboxA_L = (((ActF\<^sub>F (fboxA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpAct x RuleOpAct.Pre_R = ( case x of (PreFormula alpha f) \<Rightarrow>pre_r alpha \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S f \<^sub>S)]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleOpAct x RuleOpAct.BdiamA_L = (((ActF\<^sub>F (bdiamA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''alpha'') ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpAct x RuleOpAct.One_L = (((One\<^sub>F (?\<^sub>Act ''alpha'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((Phi\<^sub>S (?\<^sub>Act ''alpha'')) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpAct x RuleOpAct.FdiamA_R = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S ((ActF\<^sub>F (fdiamA\<^sub>F) (?\<^sub>Act ''alpha'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S))])"

primrec ruleRuleOpK :: "Locale \<Rightarrow> RuleOpK \<Rightarrow> ruleder" where
"ruleRuleOpK x RuleOpK.BdiamK_L = (((AgF\<^sub>F (bdiamK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpK x RuleOpK.FdiamK_R = ((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S ((AgF\<^sub>F (fdiamK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S))])" |
"ruleRuleOpK x RuleOpK.FboxK_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((AgF\<^sub>F (fboxK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') ((?\<^sub>F ''A'') \<^sub>S)))])" |
"ruleRuleOpK x RuleOpK.BboxK_L = (((AgF\<^sub>F (bboxK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpK x RuleOpK.BboxK_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((AgF\<^sub>F (bboxK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') ((?\<^sub>F ''A'') \<^sub>S)))])" |
"ruleRuleOpK x RuleOpK.FboxK_L = (((AgF\<^sub>F (fboxK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [(((?\<^sub>F ''A'') \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpK x RuleOpK.FdiamK_L = (((AgF\<^sub>F (fdiamK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') ((?\<^sub>F ''A'') \<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleOpK x RuleOpK.BdiamK_R = ((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S ((AgF\<^sub>F (bdiamK\<^sub>F) (?\<^sub>Ag ''a'') (?\<^sub>F ''A'')) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S ((?\<^sub>F ''A'') \<^sub>S))])"

primrec ruleRuleStruct :: "Locale \<Rightarrow> RuleStruct \<Rightarrow> ruleder" where
"ruleRuleStruct x RuleStruct.W_impL_R = ((B\<^sub>S (?\<^sub>S ''X'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStruct x RuleStruct.ImpL_I = ((B\<^sub>S (?\<^sub>S ''X'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.W_impL_L = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Z'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStruct x RuleStruct.ImpR_I2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleStruct x RuleStruct.E_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y2'') (;\<^sub>S) (?\<^sub>S ''Y1''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y1'') (;\<^sub>S) (?\<^sub>S ''Y2'')))])" |
"ruleRuleStruct x RuleStruct.IW_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleStruct x RuleStruct.IW_L = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.A_L2 = ((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''W'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleStruct x RuleStruct.E_L = ((B\<^sub>S (?\<^sub>S ''X2'') (;\<^sub>S) (?\<^sub>S ''X1'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X1'') (;\<^sub>S) (?\<^sub>S ''X2'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.A_R = ((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z'')))])" |
"ruleRuleStruct x RuleStruct.W_impR_R = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStruct x RuleStruct.C_L = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.C_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleStruct x RuleStruct.ImpR_I = ((B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.W_impR_L = ((B\<^sub>S (?\<^sub>S ''Z'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStruct x RuleStruct.A_L = ((B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''W'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z'')) \<turnstile>\<^sub>S (?\<^sub>S ''W''))])" |
"ruleRuleStruct x RuleStruct.A_R2 = ((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')) (;\<^sub>S) (?\<^sub>S ''Z''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''W'') \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (B\<^sub>S (?\<^sub>S ''Y'') (;\<^sub>S) (?\<^sub>S ''Z''))))])" |
"ruleRuleStruct x RuleStruct.I_impR2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y'')))])" |
"ruleRuleStruct x RuleStruct.I_impL = ((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.I_impR = ((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''X'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStruct x RuleStruct.ImpL_I2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (?\<^sub>S ''X'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''Y'')) \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleStruct x RuleStruct.I_impL2 = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (B\<^sub>S (?\<^sub>S ''Y'') (\<leftarrow>\<^sub>S) (?\<^sub>S ''X'')))])"

primrec ruleRuleStructAct :: "Locale \<Rightarrow> RuleStructAct \<Rightarrow> ruleder" where
"ruleRuleStructAct x RuleStructAct.A_nec_L = ((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (Z\<^sub>S (I\<^sub>S))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructAct x RuleStructAct.A_mon_L = ((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStructAct x RuleStructAct.Mon_A_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))))])" |
"ruleRuleStructAct x RuleStructAct.Nec_A_L = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (Z\<^sub>S (I\<^sub>S))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructAct x RuleStructAct.FS_A_L = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructAct x RuleStructAct.FS_A_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Z''))))])" |
"ruleRuleStructAct x RuleStructAct.A_mon_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))))])" |
"ruleRuleStructAct x RuleStructAct.A_FS_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Z''))))])" |
"ruleRuleStructAct x RuleStructAct.Nec_A_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (Z\<^sub>S (I\<^sub>S)))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleStructAct x RuleStructAct.Mon_A_L = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStructAct x RuleStructAct.A_FS_L = ((ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructAct x RuleStructAct.A_nec_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (Z\<^sub>S (I\<^sub>S)))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])"

primrec ruleRuleStructEA :: "Locale \<Rightarrow> RuleStructEA \<Rightarrow> ruleder" where
"ruleRuleStructEA x RuleStructEA.Reduce_R = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''a'')) (\<rightarrow>\<^sub>S) (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X''))))])" |
"ruleRuleStructEA x RuleStructEA.CompA_R = ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''a'')) (\<rightarrow>\<^sub>S) (?\<^sub>S ''X''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X''))))])" |
"ruleRuleStructEA x RuleStructEA.Balance = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''Y''))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStructEA x RuleStructEA.CompA_L = ((B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''a'')) (;\<^sub>S) (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (ActS\<^sub>S (backA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X''))) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])" |
"ruleRuleStructEA x RuleStructEA.Reduce_L = ((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X'')) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''a'')) (;\<^sub>S) (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''a'') (?\<^sub>S ''X''))) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))])"

primrec ruleRuleStructK :: "Locale \<Rightarrow> RuleStructK \<Rightarrow> ruleder" where
"ruleRuleStructK x RuleStructK.K_nec_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (Z\<^sub>S (I\<^sub>S)))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleStructK x RuleStructK.Nec_K_L = ((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (Z\<^sub>S (I\<^sub>S))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructK x RuleStructK.K_mon_L = ((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStructK x RuleStructK.Mon_K_L = ((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y''))) \<turnstile>\<^sub>S (?\<^sub>S ''Z''))])" |
"ruleRuleStructK x RuleStructK.FS_K_L = ((AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructK x RuleStructK.FS_K_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Z''))))])" |
"ruleRuleStructK x RuleStructK.Mon_K_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y''))))])" |
"ruleRuleStructK x RuleStructK.K_mon_R = ((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''X'') (;\<^sub>S) (?\<^sub>S ''Y'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Z'') \<turnstile>\<^sub>S (B\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')) (;\<^sub>S) (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y''))))])" |
"ruleRuleStructK x RuleStructK.K_FS_L = ((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((B\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Z''))) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])" |
"ruleRuleStructK x RuleStructK.Nec_K_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (Z\<^sub>S (I\<^sub>S)))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (Z\<^sub>S (I\<^sub>S)))])" |
"ruleRuleStructK x RuleStructK.K_FS_R = ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (B\<^sub>S (?\<^sub>S ''Y'') (\<rightarrow>\<^sub>S) (?\<^sub>S ''Z'')))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''X'') \<turnstile>\<^sub>S (B\<^sub>S (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Y'')) (\<rightarrow>\<^sub>S) (AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''Z''))))])" |
"ruleRuleStructK x RuleStructK.K_nec_L = ((AgS\<^sub>S (backK\<^sub>S) (?\<^sub>Ag ''a'') (Z\<^sub>S (I\<^sub>S))) \<turnstile>\<^sub>S (?\<^sub>S ''X'')) \<Longrightarrow>RD (\<lambda>x. Some [((Z\<^sub>S (I\<^sub>S)) \<turnstile>\<^sub>S (?\<^sub>S ''X''))])"

primrec ruleRuleSwapin :: "Locale \<Rightarrow> RuleSwapin \<Rightarrow> ruleder" where
"ruleRuleSwapin x RuleSwapin.Swapin_L = ( case x of (RelAKA rel) \<Rightarrow>swapin rel ((B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''alpha'')) (;\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''beta'') (?\<^sub>S ''X'')))) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>C ((B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''alpha'')) (;\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''beta'') (?\<^sub>S ''X'')))) \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some [((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) \<turnstile>\<^sub>S (?\<^sub>S ''Y''))]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleSwapin x RuleSwapin.Swapin_R = ( case x of (RelAKA rel) \<Rightarrow>swapin rel ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''alpha'')) (\<rightarrow>\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))))) \<Longrightarrow>C ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (B\<^sub>S (Phi\<^sub>S (?\<^sub>Act ''alpha'')) (\<rightarrow>\<^sub>S) (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''beta'') (?\<^sub>S ''X''))))) \<Longrightarrow>RD (\<lambda>x. Some [((?\<^sub>S ''Y'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))))]) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )"

primrec ruleRuleSwapout :: "Locale \<Rightarrow> RuleSwapout \<Rightarrow> ruleder" where
"ruleRuleSwapout x RuleSwapout.Swapout_L = ( case x of (RelAKA rel) \<Rightarrow>((ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X''))) \<turnstile>\<^sub>S (?\<^sub>S ''Ylist'')) \<Longrightarrow>RD swapout_L rel (AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleSwapout x RuleSwapout.Swapout_R = ( case x of (RelAKA rel) \<Rightarrow>((?\<^sub>S ''Ylist'') \<turnstile>\<^sub>S (ActS\<^sub>S (forwA\<^sub>S) (?\<^sub>Act ''alpha'') (AgS\<^sub>S (forwK\<^sub>S) (?\<^sub>Ag ''a'') (?\<^sub>S ''X'')))) \<Longrightarrow>RD swapout_R rel ((?\<^sub>S ''Y'') \<turnstile>\<^sub>S AgS\<^sub>S forwK\<^sub>S (?\<^sub>Ag ''a'') ActS\<^sub>S forwA\<^sub>S (?\<^sub>Act ''beta'') (?\<^sub>S ''X'')) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )"

primrec ruleRuleZer :: "Locale \<Rightarrow> RuleZer \<Rightarrow> ruleder" where
"ruleRuleZer x RuleZer.Prem = ( case x of (Premise seq) \<Rightarrow>(\<lambda>x. seq = x) \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some []) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleZer x RuleZer.Partial = ( case x of (Part struct) \<Rightarrow>(\<lambda>x. (case x of Sequent lhs rhs => struct = lhs \<or> struct = rhs )) \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some []) | _ \<Rightarrow> ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None) )" |
"ruleRuleZer x RuleZer.Id = ((((?\<^sub>A ''p'') \<^sub>F) \<^sub>S) \<turnstile>\<^sub>S (((?\<^sub>A ''p'') \<^sub>F) \<^sub>S)) \<Longrightarrow>RD (\<lambda>x. Some [])" |
"ruleRuleZer x RuleZer.Atom = ( atom \<Longrightarrow>C ((?\<^sub>S ''X'') \<turnstile>\<^sub>S (?\<^sub>S ''Y'')) \<Longrightarrow>RD (\<lambda>x. Some []) )"

fun rule :: "Locale \<Rightarrow> Rule \<Rightarrow> ruleder" where
"rule l (RuleBigcomma r) = ruleRuleBigcomma l r" |
"rule l (RuleCut r) = ruleRuleCut l r" |
"rule l (RuleDisp r) = ruleRuleDisp l r" |
"rule l (RuleDispAct r) = ruleRuleDispAct l r" |
"rule l (RuleDispK r) = ruleRuleDispK l r" |
"rule l (RuleGrish r) = ruleRuleGrish l r" |
"rule l (RuleKnowledge r) = ruleRuleKnowledge l r" |
"rule l (RuleOp r) = ruleRuleOp l r" |
"rule l (RuleOpAct r) = ruleRuleOpAct l r" |
"rule l (RuleOpK r) = ruleRuleOpK l r" |
"rule l (RuleStruct r) = ruleRuleStruct l r" |
"rule l (RuleStructAct r) = ruleRuleStructAct l r" |
"rule l (RuleStructEA r) = ruleRuleStructEA l r" |
"rule l (RuleStructK r) = ruleRuleStructK l r" |
"rule l (RuleSwapin r) = ruleRuleSwapin l r" |
"rule l (RuleSwapout r) = ruleRuleSwapout l r" |
"rule l (RuleZer r) = ruleRuleZer l r" |
"rule _ _ = ((?\<^sub>S''X'') \<turnstile>\<^sub>S (?\<^sub>S''Y'')) \<Longrightarrow>RD (\<lambda>x. None)"
(*rules_rule_fun-END*)

fun fst :: "ruleder \<Rightarrow> Sequent" and snd :: "ruleder \<Rightarrow> Sequent \<Rightarrow> Sequent list option" and cond :: "ruleder \<Rightarrow> (Sequent \<Rightarrow> bool) option" where
"fst (ruleder x _) = x" |
"fst (ruleder_cond _ x _) = x" |
"snd (ruleder _ y) = y" |
"snd (ruleder_cond _ _ y) = y" |
"cond (ruleder_cond c _ _) = Some c" |
"cond (ruleder _ _) = None"

fun der :: "Locale \<Rightarrow> Rule \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der l r s =( case (snd (rule l r)) s of
                None \<Rightarrow> (Fail, [])
              | Some conclusion \<Rightarrow> 
                  if (ruleMatch (fst (rule l r)) s) then 
                    case cond (rule l r) of 
                      None \<Rightarrow> ( r, map (replaceAll (match (fst (rule l r)) s) ) conclusion )
                    | Some condition \<Rightarrow> ( if condition s 
                        then (r, map (replaceAll (match (fst (rule l r)) s) ) conclusion )
                        else (Fail, []) )
                  else (Fail, []) )"


(*(*uncommentL?RuleCut-BEGIN*)*)(*uncommentL?RuleCut-END*)
(*der cut applies a supplied formula if the cut rule is used - a bit hacky atm *) 
(*fun der_cut :: "Rule \<Rightarrow> Formula \<Rightarrow> Sequent \<Rightarrow> (Rule * Sequent list)"
where
"der_cut (RuleCut RuleCut.SingleCut) cutForm s = (if (ruleMatch (fst (rule (RuleCut RuleCut.SingleCut))) s) 
   then ((RuleCut RuleCut.SingleCut), map (replaceAll (match (fst (rule (RuleCut RuleCut.SingleCut))) s @ (map (\<lambda>(x,y). (Sequent_Structure (Structure_Formula x), Sequent_Structure (Structure_Formula y))) (match (?\<^sub>F''A'') cutForm))) ) (snd (rule (RuleCut RuleCut.SingleCut)))) 
   else (Fail, []))" |
"der_cut _ _ _ = (Fail, [])"*)
(*uncommentR?RuleCut-BEGIN*)(*(*uncommentR?RuleCut-END*)*)

primrec ant :: "Sequent \<Rightarrow> Structure" where
"ant (Sequent x y) = x" |
"ant (Sequent_Structure x) = x"
primrec consq :: "Sequent \<Rightarrow> Structure" where
"consq (Sequent x y) = y"|
"consq (Sequent_Structure x) = x"

fun replaceIntoPT_aux :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree \<Rightarrow> Prooftree" and 
  replaceIntoPT_list :: "(Sequent \<times> Sequent) list \<Rightarrow> Prooftree list \<Rightarrow> Prooftree list" where 
"replaceIntoPT_aux list (Prooftree c (RuleMacro s pt) ptlist) = Prooftree (replaceAll list c) (RuleMacro s (replaceIntoPT_aux list pt)) (replaceIntoPT_list list ptlist)" |
"replaceIntoPT_aux list (Prooftree c r ptlist) = Prooftree (replaceAll list c) r (replaceIntoPT_list list ptlist)" |
"replaceIntoPT_list list [] = []" |
"replaceIntoPT_list list (l#ist) = (replaceIntoPT_aux list l)#(replaceIntoPT_list list ist)"

fun replaceIntoPT :: "Sequent \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceIntoPT seq (Prooftree c r ptlist) = replaceIntoPT_aux (match c seq) (Prooftree c r ptlist)"


fun collectPremises :: "Prooftree \<Rightarrow> Sequent list" where
"collectPremises (Prooftree p (RuleZer Prem) []) = [p]" |
"collectPremises (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectPremises list) []" |
"collectPremises (Prooftree _ _ list) = foldr append (map collectPremises list) []"

fun collectPremisesToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectPremisesToLocale pt = map Premise (collectPremises pt)"

fun collectCutFormulas :: "Prooftree \<Rightarrow> Formula list" where
"collectCutFormulas (Prooftree _ (RuleCut _) [l, r]) = (
  (case (consq (concl l)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl r)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] @ (collectCutFormulas l) @ (collectCutFormulas r) else (collectCutFormulas l) @ (collectCutFormulas r)) |  _ \<Rightarrow> (collectCutFormulas l) @ (collectCutFormulas r) ) |
    _ \<Rightarrow> (case (consq (concl r)) of (Structure_Formula f) \<Rightarrow> (case (ant (concl l)) of (Structure_Formula f') \<Rightarrow> (if f = f' then [f] @ (collectCutFormulas l) @ (collectCutFormulas r) else (collectCutFormulas l) @ (collectCutFormulas r)) |  _ \<Rightarrow> (collectCutFormulas l) @ (collectCutFormulas r)))
  )
)" |
"collectCutFormulas (Prooftree _ (RuleMacro _ pt) list) = foldr append (map collectCutFormulas list) (collectCutFormulas pt)" |
"collectCutFormulas (Prooftree _ _ list) = foldr append (map collectCutFormulas list) []"

fun collectCutFormulasToLocale :: "Prooftree \<Rightarrow> Locale list" where
"collectCutFormulasToLocale pt = map CutFormula (collectCutFormulas pt)"


fun isProofTree :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTree loc (s \<Longleftarrow> PT(RuleMacro n pt) ptlist) = (
  s = (concl pt) \<and> 
  isProofTree (append loc (collectPremisesToLocale pt)) pt \<and>
  set (collectPremises pt) = set (map concl ptlist) \<and>
  foldr (op \<and>) (map (isProofTree loc) ptlist) True
)"|
"isProofTree loc (s \<Longleftarrow> PT(r) l) = ( 
  foldr (op \<and>) (map (isProofTree loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"


fun isProofTreeWoMacro :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWoMacro loc (s \<Longleftarrow> PT(RuleMacro n pt) ptlist) = False"|
"isProofTreeWoMacro loc (s \<Longleftarrow> PT(r) l) = ( 
  foldr (op \<and>) (map (isProofTreeWoMacro loc) l) True \<and>
  foldr (op \<or>) (map (\<lambda>x. (
    set (Product_Type.snd (der x r s)) = set (map concl l) \<and> 
    Fail \<noteq> Product_Type.fst (der x r s)
  )) loc) False
)"

fun isProofTreeWithCut :: "Locale list \<Rightarrow> Prooftree \<Rightarrow> bool" where
"isProofTreeWithCut loc pt = isProofTree (append loc (collectCutFormulasToLocale pt)) pt"


(*"isProofTree loc (s \<Longleftarrow> B(r) l) = ( foldr (op \<and>) (map (isProofTree loc) l) True \<and> set (Product_Type.snd (der r s)) = set (map concl l) )"*)

(*
fun isProofTreeWCut :: "Prooftree \<Rightarrow> bool" where
"isProofTreeWCut (s \<Longleftarrow> C(f) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der_cut (RuleCut RuleCut.SingleCut) f s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))" |
"isProofTreeWCut (s \<Longleftarrow> Z(r)) = ruleMatch (fst (rule (RuleZer r))) s" | 
"isProofTreeWCut (s \<Longleftarrow> U(r) t) = (isProofTreeWCut t \<and> (case (der (RuleU r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> D(r) t) = (isProofTreeWCut t \<and> (case (der (RuleDisp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> O(r) t) = (isProofTreeWCut t \<and> (case (der (RuleOp r) s) of (Fail, []) \<Rightarrow> False | (ru,[se]) \<Rightarrow> se = concl t))" |
"isProofTreeWCut (s \<Longleftarrow> B(r) t1 ; t2) = (isProofTreeWCut t1 \<and> isProofTreeWCut t2 \<and> (case (der (RuleBin r) s) of (Fail, []) \<Rightarrow> False | (ru,[se1, se2]) \<Rightarrow> (se1 = concl t1 \<and> se2 = concl t2) \<or> (se1 = concl t2 \<and> se2 = concl t1)))"

lemma isProofTree_concl_freevars[simp]:
  fixes pt
  assumes "isProofTree pt"
  shows "freevars (concl pt) = {}"
proof (cases pt)
case (Zer s r)
  from assms have 1: "ruleMatch (fst (rule (RuleZer r))) s" by (metis (poly_guards_query) Zer isProofTree.simps(1))
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Zer concl.simps)
next
case (Unary s r t)
  with assms  have "(der (RuleU r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleU r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Unary concl.simps)
next
case (Display s r t)
  with assms  have "(der (RuleDisp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleDisp r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Display concl.simps)
next
case (Operational s r t)
  with assms  have "(der (RuleOp r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleOp r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Operational concl.simps(4))
next
case (Binary s r t1 t2)
  with assms  have "(der (RuleBin r) s) \<noteq> (Fail, [])" by fastforce
  then have 1: "ruleMatch (fst (rule (RuleBin r))) s" by (metis der.simps)
  have free: "freevars s = {}" by (metis "1" ruleMatch_def)
  thus ?thesis by (metis Binary concl.simps)
next
case (Cut s r t1 t2)
  then have False by (metis assms isProofTree.simps)
  thus ?thesis ..
qed
*)
(*
- equality of shallow and deep terms
  - for every deep-term with a valid proof tree there is an equivalent shallow-term in the set derivable
  - shallow\<Rightarrow>deep possible induction proof on the rules of the shallow embedding set*)

definition "ruleList = (*rules_rule_list-BEGIN*)(map (RuleBigcomma) [Bigcomma_Nil_R,Bigcomma_Cons_R,Bigcomma_Cons_L2,Bigcomma_Nil_L2,Bigcomma_Cons_R2,Bigcomma_Cons_L,Bigcomma_Nil_R2,Bigcomma_Nil_L]) @ (map (RuleCut) [SingleCut]) @ (map (RuleDisp) [Comma_impL_disp,Comma_impR_disp2,ImpL_comma_disp2,ImpR_comma_disp2,ImpR_comma_disp,ImpL_comma_disp,Comma_impR_disp,Comma_impL_disp2]) @ (map (RuleDispAct) [Back_forw_A,Forw_back_A2,Forw_back_A,Back_forw_A2]) @ (map (RuleDispK) [Back_forw_K2,Back_forw_K,Forw_back_K2,Forw_back_K]) @ (map (RuleGrish) [Grishin_R2,Grishin_R,Grishin_L,Grishin_L2]) @ (map (RuleKnowledge) [Refl_ForwK]) @ (map (RuleOp) [Bot_R,Top_L,DImpR_L,ImpL_R,DImpL_R,And_L,ImpR_R,Or_L,Or_R,ImpR_L,DImpL_L,And_R,DImpR_R,ImpL_L,Top_R,Bot_L]) @ (map (RuleOpAct) [FdiamA_L,One_R,BdiamA_R,FboxA_R,Pre_L,BboxA_R,BboxA_L,FboxA_L,Pre_R,BdiamA_L,One_L,FdiamA_R]) @ (map (RuleOpK) [BdiamK_L,FdiamK_R,FboxK_R,BboxK_L,BboxK_R,FboxK_L,FdiamK_L,BdiamK_R]) @ (map (RuleStruct) [W_impL_R,ImpL_I,W_impL_L,ImpR_I2,E_R,IW_R,IW_L,A_L2,E_L,A_R,W_impR_R,C_L,C_R,ImpR_I,W_impR_L,A_L,A_R2,I_impR2,I_impL,I_impR,ImpL_I2,I_impL2]) @ (map (RuleStructAct) [A_nec_L,A_mon_L,Mon_A_R,Nec_A_L,FS_A_L,FS_A_R,A_mon_R,A_FS_R,Nec_A_R,Mon_A_L,A_FS_L,A_nec_R]) @ (map (RuleStructEA) [Reduce_R,CompA_R,Balance,CompA_L,Reduce_L]) @ (map (RuleStructK) [K_nec_R,Nec_K_L,K_mon_L,Mon_K_L,FS_K_L,FS_K_R,Mon_K_R,K_mon_R,K_FS_L,Nec_K_R,K_FS_R,K_nec_L]) @ (map (RuleSwapin) [Swapin_L,Swapin_R]) @ (map (RuleSwapout) [Swapout_L,Swapout_R]) @ (map (RuleZer) [Prem,Partial,Id,Atom])(*rules_rule_list-END*)"

lemma Atprop_without_Freevar[simp]: "\<And>a. freevars a = {} \<Longrightarrow> \<exists>q. a = Atprop q"
  by (metis Atprop.exhaust freevars_Atprop.simps(1) insert_not_empty)

(*
(*perhaps things bellow should be moved to a separate utils file?? *)

fun replaceLPT :: "Prooftree \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceLPT (s \<Longleftarrow> B(r) t1 ; t2) rep = (s \<Longleftarrow> B(r) rep ; t2)" |
"replaceLPT pt rep = pt"

fun replaceRPT :: "Prooftree \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replaceRPT (s \<Longleftarrow> B(r) t1 ; t2) rep = (s \<Longleftarrow> B(r) t1 ; rep)" |
"replaceRPT pt rep = pt"
*)

(*(*uncommentL?Agent?Agent_Freevar-BEGIN*)*)(*uncommentL?Agent?Agent_Freevar-END*)
primrec rulifyAgent :: "Agent \<Rightarrow> Agent" where
"rulifyAgent (Agent a) = Agent_Freevar a" |
"rulifyAgent (Agent_Freevar a) = Agent_Freevar a"
(*uncommentR?Agent?Agent_Freevar-BEGIN*)(*(*uncommentR?Agent?Agent_Freevar-END*)*)

(*(*uncommentL?Action?Action_Freevar-BEGIN*)*)(*uncommentL?Action?Action_Freevar-END*)
primrec rulifyAction :: "Action \<Rightarrow> Action" where
"rulifyAction (Action a) = Action_Freevar a" |
"rulifyAction (Action_Freevar a) = Action_Freevar a"
(*uncommentR?Action?Action_Freevar-BEGIN*)(*(*uncommentR?Action?Action_Freevar-END*)*)

(*(*uncommentL?Formula-BEGIN*)*)(*uncommentL?Formula-END*)
fun rulifyFormula :: "Formula \<Rightarrow> Formula" where
(*(*uncommentL?Formula_Atprop-BEGIN*)*)(*uncommentL?Formula_Atprop-END*)
"rulifyFormula (Formula_Atprop(Atprop (f#a))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (Formula_Freevar (f#a)) else (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
(*uncommentR?Formula_Atprop-BEGIN*)(*(*uncommentR?Formula_Atprop-END*)*)
(*(*uncommentL?Formula_Bin-BEGIN*)*)(*uncommentL?Formula_Bin-END*)
"rulifyFormula (Formula_Bin x c y) = (Formula_Bin (rulifyFormula x) c (rulifyFormula y))" |
(*uncommentR?Formula_Bin-BEGIN*)(*(*uncommentR?Formula_Bin-END*)*)
(*(*uncommentL?Formula_Agent_Formula-BEGIN*)*)(*uncommentL?Formula_Agent_Formula-END*)
"rulifyFormula (Formula_Agent_Formula c a x) = (Formula_Agent_Formula c (rulifyAgent a) (rulifyFormula x) )" |
(*uncommentR?Formula_Agent_Formula-BEGIN*)(*(*uncommentR?Formula_Agent_Formula-END*)*)
(*(*uncommentL?Formula_Action_Formula-BEGIN*)*)(*uncommentL?Formula_Action_Formula-END*)
"rulifyFormula (Formula_Action_Formula c a x) = (Formula_Action_Formula c (rulifyAction a) (rulifyFormula x) )" |
(*uncommentR?Formula_Action_Formula-BEGIN*)(*(*uncommentR?Formula_Action_Formula-END*)*)
(*(*uncommentL?Formula_Precondition-BEGIN*)*)(*uncommentL?Formula_Precondition-END*)
"rulifyFormula (Formula_Precondition a) = (Formula_Precondition (rulifyAction a))" |
(*uncommentR?Formula_Precondition-BEGIN*)(*(*uncommentR?Formula_Precondition-END*)*)
"rulifyFormula x = x"
(*uncommentR?Formula-BEGIN*)(*(*uncommentR?Formula-END*)*)

(*(*uncommentL?Structure-BEGIN*)*)(*uncommentL?Structure-END*)
fun rulifyStructure :: "Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Formula?Formula_Atprop-BEGIN*)*)(*uncommentL?Structure_Formula?Formula_Atprop-END*)
"rulifyStructure (Structure_Formula (Formula_Atprop(Atprop (f#a)))) = 
(if CHR ''A'' \<le> f \<and> f \<le> CHR ''Z'' then (
  if f = CHR ''F'' then Structure_Formula (Formula_Freevar (f#a)) else Structure_Freevar (f#a)
  ) else Structure_Formula (Formula_Atprop (Atprop_Freevar (f#a)))
)" |
(*uncommentR?Structure_Formula?Formula_Atprop-BEGIN*)(*(*uncommentR?Structure_Formula?Formula_Atprop-END*)*)
(*(*uncommentL?Structure_Formula-BEGIN*)*)(*uncommentL?Structure_Formula-END*)
"rulifyStructure (Structure_Formula x) = Structure_Formula (rulifyFormula x)" | 
(*uncommentR?Structure_Formula-BEGIN*)(*(*uncommentR?Structure_Formula-END*)*)
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*)
"rulifyStructure (Structure_Bin x c y) = (Structure_Bin (rulifyStructure x) c (rulifyStructure y))" |
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*)
"rulifyStructure (Structure_Agent_Structure c a x) = (Structure_Agent_Structure c (rulifyAgent a) (rulifyStructure x) )" |
(*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*)
"rulifyStructure (Structure_Action_Structure c a x) = (Structure_Action_Structure c (rulifyAction a) (rulifyStructure x) )" |
(*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Bigcomma-BEGIN*)*)(*uncommentL?Structure_Bigcomma-END*)
"rulifyStructure (Structure_Bigcomma list) = (Structure_Bigcomma (map rulifyStructure list))" |
(*uncommentR?Structure_Bigcomma-BEGIN*)(*(*uncommentR?Structure_Bigcomma-END*)*)
(*(*uncommentL?Structure_Phi-BEGIN*)*)(*uncommentL?Structure_Phi-END*)
"rulifyStructure (Structure_Phi a) = (Structure_Phi (rulifyAction a))" |
(*uncommentR?Structure_Phi-BEGIN*)(*(*uncommentR?Structure_Phi-END*)*)
"rulifyStructure x = x"
(*uncommentR?Structure-BEGIN*)(*(*uncommentR?Structure-END*)*)

(*(*uncommentL?Sequent-BEGIN*)*)(*uncommentL?Sequent-END*)
primrec rulifySequent :: "Sequent \<Rightarrow> Sequent" where
"rulifySequent (Sequent x y) = Sequent (rulifyStructure x) (rulifyStructure y)"|
"rulifySequent (Sequent_Structure x) = (Sequent_Structure x)"
(*uncommentR?Sequent-BEGIN*)(*(*uncommentR?Sequent-END*)*)

fun rulifyProoftree :: "Prooftree \<Rightarrow> Prooftree" where
"rulifyProoftree (Prooftree s (RuleMacro str pt) list) = Prooftree (rulifySequent s) (RuleMacro str (rulifyProoftree pt)) (map rulifyProoftree list)" |
"rulifyProoftree (Prooftree s r list) = (Prooftree (rulifySequent s) r (map rulifyProoftree list))"


fun replaceIntoProoftree :: "Prooftree list \<Rightarrow> Prooftree \<Rightarrow> Prooftree"  where
"replaceIntoProoftree [] (Prooftree s (RuleZer Prem) []) = (Prooftree s (RuleZer Prem) [])" |
"replaceIntoProoftree (l#ist) (Prooftree s (RuleZer Prem) []) = (if (concl l) = s then l else replaceIntoProoftree ist (Prooftree s (RuleZer Prem) []))" |
"replaceIntoProoftree list (Prooftree s r []) =  (Prooftree s r [])" |
"replaceIntoProoftree list (Prooftree s r l) =  (Prooftree s r (map (replaceIntoProoftree list) l))"

fun expandProoftree :: "Prooftree \<Rightarrow> Prooftree"  where
"expandProoftree (Prooftree _ (RuleMacro n (Prooftree s r l)) list) = (Prooftree s r (map (replaceIntoProoftree (map expandProoftree list)) (map expandProoftree l)))" |
"expandProoftree (Prooftree s r list) = Prooftree s r (map expandProoftree list)"

fun collect_freevars_Structure :: "Structure \<Rightarrow> Structure list" where
(*(*uncommentL?Structure_Formula-BEGIN*)*)(*uncommentL?Structure_Formula-END*)  "collect_freevars_Structure (Structure_Formula f) = [Structure_Formula f]" (*uncommentR?Structure_Formula-BEGIN*)(*(*uncommentR?Structure_Formula-END*)*)
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) | "collect_freevars_Structure (Structure_Bin l _ r) = (collect_freevars_Structure l) @ (collect_freevars_Structure r)" (*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Freevar-BEGIN*)*)(*uncommentL?Structure_Freevar-END*) | "collect_freevars_Structure (Structure_Freevar free) = [Structure_Freevar free]" (*uncommentR?Structure_Freevar-BEGIN*)(*(*uncommentR?Structure_Freevar-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*) | "collect_freevars_Structure (Structure_Action_Structure oper ac struct) = [Structure_Formula (Formula_Action ac)] @ (collect_freevars_Structure struct)" (*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*) | "collect_freevars_Structure (Structure_Agent_Structure oper ag struct) = [Structure_Formula (Formula_Agent ag)] @ (collect_freevars_Structure struct)" (*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
(*(*uncommentL?Structure_Phi-BEGIN*)*)(*uncommentL?Structure_Phi-END*) | "collect_freevars_Structure (Structure_Phi a) = [Structure_Phi a]"  (*uncommentR?Structure_Phi-BEGIN*)(*(*uncommentR?Structure_Phi-END*)*)
(*(*uncommentL?Structure_Zer-BEGIN*)*)(*uncommentL?Structure_Zer-END*) | "collect_freevars_Structure (Structure_Zer z) = [Structure_Zer z]" (*uncommentR?Structure_Zer-BEGIN*)(*(*uncommentR?Structure_Zer-END*)*)
(*(*uncommentL?Structure_Bigcomma-BEGIN*)*)(*uncommentL?Structure_Bigcomma-END*) | "collect_freevars_Structure (Structure_Bigcomma list) = foldr (op @) (map collect_freevars_Structure list) []" (*uncommentR?Structure_Bigcomma-BEGIN*)(*(*uncommentR?Structure_Bigcomma-END*)*)


fun collect_freevars_Sequent :: "Sequent \<Rightarrow> Structure list" where
"collect_freevars_Sequent (Sequent l r) = (collect_freevars_Structure l) @ (collect_freevars_Structure r)" |
"collect_freevars_Sequent (Sequent_Structure _) = []"


fun is_display_rule :: "Rule \<Rightarrow> Rule list" where
"is_display_rule r = 
(if (case (snd (rule Empty r) (fst (rule Empty r)) ) of Some list \<Rightarrow>
  (case list of h#rest \<Rightarrow>
  multiset_of (collect_freevars_Sequent (fst (rule Empty r))) = 
  multiset_of (collect_freevars_Sequent h ) | _ \<Rightarrow> False ) | _ \<Rightarrow> False )
then [r] 
else [])"

definition displayRules :: "Rule list" where
"displayRules = foldr (op @) (map is_display_rule ruleList) []"

value "displayRules"

(*
definition "lhs = collect_freevars_Sequent (fst (rule Empty (RuleStruct I_impL)))"
definition "rhs = collect_freevars_Sequent (hd (the (snd (rule Empty (RuleStruct I_impL)) (fst (rule Empty (RuleStruct E_L)))  )))"

value "multiset_of lhs = multiset_of rhs"
*)

datatype polarity = Plus ("+p") | Minus ("-p") | N

fun polarity_weird_xor :: "polarity \<Rightarrow> polarity \<Rightarrow> polarity" (infix "\<or>p" 400) where
"polarity_weird_xor +p N = +p" |
"polarity_weird_xor -p N = -p" |
"polarity_weird_xor N x = x" |
"polarity_weird_xor +p _ = N" |
"polarity_weird_xor -p _ = N"


fun polarity_not :: "polarity \<Rightarrow> polarity" ( "\<not>p _") where
"polarity_not -p = +p" |
"polarity_not +p = -p" |
"polarity_not N = N"


fun polarity_weird_and :: "polarity \<Rightarrow> polarity \<Rightarrow> polarity" (infix "\<and>p" 400) where
"polarity_weird_and -p x = \<not>p x" |
"polarity_weird_and +p x = x" |
"polarity_weird_and N _ = N"

lemma polarity_weird_xor_comm: "a \<or>p b = b \<or>p a"
apply (cases a, (cases b, auto)+)
done

lemma polarity_weird_and_comm: "a \<and>p b = b \<and>p a"
apply (cases a, (cases b, auto)+)
done

fun structure_Op_polarity :: "Structure_Bin_Op \<Rightarrow> (polarity \<times> polarity)" where
(*(*uncommentL?Structure_Comma-BEGIN*)*)(*uncommentL?Structure_Comma-END*) 
   "structure_Op_polarity Structure_Comma = (+p, +p)"
(*uncommentR?Structure_Comma-BEGIN*)(*(*uncommentR?Structure_Comma-END*)*)
(*(*uncommentL?Structure_ImpL-BEGIN*)*)(*uncommentL?Structure_ImpL-END*) 
 | "structure_Op_polarity Structure_ImpL = (+p, -p)"
(*uncommentR?Structure_ImpL-BEGIN*)(*(*uncommentR?Structure_ImpL-END*)*)
(*(*uncommentL?Structure_ImpR-BEGIN*)*)(*uncommentL?Structure_ImpR-END*) 
 | "structure_Op_polarity Structure_ImpR = (-p, +p)"
(*uncommentR?Structure_ImpR-BEGIN*)(*(*uncommentR?Structure_ImpR-END*)*)


(*we assume the structure appears in the sequent exactly once*)
fun polarity_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> polarity" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) 
"polarity_Structure s (Structure_Bin l oper r) = (
  if l = s then prod.fst (structure_Op_polarity oper)
  else if r = s then prod.snd (structure_Op_polarity oper)
  else ((prod.fst (structure_Op_polarity oper)) \<and>p (polarity_Structure s l)) \<or>p ((prod.snd (structure_Op_polarity oper)) \<and>p (polarity_Structure s r)) )" | 
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*) "polarity_Structure s (Structure_Action_Structure oper ac struct) = (polarity_Structure s struct)" | (*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*) "polarity_Structure s (Structure_Agent_Structure oper ag struct) = (polarity_Structure s struct)" | (*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
"polarity_Structure s x = (if s = x then +p else N)"


fun polarity_Sequent :: "Structure \<Rightarrow> Sequent \<Rightarrow> polarity" where
"polarity_Sequent s (Sequent lhs rhs) = (\<not>p(polarity_Structure s lhs)) \<or>p (polarity_Structure s rhs)" |
"polarity_Sequent s _ = N"

fun partial_goal :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) 
"partial_goal s (Structure_Bin l oper r) = (case (polarity_Structure s l) of N \<Rightarrow> (if s = l then l else r) | _ \<Rightarrow> l)" |
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*) "partial_goal s (Structure_Action_Structure oper ac struct) = struct" | (*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*) "partial_goal s (Structure_Agent_Structure oper ag struct) = struct" | (*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
"partial_goal s x = x"

fun partial_goal_complement :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) 
"partial_goal_complement s (Structure_Bin l oper r) = (case (polarity_Structure s l) of N \<Rightarrow> (if s = l then r else l) | _ \<Rightarrow> r)" |
(*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*) "partial_goal_complement s (Structure_Action_Structure oper ac struct) = struct" | (*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*) "partial_goal_complement s (Structure_Agent_Structure oper ag struct) = struct" | (*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
"partial_goal_complement s x = x"


lemma partial_goal:
  fixes oper x y s
  shows "((partial_goal s (Structure_Bin x oper y)) = x) \<or> (partial_goal s (Structure_Bin x oper y)) = y"
proof auto
assume "s = x" "(case polarity_Structure x x of +p \<Rightarrow> x | _ \<Rightarrow> x) \<noteq> y"
then show "(case polarity_Structure x x of +p \<Rightarrow> x | _ \<Rightarrow> x) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
next
assume "s \<noteq> x" "(case polarity_Structure s x of N \<Rightarrow> y | _ \<Rightarrow> x) \<noteq> y"
then show "(case polarity_Structure s x of N \<Rightarrow> y | _ \<Rightarrow> x) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
qed

lemma partial_goal_complement:
  fixes oper x y s
  shows "((partial_goal_complement s (Structure_Bin x oper y)) = x) \<or> (partial_goal_complement s (Structure_Bin x oper y)) = y"
proof auto
assume "s = x" "(case polarity_Structure x x of +p \<Rightarrow> y | _ \<Rightarrow> y) \<noteq> y"
then show "(case polarity_Structure x x of +p \<Rightarrow> y | _ \<Rightarrow> y) = x"
  by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
next
assume "s \<noteq> x" "(case polarity_Structure s x of N \<Rightarrow> x | _ \<Rightarrow> y) \<noteq> y"
then show "(case polarity_Structure s x of N \<Rightarrow> x | _ \<Rightarrow> y) = x" by (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))
qed


lemma partial_goal_and_complement:
  fixes oper x y s
  defines "struct \<equiv> Structure_Bin x oper y"
  shows "( (partial_goal s struct) = x \<and> (partial_goal_complement s struct) = y ) \<or> 
         ( (partial_goal_complement s struct) = x \<and> (partial_goal s struct) = y )"
using struct_def
apply auto
apply (metis polarity.exhaust polarity.simps(7) polarity.simps(8) polarity.simps(9))+
done


fun position_in_Sequent :: "Structure \<Rightarrow> Sequent \<Rightarrow> polarity" where
"position_in_Sequent s (Sequent l r) = (
  if s = l then -p
  else if (polarity_Structure s l) \<noteq> N then -p
  else if s = r then +p 
  else if (polarity_Structure s r) \<noteq> N then +p
  else N )" |
"position_in_Sequent s _ = N"




fun fresh_name_aux :: "string list \<Rightarrow> string \<Rightarrow> string set \<Rightarrow> string" where
"fresh_name_aux [] s _ = s" |
"fresh_name_aux (x#xs) s full = (if (s@x) \<notin> full then s@x else (fresh_name_aux xs (s@x) full) )"


definition fresh_name :: "string list \<Rightarrow> string" where
"fresh_name list = fresh_name_aux list ''X'' (set list)"


fun collect_SFAtprop_names :: "Structure \<Rightarrow> string list" where
(*(*uncommentL?Structure_Formula?Formula_Atprop?Atprop-BEGIN*)*)(*uncommentL?Structure_Formula?Formula_Atprop?Atprop-END*)  "collect_SFAtprop_names (Structure_Formula (Formula_Atprop (Atprop x))) = [x]" |(*uncommentR?Structure_Formula?Formula_Atprop?Atprop-BEGIN*)(*(*uncommentR?Structure_Formula?Formula_Atprop?Atprop-END*)*)
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) "collect_SFAtprop_names (Structure_Bin l oper r) = (collect_SFAtprop_names l) @ (collect_SFAtprop_names r)" | (*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*) "collect_SFAtprop_names (Structure_Action_Structure oper ac struct) = collect_SFAtprop_names struct" | (*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*) "collect_SFAtprop_names (Structure_Agent_Structure oper ag struct) = collect_SFAtprop_names struct" | (*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
"collect_SFAtprop_names s = []"

fun replace_SFAtprop_into_Structure :: "Structure \<Rightarrow> Structure \<Rightarrow> Structure \<Rightarrow> Structure" where
(*(*uncommentL?Structure_Bin-BEGIN*)*)(*uncommentL?Structure_Bin-END*) "replace_SFAtprop_into_Structure sfa repl (Structure_Bin l oper r) = Structure_Bin (replace_SFAtprop_into_Structure sfa repl l) oper (replace_SFAtprop_into_Structure sfa repl r)" | (*uncommentR?Structure_Bin-BEGIN*)(*(*uncommentR?Structure_Bin-END*)*)
(*(*uncommentL?Structure_Action_Structure-BEGIN*)*)(*uncommentL?Structure_Action_Structure-END*) "replace_SFAtprop_into_Structure sfa repl (Structure_Action_Structure oper ac struct) = Structure_Action_Structure oper ac (replace_SFAtprop_into_Structure sfa repl struct)" | (*uncommentR?Structure_Action_Structure-BEGIN*)(*(*uncommentR?Structure_Action_Structure-END*)*)
(*(*uncommentL?Structure_Agent_Structure-BEGIN*)*)(*uncommentL?Structure_Agent_Structure-END*) "replace_SFAtprop_into_Structure sfa repl (Structure_Agent_Structure oper ag struct) = Structure_Agent_Structure oper ag (replace_SFAtprop_into_Structure sfa repl struct)" | (*uncommentR?Structure_Agent_Structure-BEGIN*)(*(*uncommentR?Structure_Agent_Structure-END*)*)
"replace_SFAtprop_into_Structure sfa repl s = (if sfa = s then repl else s)"


fun replace_SFAtprop_into_Sequent :: "Structure \<Rightarrow> Structure \<Rightarrow> Sequent \<Rightarrow> Sequent" where
"replace_SFAtprop_into_Sequent sfa repl (Sequent l r) = Sequent (replace_SFAtprop_into_Structure sfa repl l) (replace_SFAtprop_into_Structure sfa repl r)" |
"replace_SFAtprop_into_Sequent sfa relp x = x"

fun replace_SFAtprop_into_PT :: "Structure \<Rightarrow> Structure \<Rightarrow> Prooftree \<Rightarrow> Prooftree" where
"replace_SFAtprop_into_PT sfa repl (Prooftree s r list) = (Prooftree (replace_SFAtprop_into_Sequent sfa repl s) r (map (replace_SFAtprop_into_PT sfa repl) list))"


fun sequent_fresh_name :: "Sequent \<Rightarrow> Structure" where
"sequent_fresh_name (Sequent l r) = (Structure_Formula (Formula_Atprop (Atprop (fresh_name ((collect_SFAtprop_names l)@(collect_SFAtprop_names r)) ))))" |
"sequent_fresh_name _ = (Structure_Formula (Formula_Atprop (Atprop ''X'')))"



export_code open der isProofTree ruleList displayRules ant consq rulifyProoftree replaceIntoPT isProofTreeWithCut 
expandProoftree polarity_Sequent position_in_Sequent partial_goal partial_goal_complement sequent_fresh_name replace_SFAtprop_into_PT in Scala
module_name (*calc_name-BEGIN*)DEAK(*calc_name-END*) file (*export_path-BEGIN*)"../scala/DEAK.scala"(*export_path-END*)
end