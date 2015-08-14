theory (*calc_name_core_se-BEGIN*)DEAK_Core_SE(*calc_name_core_se-END*)
imports Main
begin

(*calc_structure_se-BEGIN*)
type_synonym Action = string

type_synonym Agent = string

type_synonym Atprop = string

datatype Formula = Formula_FboxA Action Formula ("fboxA\<^sub>F _ _" [330,330] 331)
                 | Formula_FdiamA Action Formula ("fdiamA\<^sub>F _ _" [330,330] 331)
                 | Formula_BboxA Action Formula ("bboxA\<^sub>F _ _" [330,330] 331)
                 | Formula_BdiamA Action Formula ("bdiamA\<^sub>F _ _" [330,330] 331)
                 | Formula_FboxK Agent Formula ("fboxK\<^sub>F _ _" [330,330] 331)
                 | Formula_FdiamK Agent Formula ("fdiamK\<^sub>F _ _" [330,330] 331)
                 | Formula_BboxK Agent Formula ("bboxK\<^sub>F _ _" [330,330] 331)
                 | Formula_BdiamK Agent Formula ("bdiamK\<^sub>F _ _" [330,330] 331)
                 | Formula_Atprop Atprop ("_ \<^sub>F" [320] 330)
                 | Formula_And Formula Formula (infix "\<and>\<^sub>F" 330)
                 | Formula_ImpL Formula Formula (infix "\<leftarrow>\<^sub>F" 330)
                 | Formula_DImpL Formula Formula (infix "-<\<^sub>F" 330)
                 | Formula_DImpR Formula Formula (infix ">-\<^sub>F" 330)
                 | Formula_Or Formula Formula (infix "\<or>\<^sub>F" 330)
                 | Formula_ImpR Formula Formula (infix "\<rightarrow>\<^sub>F" 330)
                 | Formula_Precondition Action ("One\<^sub>F _" [340] 330)
                 | Formula_Top ("\<top>\<^sub>F")
                 | Formula_Bot ("\<bottom>\<^sub>F")

datatype Structure = Structure_ForwA Action Structure ("forwA\<^sub>S _ _" [330,330] 331)
                   | Structure_BackA Action Structure ("backA\<^sub>S _ _" [330,330] 331)
                   | Structure_BackK Agent Structure ("backK\<^sub>S _ _" [330,330] 331)
                   | Structure_ForwK Agent Structure ("forwK\<^sub>S _ _" [330,330] 331)
                   | Structure_Bigcomma "Structure list" (";;\<^sub>S _" [330] 331)
                   | Structure_Comma Structure Structure (infix ";\<^sub>S" 340)
                   | Structure_ImpL Structure Structure (infix "\<leftarrow>\<^sub>S" 340)
                   | Structure_ImpR Structure Structure (infix "\<rightarrow>\<^sub>S" 340)
                   | Structure_Formula Formula ("_ \<^sub>S" [330] 340)
                   | Structure_Phi Action ("Phi\<^sub>S _" [340] 330)
                   | Structure_Neutral ("I\<^sub>S")

datatype Sequent = Sequent Structure Structure ("_ \<turnstile>\<^sub>S _" [311,311] 310)
(*calc_structure_se-END*)


end