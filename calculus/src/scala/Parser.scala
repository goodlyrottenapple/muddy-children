import scala.util.parsing.combinator._
import scala.util.parsing.json._
/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/

object Parser extends JavaTokenParsers with OperatorPrecedenceParsers {

	lazy val stringParser:PackratParser[List[Char]] = 
		ident ^^ { i => i.toList }


	def listParser[T](innerParser:PackratParser[T]):PackratParser[List[T]] =
		"[" ~ "]" ^^ { _ => List[T]() } |
		"[" ~> rep(innerParser <~ ",") ~ innerParser <~ "]" ^^ { case list ~ last => list ++ List[T](last) }

/*/*uncommentL?Structure-BEGIN*/*//*uncommentL?Structure-END*/
	lazy val structure_listParser:PackratParser[List[Structure]] = listParser[Structure](structureParser)
/*uncommentR?Structure-BEGIN*//*/*uncommentR?Structure-END*/*/

/*parser_calc_structure-BEGIN*/
	lazy val actionParser : PackratParser[Action] = 
		action_freevarParser | actionaParser | "(" ~> actionParser <~ ")"

	lazy val actionaParser : PackratParser[Action] =
		stringParser ^^ { case a => Actiona(a) }

	lazy val action_freevarParser : PackratParser[Action] =
		"Act?" ~ stringParser ^^ { case "Act?" ~ a => Action_Freevar(a) }

	def parseAction(s:String) : Option[Action] = parseAll(actionParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val agentParser : PackratParser[Agent] = 
		agent_freevarParser | agentaParser | "(" ~> agentParser <~ ")"

	lazy val agent_freevarParser : PackratParser[Agent] =
		"Ag?" ~ stringParser ^^ { case "Ag?" ~ a => Agent_Freevar(a) }

	lazy val agentaParser : PackratParser[Agent] =
		stringParser ^^ { case a => Agenta(a) }

	def parseAgent(s:String) : Option[Agent] = parseAll(agentParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val atpropParser : PackratParser[Atprop] = 
		atprop_freevarParser | atpropaParser | "(" ~> atpropParser <~ ")"

	lazy val atprop_freevarParser : PackratParser[Atprop] =
		"A?" ~ stringParser ^^ { case "A?" ~ a => Atprop_Freevar(a) }

	lazy val atpropaParser : PackratParser[Atprop] =
		stringParser ^^ { case a => Atpropa(a) }

	def parseAtprop(s:String) : Option[Atprop] = parseAll(atpropParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}





	lazy val formulaParser:PackratParser[Formula] = operators[Any,Formula](
		Prefix(200)(formula_fboxaParser~actionParser) { case (_~a, b) => Formula_Action_Formula(Formula_FboxA(),a, b) },
		Prefix(200)(formula_fdiamaParser~actionParser) { case (_~a, b) => Formula_Action_Formula(Formula_FdiamA(),a, b) },
		Prefix(200)(formula_bboxaParser~actionParser) { case (_~a, b) => Formula_Action_Formula(Formula_BboxA(),a, b) },
		Prefix(200)(formula_bdiamaParser~actionParser) { case (_~a, b) => Formula_Action_Formula(Formula_BdiamA(),a, b) },
		Prefix(200)(formula_fboxkParser~agentParser) { case (_~a, b) => Formula_Agent_Formula(Formula_FboxK(),a, b) },
		Prefix(200)(formula_fdiamkParser~agentParser) { case (_~a, b) => Formula_Agent_Formula(Formula_FdiamK(),a, b) },
		Prefix(200)(formula_bboxkParser~agentParser) { case (_~a, b) => Formula_Agent_Formula(Formula_BboxK(),a, b) },
		Prefix(200)(formula_bdiamkParser~agentParser) { case (_~a, b) => Formula_Agent_Formula(Formula_BdiamK(),a, b) },
		Infix(400, 401)(formula_andParser) { (_, a, b) => Formula_Bin(a, Formula_And(), b ) },
		Infix(500, 501)(formula_implParser) { (_, a, b) => Formula_Bin(a, Formula_ImpL(), b ) },
		Infix(500, 501)(formula_dimplParser) { (_, a, b) => Formula_Bin(a, Formula_DImpL(), b ) },
		Infix(500, 501)(formula_dimprParser) { (_, a, b) => Formula_Bin(a, Formula_DImpR(), b ) },
		Infix(400, 401)(formula_orParser) { (_, a, b) => Formula_Bin(a, Formula_Or(), b ) },
		Infix(500, 501)(formula_imprParser) { (_, a, b) => Formula_Bin(a, Formula_ImpR(), b ) }
	) ( formula_freevarParser | formula_zerParser | formula_preconditionParser | formula_atpropParser | "(" ~> formulaParser <~ ")" )

	def parseFormula(s:String) : Option[Formula] = parseAll(formulaParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}

	lazy val formula_action_formulaParser : PackratParser[Formula] =
		formula_action_formula_opParser ~ actionParser ~ formulaParser ^^ { case a ~ b ~ c => Formula_Action_Formula(a, b, c) }

	lazy val formula_agent_formulaParser : PackratParser[Formula] =
		formula_agent_formula_opParser ~ agentParser ~ formulaParser ^^ { case a ~ b ~ c => Formula_Agent_Formula(a, b, c) }

	lazy val formula_binParser : PackratParser[Formula] =
		formulaParser ~ formula_bin_opParser ~ formulaParser ^^ { case a ~ b ~ c => Formula_Bin(a, b, c) }

	lazy val formula_zerParser : PackratParser[Formula] =
		formula_zer_opParser ^^ { case a => Formula_Zer(a) }

	lazy val formula_preconditionParser : PackratParser[Formula] =
		"One" ~ actionParser ^^ { case "One" ~ a => Formula_Precondition(a) }

	lazy val formula_freevarParser : PackratParser[Formula] =
		"F?" ~ stringParser ^^ { case "F?" ~ a => Formula_Freevar(a) }

	lazy val formula_atpropParser : PackratParser[Formula] =
		atpropParser ^^ { case a => Formula_Atprop(a) }



	lazy val formula_action_formula_opParser : PackratParser[Formula_Action_Formula_Op] = 
		formula_fboxaParser | formula_fdiamaParser | formula_bboxaParser | formula_bdiamaParser | "(" ~> formula_action_formula_opParser <~ ")"

	lazy val formula_fboxaParser : PackratParser[Formula_Action_Formula_Op] =
		"fboxA" ^^ { _ => Formula_FboxA() }

	lazy val formula_fdiamaParser : PackratParser[Formula_Action_Formula_Op] =
		"fdiamA" ^^ { _ => Formula_FdiamA() }

	lazy val formula_bboxaParser : PackratParser[Formula_Action_Formula_Op] =
		"bboxA" ^^ { _ => Formula_BboxA() }

	lazy val formula_bdiamaParser : PackratParser[Formula_Action_Formula_Op] =
		"bdiamA" ^^ { _ => Formula_BdiamA() }

	def parseFormula_Action_Formula_Op(s:String) : Option[Formula_Action_Formula_Op] = parseAll(formula_action_formula_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val formula_agent_formula_opParser : PackratParser[Formula_Agent_Formula_Op] = 
		formula_fboxkParser | formula_fdiamkParser | formula_bboxkParser | formula_bdiamkParser | "(" ~> formula_agent_formula_opParser <~ ")"

	lazy val formula_fboxkParser : PackratParser[Formula_Agent_Formula_Op] =
		"fboxK" ^^ { _ => Formula_FboxK() }

	lazy val formula_fdiamkParser : PackratParser[Formula_Agent_Formula_Op] =
		"fdiamK" ^^ { _ => Formula_FdiamK() }

	lazy val formula_bboxkParser : PackratParser[Formula_Agent_Formula_Op] =
		"bboxK" ^^ { _ => Formula_BboxK() }

	lazy val formula_bdiamkParser : PackratParser[Formula_Agent_Formula_Op] =
		"bdiamK" ^^ { _ => Formula_BdiamK() }

	def parseFormula_Agent_Formula_Op(s:String) : Option[Formula_Agent_Formula_Op] = parseAll(formula_agent_formula_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val formula_bin_opParser : PackratParser[Formula_Bin_Op] = 
		formula_andParser | formula_implParser | formula_dimplParser | formula_dimprParser | formula_orParser | formula_imprParser | "(" ~> formula_bin_opParser <~ ")"

	lazy val formula_andParser : PackratParser[Formula_Bin_Op] =
		"/\\" ^^ { _ => Formula_And() }

	lazy val formula_implParser : PackratParser[Formula_Bin_Op] =
		"<"~not("<") ^^ { _ => Formula_ImpL() }

	lazy val formula_dimplParser : PackratParser[Formula_Bin_Op] =
		"-<" ^^ { _ => Formula_DImpL() }

	lazy val formula_dimprParser : PackratParser[Formula_Bin_Op] =
		">-" ^^ { _ => Formula_DImpR() }

	lazy val formula_orParser : PackratParser[Formula_Bin_Op] =
		"\\/" ^^ { _ => Formula_Or() }

	lazy val formula_imprParser : PackratParser[Formula_Bin_Op] =
		">"~not(">" | "-") ^^ { _ => Formula_ImpR() }

	def parseFormula_Bin_Op(s:String) : Option[Formula_Bin_Op] = parseAll(formula_bin_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val formula_zer_opParser : PackratParser[Formula_Zer_Op] = 
		formula_topParser | formula_botParser | "(" ~> formula_zer_opParser <~ ")"

	lazy val formula_topParser : PackratParser[Formula_Zer_Op] =
		"T" ^^ { _ => Formula_Top() }

	lazy val formula_botParser : PackratParser[Formula_Zer_Op] =
		"B" ^^ { _ => Formula_Bot() }

	def parseFormula_Zer_Op(s:String) : Option[Formula_Zer_Op] = parseAll(formula_zer_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val sequentParser : PackratParser[Sequent] = 
		sequentaParser | "(" ~> sequentParser <~ ")"

	lazy val sequentaParser : PackratParser[Sequent] =
		structureParser ~ "|-" ~ structureParser ^^ { case a ~ "|-" ~ b => Sequenta(a, b) }

	def parseSequent(s:String) : Option[Sequent] = parseAll(sequentParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}





	lazy val structureParser:PackratParser[Structure] = operators[Any,Structure](
		Prefix(200)(structure_backkParser~agentParser) { case (_~a, b) => Structure_Agent_Structure(Structure_BackK(),a, b) },
		Prefix(200)(structure_forwkParser~agentParser) { case (_~a, b) => Structure_Agent_Structure(Structure_ForwK(),a, b) },
		Prefix(200)(structure_forwaParser~actionParser) { case (_~a, b) => Structure_Action_Structure(Structure_ForwA(),a, b) },
		Prefix(200)(structure_backaParser~actionParser) { case (_~a, b) => Structure_Action_Structure(Structure_BackA(),a, b) },
		Infix(400, 401)(structure_commaParser) { (_, a, b) => Structure_Bin(a, Structure_Comma(), b ) },
		Infix(500, 501)(structure_implParser) { (_, a, b) => Structure_Bin(a, Structure_ImpL(), b ) },
		Infix(500, 501)(structure_imprParser) { (_, a, b) => Structure_Bin(a, Structure_ImpR(), b ) }
	) ( structure_bigcommaParser | structure_freevarParser | structure_zerParser | structure_phiParser | structure_formulaParser | "(" ~> structureParser <~ ")" )

	def parseStructure(s:String) : Option[Structure] = parseAll(structureParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}

	lazy val structure_bigcommaParser : PackratParser[Structure] =
		";;" ~ structure_listParser ^^ { case ";;" ~ a => Structure_Bigcomma(a) }

	lazy val structure_binParser : PackratParser[Structure] =
		structureParser ~ structure_bin_opParser ~ structureParser ^^ { case a ~ b ~ c => Structure_Bin(a, b, c) }

	lazy val structure_agent_structureParser : PackratParser[Structure] =
		structure_agent_structure_opParser ~ agentParser ~ structureParser ^^ { case a ~ b ~ c => Structure_Agent_Structure(a, b, c) }

	lazy val structure_formulaParser : PackratParser[Structure] =
		formulaParser ^^ { case a => Structure_Formula(a) }

	lazy val structure_phiParser : PackratParser[Structure] =
		"Phi" ~ actionParser ^^ { case "Phi" ~ a => Structure_Phi(a) }

	lazy val structure_zerParser : PackratParser[Structure] =
		structure_zer_opParser ^^ { case a => Structure_Zer(a) }

	lazy val structure_action_structureParser : PackratParser[Structure] =
		structure_action_structure_opParser ~ actionParser ~ structureParser ^^ { case a ~ b ~ c => Structure_Action_Structure(a, b, c) }

	lazy val structure_freevarParser : PackratParser[Structure] =
		"?" ~ stringParser ^^ { case "?" ~ a => Structure_Freevar(a) }



	lazy val structure_action_structure_opParser : PackratParser[Structure_Action_Structure_Op] = 
		structure_forwaParser | structure_backaParser | "(" ~> structure_action_structure_opParser <~ ")"

	lazy val structure_forwaParser : PackratParser[Structure_Action_Structure_Op] =
		"forwA" ^^ { _ => Structure_ForwA() }

	lazy val structure_backaParser : PackratParser[Structure_Action_Structure_Op] =
		"backA" ^^ { _ => Structure_BackA() }

	def parseStructure_Action_Structure_Op(s:String) : Option[Structure_Action_Structure_Op] = parseAll(structure_action_structure_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val structure_agent_structure_opParser : PackratParser[Structure_Agent_Structure_Op] = 
		structure_backkParser | structure_forwkParser | "(" ~> structure_agent_structure_opParser <~ ")"

	lazy val structure_backkParser : PackratParser[Structure_Agent_Structure_Op] =
		"backK" ^^ { _ => Structure_BackK() }

	lazy val structure_forwkParser : PackratParser[Structure_Agent_Structure_Op] =
		"forwK" ^^ { _ => Structure_ForwK() }

	def parseStructure_Agent_Structure_Op(s:String) : Option[Structure_Agent_Structure_Op] = parseAll(structure_agent_structure_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val structure_bin_opParser : PackratParser[Structure_Bin_Op] = 
		structure_commaParser | structure_implParser | structure_imprParser | "(" ~> structure_bin_opParser <~ ")"

	lazy val structure_commaParser : PackratParser[Structure_Bin_Op] =
		";"~not(";") ^^ { _ => Structure_Comma() }

	lazy val structure_implParser : PackratParser[Structure_Bin_Op] =
		"<<" ^^ { _ => Structure_ImpL() }

	lazy val structure_imprParser : PackratParser[Structure_Bin_Op] =
		">>" ^^ { _ => Structure_ImpR() }

	def parseStructure_Bin_Op(s:String) : Option[Structure_Bin_Op] = parseAll(structure_bin_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val structure_zer_opParser : PackratParser[Structure_Zer_Op] = 
		structure_neutralParser | "(" ~> structure_zer_opParser <~ ")"

	lazy val structure_neutralParser : PackratParser[Structure_Zer_Op] =
		"I" ^^ { _ => Structure_Neutral() }

	def parseStructure_Zer_Op(s:String) : Option[Structure_Zer_Op] = parseAll(structure_zer_opParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}
/*parser_calc_structure-END*/

/*parser_calc_structure_rules-BEGIN*/
	lazy val rulebigcommaParser : PackratParser[RuleBigcomma] = 
		bigcomma_nil_r2Parser | bigcomma_nil_rParser | bigcomma_nil_l2Parser | bigcomma_nil_lParser | bigcomma_cons_r2Parser | bigcomma_cons_rParser | bigcomma_cons_l2Parser | bigcomma_cons_lParser | "(" ~> rulebigcommaParser <~ ")"

	lazy val bigcomma_nil_rParser : PackratParser[RuleBigcomma] =
		"Bigcomma_Nil_R" ^^ { _ => Bigcomma_Nil_R() }

	lazy val bigcomma_cons_rParser : PackratParser[RuleBigcomma] =
		"Bigcomma_Cons_R" ^^ { _ => Bigcomma_Cons_R() }

	lazy val bigcomma_cons_l2Parser : PackratParser[RuleBigcomma] =
		"Bigcomma_Cons_L2" ^^ { _ => Bigcomma_Cons_L2() }

	lazy val bigcomma_nil_l2Parser : PackratParser[RuleBigcomma] =
		"Bigcomma_Nil_L2" ^^ { _ => Bigcomma_Nil_L2() }

	lazy val bigcomma_cons_r2Parser : PackratParser[RuleBigcomma] =
		"Bigcomma_Cons_R2" ^^ { _ => Bigcomma_Cons_R2() }

	lazy val bigcomma_cons_lParser : PackratParser[RuleBigcomma] =
		"Bigcomma_Cons_L" ^^ { _ => Bigcomma_Cons_L() }

	lazy val bigcomma_nil_r2Parser : PackratParser[RuleBigcomma] =
		"Bigcomma_Nil_R2" ^^ { _ => Bigcomma_Nil_R2() }

	lazy val bigcomma_nil_lParser : PackratParser[RuleBigcomma] =
		"Bigcomma_Nil_L" ^^ { _ => Bigcomma_Nil_L() }

	def parseRuleBigcomma(s:String) : Option[RuleBigcomma] = parseAll(rulebigcommaParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulecutParser : PackratParser[RuleCut] = 
		singlecutParser | "(" ~> rulecutParser <~ ")"

	lazy val singlecutParser : PackratParser[RuleCut] =
		"Cut" ^^ { _ => SingleCut() }

	def parseRuleCut(s:String) : Option[RuleCut] = parseAll(rulecutParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruledispParser : PackratParser[RuleDisp] = 
		impr_comma_disp2Parser | impr_comma_dispParser | impl_comma_disp2Parser | impl_comma_dispParser | comma_impr_disp2Parser | comma_impr_dispParser | comma_impl_disp2Parser | comma_impl_dispParser | "(" ~> ruledispParser <~ ")"

	lazy val comma_impl_dispParser : PackratParser[RuleDisp] =
		"Comma_impL_disp" ^^ { _ => Comma_impL_disp() }

	lazy val comma_impr_disp2Parser : PackratParser[RuleDisp] =
		"Comma_impR_disp2" ^^ { _ => Comma_impR_disp2() }

	lazy val impl_comma_disp2Parser : PackratParser[RuleDisp] =
		"ImpL_comma_disp2" ^^ { _ => ImpL_comma_disp2() }

	lazy val impr_comma_disp2Parser : PackratParser[RuleDisp] =
		"ImpR_comma_disp2" ^^ { _ => ImpR_comma_disp2() }

	lazy val impr_comma_dispParser : PackratParser[RuleDisp] =
		"ImpR_comma_disp" ^^ { _ => ImpR_comma_disp() }

	lazy val impl_comma_dispParser : PackratParser[RuleDisp] =
		"ImpL_comma_disp" ^^ { _ => ImpL_comma_disp() }

	lazy val comma_impr_dispParser : PackratParser[RuleDisp] =
		"Comma_impR_disp" ^^ { _ => Comma_impR_disp() }

	lazy val comma_impl_disp2Parser : PackratParser[RuleDisp] =
		"Comma_impL_disp2" ^^ { _ => Comma_impL_disp2() }

	def parseRuleDisp(s:String) : Option[RuleDisp] = parseAll(ruledispParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruledispactParser : PackratParser[RuleDispAct] = 
		forw_back_a2Parser | forw_back_aParser | back_forw_a2Parser | back_forw_aParser | "(" ~> ruledispactParser <~ ")"

	lazy val back_forw_aParser : PackratParser[RuleDispAct] =
		"Back_forw_A" ^^ { _ => Back_forw_A() }

	lazy val forw_back_a2Parser : PackratParser[RuleDispAct] =
		"Forw_back_A2" ^^ { _ => Forw_back_A2() }

	lazy val forw_back_aParser : PackratParser[RuleDispAct] =
		"Forw_back_A" ^^ { _ => Forw_back_A() }

	lazy val back_forw_a2Parser : PackratParser[RuleDispAct] =
		"Back_forw_A2" ^^ { _ => Back_forw_A2() }

	def parseRuleDispAct(s:String) : Option[RuleDispAct] = parseAll(ruledispactParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruledispkParser : PackratParser[RuleDispK] = 
		forw_back_k2Parser | forw_back_kParser | back_forw_k2Parser | back_forw_kParser | "(" ~> ruledispkParser <~ ")"

	lazy val back_forw_k2Parser : PackratParser[RuleDispK] =
		"Back_forw_K2" ^^ { _ => Back_forw_K2() }

	lazy val back_forw_kParser : PackratParser[RuleDispK] =
		"Back_forw_K" ^^ { _ => Back_forw_K() }

	lazy val forw_back_k2Parser : PackratParser[RuleDispK] =
		"Forw_back_K2" ^^ { _ => Forw_back_K2() }

	lazy val forw_back_kParser : PackratParser[RuleDispK] =
		"Forw_back_K" ^^ { _ => Forw_back_K() }

	def parseRuleDispK(s:String) : Option[RuleDispK] = parseAll(ruledispkParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulegrishParser : PackratParser[RuleGrish] = 
		grishin_r2Parser | grishin_rParser | grishin_l2Parser | grishin_lParser | "(" ~> rulegrishParser <~ ")"

	lazy val grishin_r2Parser : PackratParser[RuleGrish] =
		"Grishin_R2" ^^ { _ => Grishin_R2() }

	lazy val grishin_rParser : PackratParser[RuleGrish] =
		"Grishin_R" ^^ { _ => Grishin_R() }

	lazy val grishin_lParser : PackratParser[RuleGrish] =
		"Grishin_L" ^^ { _ => Grishin_L() }

	lazy val grishin_l2Parser : PackratParser[RuleGrish] =
		"Grishin_L2" ^^ { _ => Grishin_L2() }

	def parseRuleGrish(s:String) : Option[RuleGrish] = parseAll(rulegrishParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleknowledgeParser : PackratParser[RuleKnowledge] = 
		refl_forwkParser | "(" ~> ruleknowledgeParser <~ ")"

	lazy val refl_forwkParser : PackratParser[RuleKnowledge] =
		"Refl_ForwK" ^^ { _ => Refl_ForwK() }

	def parseRuleKnowledge(s:String) : Option[RuleKnowledge] = parseAll(ruleknowledgeParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleopParser : PackratParser[RuleOp] = 
		top_rParser | top_lParser | or_rParser | or_lParser | impr_rParser | impr_lParser | impl_rParser | impl_lParser | dimpr_rParser | dimpr_lParser | dimpl_rParser | dimpl_lParser | bot_rParser | bot_lParser | and_rParser | and_lParser | "(" ~> ruleopParser <~ ")"

	lazy val bot_rParser : PackratParser[RuleOp] =
		"Bot_R" ^^ { _ => Bot_R() }

	lazy val top_lParser : PackratParser[RuleOp] =
		"Top_L" ^^ { _ => Top_L() }

	lazy val dimpr_lParser : PackratParser[RuleOp] =
		"DImpR_L" ^^ { _ => DImpR_L() }

	lazy val impl_rParser : PackratParser[RuleOp] =
		"ImpL_R" ^^ { _ => ImpL_R() }

	lazy val dimpl_rParser : PackratParser[RuleOp] =
		"DImpL_R" ^^ { _ => DImpL_R() }

	lazy val and_lParser : PackratParser[RuleOp] =
		"And_L" ^^ { _ => And_L() }

	lazy val impr_rParser : PackratParser[RuleOp] =
		"ImpR_R" ^^ { _ => ImpR_R() }

	lazy val or_lParser : PackratParser[RuleOp] =
		"Or_L" ^^ { _ => Or_L() }

	lazy val or_rParser : PackratParser[RuleOp] =
		"Or_R" ^^ { _ => Or_R() }

	lazy val impr_lParser : PackratParser[RuleOp] =
		"ImpR_L" ^^ { _ => ImpR_L() }

	lazy val dimpl_lParser : PackratParser[RuleOp] =
		"DImpL_L" ^^ { _ => DImpL_L() }

	lazy val and_rParser : PackratParser[RuleOp] =
		"And_R" ^^ { _ => And_R() }

	lazy val dimpr_rParser : PackratParser[RuleOp] =
		"DImpR_R" ^^ { _ => DImpR_R() }

	lazy val impl_lParser : PackratParser[RuleOp] =
		"ImpL_L" ^^ { _ => ImpL_L() }

	lazy val top_rParser : PackratParser[RuleOp] =
		"Top_R" ^^ { _ => Top_R() }

	lazy val bot_lParser : PackratParser[RuleOp] =
		"Bot_L" ^^ { _ => Bot_L() }

	def parseRuleOp(s:String) : Option[RuleOp] = parseAll(ruleopParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleopactParser : PackratParser[RuleOpAct] = 
		pre_rParser | pre_lParser | one_rParser | one_lParser | fdiama_rParser | fdiama_lParser | fboxa_rParser | fboxa_lParser | bdiama_rParser | bdiama_lParser | bboxa_rParser | bboxa_lParser | "(" ~> ruleopactParser <~ ")"

	lazy val fdiama_lParser : PackratParser[RuleOpAct] =
		"FdiamA_L" ^^ { _ => FdiamA_L() }

	lazy val one_rParser : PackratParser[RuleOpAct] =
		"One_R" ^^ { _ => One_R() }

	lazy val bdiama_rParser : PackratParser[RuleOpAct] =
		"BdiamA_R" ^^ { _ => BdiamA_R() }

	lazy val fboxa_rParser : PackratParser[RuleOpAct] =
		"FboxA_R" ^^ { _ => FboxA_R() }

	lazy val pre_lParser : PackratParser[RuleOpAct] =
		"Pre_L" ^^ { _ => Pre_L() }

	lazy val bboxa_rParser : PackratParser[RuleOpAct] =
		"BboxA_R" ^^ { _ => BboxA_R() }

	lazy val bboxa_lParser : PackratParser[RuleOpAct] =
		"BboxA_L" ^^ { _ => BboxA_L() }

	lazy val fboxa_lParser : PackratParser[RuleOpAct] =
		"FboxA_L" ^^ { _ => FboxA_L() }

	lazy val pre_rParser : PackratParser[RuleOpAct] =
		"Pre_R" ^^ { _ => Pre_R() }

	lazy val bdiama_lParser : PackratParser[RuleOpAct] =
		"BdiamA_L" ^^ { _ => BdiamA_L() }

	lazy val one_lParser : PackratParser[RuleOpAct] =
		"One_L" ^^ { _ => One_L() }

	lazy val fdiama_rParser : PackratParser[RuleOpAct] =
		"FdiamA_R" ^^ { _ => FdiamA_R() }

	def parseRuleOpAct(s:String) : Option[RuleOpAct] = parseAll(ruleopactParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleopkParser : PackratParser[RuleOpK] = 
		fdiamk_rParser | fdiamk_lParser | fboxk_rParser | fboxk_lParser | bdiamk_rParser | bdiamk_lParser | bboxk_rParser | bboxk_lParser | "(" ~> ruleopkParser <~ ")"

	lazy val bdiamk_lParser : PackratParser[RuleOpK] =
		"BdiamK_L" ^^ { _ => BdiamK_L() }

	lazy val fdiamk_rParser : PackratParser[RuleOpK] =
		"FdiamK_R" ^^ { _ => FdiamK_R() }

	lazy val fboxk_rParser : PackratParser[RuleOpK] =
		"FboxK_R" ^^ { _ => FboxK_R() }

	lazy val bboxk_lParser : PackratParser[RuleOpK] =
		"BboxK_L" ^^ { _ => BboxK_L() }

	lazy val bboxk_rParser : PackratParser[RuleOpK] =
		"BboxK_R" ^^ { _ => BboxK_R() }

	lazy val fboxk_lParser : PackratParser[RuleOpK] =
		"FboxK_L" ^^ { _ => FboxK_L() }

	lazy val fdiamk_lParser : PackratParser[RuleOpK] =
		"FdiamK_L" ^^ { _ => FdiamK_L() }

	lazy val bdiamk_rParser : PackratParser[RuleOpK] =
		"BdiamK_R" ^^ { _ => BdiamK_R() }

	def parseRuleOpK(s:String) : Option[RuleOpK] = parseAll(ruleopkParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulestructParser : PackratParser[RuleStruct] = 
		w_impr_rParser | w_impr_lParser | w_impl_rParser | w_impl_lParser | impr_i2Parser | impr_iParser | impl_i2Parser | impl_iParser | i_impr2Parser | i_imprParser | i_impl2Parser | i_implParser | iw_rParser | iw_lParser | e_rParser | e_lParser | c_rParser | c_lParser | a_r2Parser | a_rParser | a_l2Parser | a_lParser | "(" ~> rulestructParser <~ ")"

	lazy val w_impl_rParser : PackratParser[RuleStruct] =
		"W_impL_R" ^^ { _ => W_impL_R() }

	lazy val impl_iParser : PackratParser[RuleStruct] =
		"ImpL_I" ^^ { _ => ImpL_I() }

	lazy val w_impl_lParser : PackratParser[RuleStruct] =
		"W_impL_L" ^^ { _ => W_impL_L() }

	lazy val impr_i2Parser : PackratParser[RuleStruct] =
		"ImpR_I2" ^^ { _ => ImpR_I2() }

	lazy val e_rParser : PackratParser[RuleStruct] =
		"E_R" ^^ { _ => E_R() }

	lazy val iw_rParser : PackratParser[RuleStruct] =
		"IW_R" ^^ { _ => IW_R() }

	lazy val iw_lParser : PackratParser[RuleStruct] =
		"IW_L" ^^ { _ => IW_L() }

	lazy val a_l2Parser : PackratParser[RuleStruct] =
		"A_L2" ^^ { _ => A_L2() }

	lazy val e_lParser : PackratParser[RuleStruct] =
		"E_L" ^^ { _ => E_L() }

	lazy val a_rParser : PackratParser[RuleStruct] =
		"A_R" ^^ { _ => A_R() }

	lazy val w_impr_rParser : PackratParser[RuleStruct] =
		"W_impR_R" ^^ { _ => W_impR_R() }

	lazy val c_lParser : PackratParser[RuleStruct] =
		"C_L" ^^ { _ => C_L() }

	lazy val c_rParser : PackratParser[RuleStruct] =
		"C_R" ^^ { _ => C_R() }

	lazy val impr_iParser : PackratParser[RuleStruct] =
		"ImpR_I" ^^ { _ => ImpR_I() }

	lazy val w_impr_lParser : PackratParser[RuleStruct] =
		"W_impR_L" ^^ { _ => W_impR_L() }

	lazy val a_lParser : PackratParser[RuleStruct] =
		"A_L" ^^ { _ => A_L() }

	lazy val a_r2Parser : PackratParser[RuleStruct] =
		"A_R2" ^^ { _ => A_R2() }

	lazy val i_impr2Parser : PackratParser[RuleStruct] =
		"I_impR2" ^^ { _ => I_impR2() }

	lazy val i_implParser : PackratParser[RuleStruct] =
		"I_impL" ^^ { _ => I_impL() }

	lazy val i_imprParser : PackratParser[RuleStruct] =
		"I_impR" ^^ { _ => I_impR() }

	lazy val impl_i2Parser : PackratParser[RuleStruct] =
		"ImpL_I2" ^^ { _ => ImpL_I2() }

	lazy val i_impl2Parser : PackratParser[RuleStruct] =
		"I_impL2" ^^ { _ => I_impL2() }

	def parseRuleStruct(s:String) : Option[RuleStruct] = parseAll(rulestructParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulestructactParser : PackratParser[RuleStructAct] = 
		nec_a_rParser | nec_a_lParser | mon_a_rParser | mon_a_lParser | fs_a_rParser | fs_a_lParser | a_nec_rParser | a_nec_lParser | a_mon_rParser | a_mon_lParser | a_fs_rParser | a_fs_lParser | "(" ~> rulestructactParser <~ ")"

	lazy val a_nec_lParser : PackratParser[RuleStructAct] =
		"A_nec_L" ^^ { _ => A_nec_L() }

	lazy val a_mon_lParser : PackratParser[RuleStructAct] =
		"A_mon_L" ^^ { _ => A_mon_L() }

	lazy val mon_a_rParser : PackratParser[RuleStructAct] =
		"Mon_A_R" ^^ { _ => Mon_A_R() }

	lazy val nec_a_lParser : PackratParser[RuleStructAct] =
		"Nec_A_L" ^^ { _ => Nec_A_L() }

	lazy val fs_a_lParser : PackratParser[RuleStructAct] =
		"FS_A_L" ^^ { _ => FS_A_L() }

	lazy val fs_a_rParser : PackratParser[RuleStructAct] =
		"FS_A_R" ^^ { _ => FS_A_R() }

	lazy val a_mon_rParser : PackratParser[RuleStructAct] =
		"A_mon_R" ^^ { _ => A_mon_R() }

	lazy val a_fs_rParser : PackratParser[RuleStructAct] =
		"A_FS_R" ^^ { _ => A_FS_R() }

	lazy val nec_a_rParser : PackratParser[RuleStructAct] =
		"Nec_A_R" ^^ { _ => Nec_A_R() }

	lazy val mon_a_lParser : PackratParser[RuleStructAct] =
		"Mon_A_L" ^^ { _ => Mon_A_L() }

	lazy val a_fs_lParser : PackratParser[RuleStructAct] =
		"A_FS_L" ^^ { _ => A_FS_L() }

	lazy val a_nec_rParser : PackratParser[RuleStructAct] =
		"A_nec_R" ^^ { _ => A_nec_R() }

	def parseRuleStructAct(s:String) : Option[RuleStructAct] = parseAll(rulestructactParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulestructeaParser : PackratParser[RuleStructEA] = 
		reduce_rParser | reduce_lParser | compa_rParser | compa_lParser | balanceParser | "(" ~> rulestructeaParser <~ ")"

	lazy val reduce_rParser : PackratParser[RuleStructEA] =
		"Reduce'R" ^^ { _ => Reduce_R() }

	lazy val compa_rParser : PackratParser[RuleStructEA] =
		"CompA_R" ^^ { _ => CompA_R() }

	lazy val balanceParser : PackratParser[RuleStructEA] =
		"Balance" ^^ { _ => Balance() }

	lazy val compa_lParser : PackratParser[RuleStructEA] =
		"CompA_L" ^^ { _ => CompA_L() }

	lazy val reduce_lParser : PackratParser[RuleStructEA] =
		"Reduce'L" ^^ { _ => Reduce_L() }

	def parseRuleStructEA(s:String) : Option[RuleStructEA] = parseAll(rulestructeaParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulestructkParser : PackratParser[RuleStructK] = 
		nec_k_rParser | nec_k_lParser | mon_k_rParser | mon_k_lParser | k_nec_rParser | k_nec_lParser | k_mon_rParser | k_mon_lParser | k_fs_rParser | k_fs_lParser | fs_k_rParser | fs_k_lParser | "(" ~> rulestructkParser <~ ")"

	lazy val k_nec_rParser : PackratParser[RuleStructK] =
		"K_nec_R" ^^ { _ => K_nec_R() }

	lazy val nec_k_lParser : PackratParser[RuleStructK] =
		"Nec_K_L" ^^ { _ => Nec_K_L() }

	lazy val k_mon_lParser : PackratParser[RuleStructK] =
		"K_mon_L" ^^ { _ => K_mon_L() }

	lazy val mon_k_lParser : PackratParser[RuleStructK] =
		"Mon_K_L" ^^ { _ => Mon_K_L() }

	lazy val fs_k_lParser : PackratParser[RuleStructK] =
		"FS_K_L" ^^ { _ => FS_K_L() }

	lazy val fs_k_rParser : PackratParser[RuleStructK] =
		"FS_K_R" ^^ { _ => FS_K_R() }

	lazy val mon_k_rParser : PackratParser[RuleStructK] =
		"Mon_K_R" ^^ { _ => Mon_K_R() }

	lazy val k_mon_rParser : PackratParser[RuleStructK] =
		"K_mon_R" ^^ { _ => K_mon_R() }

	lazy val k_fs_lParser : PackratParser[RuleStructK] =
		"K_FS_L" ^^ { _ => K_FS_L() }

	lazy val nec_k_rParser : PackratParser[RuleStructK] =
		"Nec_K_R" ^^ { _ => Nec_K_R() }

	lazy val k_fs_rParser : PackratParser[RuleStructK] =
		"K_FS_R" ^^ { _ => K_FS_R() }

	lazy val k_nec_lParser : PackratParser[RuleStructK] =
		"K_nec_L" ^^ { _ => K_nec_L() }

	def parseRuleStructK(s:String) : Option[RuleStructK] = parseAll(rulestructkParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleswapinParser : PackratParser[RuleSwapin] = 
		swapin_rParser | swapin_lParser | "(" ~> ruleswapinParser <~ ")"

	lazy val swapin_lParser : PackratParser[RuleSwapin] =
		"swapin'L" ^^ { _ => Swapin_L() }

	lazy val swapin_rParser : PackratParser[RuleSwapin] =
		"swapin'R" ^^ { _ => Swapin_R() }

	def parseRuleSwapin(s:String) : Option[RuleSwapin] = parseAll(ruleswapinParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleswapoutParser : PackratParser[RuleSwapout] = 
		swapout_rParser | swapout_lParser | "(" ~> ruleswapoutParser <~ ")"

	lazy val swapout_lParser : PackratParser[RuleSwapout] =
		"swapout'L" ^^ { _ => Swapout_L() }

	lazy val swapout_rParser : PackratParser[RuleSwapout] =
		"Swapout'R" ^^ { _ => Swapout_R() }

	def parseRuleSwapout(s:String) : Option[RuleSwapout] = parseAll(ruleswapoutParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val rulezerParser : PackratParser[RuleZer] = 
		premParser | partialParser | idParser | atomParser | "(" ~> rulezerParser <~ ")"

	lazy val premParser : PackratParser[RuleZer] =
		"Prem" ^^ { _ => Prem() }

	lazy val partialParser : PackratParser[RuleZer] =
		"Partial" ^^ { _ => Partial() }

	lazy val idParser : PackratParser[RuleZer] =
		"Id" ^^ { _ => Id() }

	lazy val atomParser : PackratParser[RuleZer] =
		"Atom" ^^ { _ => Atom() }

	def parseRuleZer(s:String) : Option[RuleZer] = parseAll(rulezerParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}



	lazy val ruleParser : PackratParser[Rule] =
		rulebigcommaParser ^^ { case a => RuleBigcommaa(a) } |
		rulecutParser ^^ { case a => RuleCuta(a) } |
		ruledispParser ^^ { case a => RuleDispa(a) } |
		ruledispactParser ^^ { case a => RuleDispActa(a) } |
		ruledispkParser ^^ { case a => RuleDispKa(a) } |
		rulegrishParser ^^ { case a => RuleGrisha(a) } |
		ruleknowledgeParser ^^ { case a => RuleKnowledgea(a) } |
		ruleopParser ^^ { case a => RuleOpa(a) } |
		ruleopactParser ^^ { case a => RuleOpActa(a) } |
		ruleopkParser ^^ { case a => RuleOpKa(a) } |
		rulestructParser ^^ { case a => RuleStructa(a) } |
		rulestructactParser ^^ { case a => RuleStructActa(a) } |
		rulestructeaParser ^^ { case a => RuleStructEAa(a) } |
		rulestructkParser ^^ { case a => RuleStructKa(a) } |
		ruleswapinParser ^^ { case a => RuleSwapina(a) } |
		ruleswapoutParser ^^ { case a => RuleSwapouta(a) } |
		rulezerParser ^^ { case a => RuleZera(a) } |
		"Macro" ~> stringParser ~ prooftreeParser ^^ { case a ~ pt => RuleMacro(a, pt) } |
		"Fail" ^^ { _ => Fail() }

	def parseRule(s:String) : Option[Rule] = parseAll(ruleParser,s) match {
		case Success(result, _) => Some(result)
		case failure : NoSuccess => None
	}
/*parser_calc_structure_rules-END*/


/*/*uncommentL?core_compiled-BEGIN*/*//*uncommentL?core_compiled-END*/
	def prooftreeListParser : Parser[List[Prooftree]] =
		"[" ~ "]" ^^ { _ => List[Prooftree]() } |
		"[" ~> rep(prooftreeParser <~ ",") ~ prooftreeParser <~ "]" ^^ { case list ~ last => list ++ List[Prooftree](last) }

	def prooftreeParser : Parser[Prooftree] =
		sequentParser ~ "<==" ~ "(" ~ ruleParser ~ ")" ~ prooftreeListParser ^^ { case a ~ "<==" ~ "(" ~ b ~ ")" ~ c => Prooftreea(a, b, c) } |
		"(" ~> sequentParser ~ "<==" ~ "(" ~ ruleParser ~ ")" ~ prooftreeListParser  <~ ")" ^^ { case a ~ "<==" ~ "(" ~ b ~ ")" ~ c => Prooftreea(a, b, c) }

	def parseProoftree(s:String) : Option[Prooftree] = parseAll(prooftreeParser,s) match {
		case Success(result, _) => Some(result)
		case NoSuccess(msg, _) => println(msg);None
	}
/*uncommentR?core_compiled-BEGIN*//*/*uncommentR?core_compiled-END*/*/

	def main(args:Array[String]) {
/*/*uncommentL?Sequent-BEGIN*/*//*uncommentL?Sequent-END*/
		if (args.length == 1){
			Some(JSON.parseFull(args(0))) match {
      			case Some(L(list)) =>
      				val buf = new scala.collection.mutable.ListBuffer[String]()
					for (e <- list) parseSequent(e) match {
				    	case Some(r) => 
				    		buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE)
				    	case None => buf += ""
				    }
				    print( JSONArray(buf.toList) )
				case _ => print("[]")
		    }
		}
		else if (args.length == 2){
			Some(JSON.parseFull(args(1))) match {
      			case Some(L(list)) =>
      				val buf = new scala.collection.mutable.ListBuffer[String]()
					for (e <- list) parseSequent(e) match {
				    	case Some(r) => 
				    		if(args(0) == "se") buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE_SE)
				    		else buf += PrintCalc.sequentToString(r, PrintCalc.ISABELLE)
				    	case None => buf += ""
				    }
				    print( JSONArray(buf.toList) )
				case _ => print("[]")
		    }
		}  
		else print("[]")
/*uncommentR?Sequent-BEGIN*//*/*uncommentR?Sequent-END*/*/
	}
}

class CC[T] {
  def unapply(a:Option[Any]):Option[T] = if (a.isEmpty) {
    None
  } else {
    Some(a.get.asInstanceOf[T])
  }
}

object L extends CC[List[String]]


/* the following code snippet was adapted from code found at https://gist.github.com/hisui/1692021 */

trait OperatorPrecedenceParsers extends PackratParsers {

  trait Op[+T,U] {
    def lhs:Double = 0
    def rhs:Double = 0
    def parse:PackratParser[T]
  }

  case class Infix[T,U]
  ( override val lhs:Double
  , override val rhs:Double)
  ( override val parse:PackratParser[T])(val map:(T,U,U) => U) extends Op[T,U]

  case class Prefix[T,U](override val rhs:Double)(override val parse:PackratParser[T])(val map:(T,U) => U) extends Op[T,U]
  case class Suffix[T,U](override val lhs:Double)(override val parse:PackratParser[T])(val map:(T,U) => U) extends Op[T,U]

  def operators[T,U](opseq:Op[T,U]*)(innermost:PackratParser[U]) = new PackratParser[U] {

    type Ops = List[(Op[T,U],T)]
    type Out = List[U]

    val (prefixOps, suffixOps) = opseq.partition( _.isInstanceOf[Prefix[_,_]] )

    def findPrefix(ops:Ops, out:Out, in:Input):ParseResult[U] = {

      prefixOps.iterator.map(e => e -> e.parse(in))
        .collectFirst {
          case (op, Success(o, in2)) => findPrefix(op -> o :: ops, out, in2)
        }
        .getOrElse{ //println(innermost(in)); 
        	innermost(in)
          .flatMapWithNext(o => in => findSuffix(ops, o :: out, in)) }
    }
    
    def fold(lhs:Double, ops:Ops, out:Out):(Ops,Out) =
      ops match {
        case (op, o)::ops if op.rhs < lhs =>
          fold(lhs, ops, (( (op, out): @unchecked ) match {
            case (op:Prefix[T,U], x::xs) => op.map(o, x) :: xs
            case (op:Suffix[T,U], x::xs) => op.map(o, x) :: xs
            case (op: Infix[T,U], y::x::xs) => op.map(o, x, y) :: xs
          }))
        case _ => ops -> out
      }

    def findSuffix(ops:Ops, out:Out, in:Input):ParseResult[U] =
      suffixOps.iterator.map(e => e -> e.parse(in))
        .collectFirst {
          case (op, Success(o, in)) =>
            val $ = fold(op.lhs, ops, out)
            (if (op.isInstanceOf[Infix[_,_]])
              findPrefix _ else
              findSuffix _ ) ((op, o) :: $._1, $._2, in)
        }
        .getOrElse(Success(fold(1/0.0, ops, out)._2.head, in))

    override def apply(in:Input):ParseResult[U] = findPrefix(Nil, Nil, in)

  }
}