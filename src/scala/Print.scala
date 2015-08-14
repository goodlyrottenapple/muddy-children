/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/

object PrintCalc{
	val ASCII = "ascii"
	val LATEX = "latex"
	val ISABELLE = "isabelle"
	val ISABELLE_SE = "isabelle_se"


	def bracketIf(in:String, b: Boolean = true) : String = {
		if(b) return "(" + in + ")"
		else return in
	}

	def stringToString(x:List[Char], format:String = LATEX) : String = format match {
		case ASCII | LATEX | ISABELLE_SE => x.mkString
		case ISABELLE => "''" + x.mkString +"''"
	}

/*/*uncommentL?Structure-BEGIN*/*//*uncommentL?Structure-END*/
	def structure_listToString(in:List[Structure], format:String = LATEX) : String = "[" + in.map(x => structureToString(x, format)).mkString(", ") + "]" 
/*uncommentR?Structure-BEGIN*//*/*uncommentR?Structure-END*/*/

/*print_calc_structure-BEGIN*/
	def actionToString(in:Action, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Actiona(a) => stringToString(a, format)
				case Action_Freevar(a) => "(" + "Act?" + " " + stringToString(a, format) + ")"
			}
		case LATEX =>
			in match {
				case Actiona(a) => stringToString(a, format)
				case Action_Freevar(a) => "?" + " " + stringToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Actiona(a) => "(" + "Action" + " " + stringToString(a, format) + ")"
				case Action_Freevar(a) => "(" + "?\\<^sub>Act" + " " + stringToString(a, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Actiona(a) => "(" + "Action" + " " + stringToString(a, format) + ")"
				case Action_Freevar(a) => stringToString(a, format)
			}
	}

	def actionPrec(in:Action) : Tuple2[Int, Int] = in match {
		case Actiona(a) => (Int.MinValue, Int.MinValue)
		case Action_Freevar(a) => (Int.MinValue, Int.MinValue)
	}
	def agentToString(in:Agent, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Agent_Freevar(a) => "(" + "Ag?" + " " + stringToString(a, format) + ")"
				case Agenta(a) => stringToString(a, format)
			}
		case LATEX =>
			in match {
				case Agent_Freevar(a) => "?" + " " + stringToString(a, format)
				case Agenta(a) => stringToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Agent_Freevar(a) => "(" + "?\\<^sub>Ag" + " " + stringToString(a, format) + ")"
				case Agenta(a) => "(" + "Agent" + " " + stringToString(a, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Agent_Freevar(a) => stringToString(a, format)
				case Agenta(a) => "(" + "Agent" + " " + stringToString(a, format) + ")"
			}
	}

	def agentPrec(in:Agent) : Tuple2[Int, Int] = in match {
		case Agent_Freevar(a) => (Int.MinValue, Int.MinValue)
		case Agenta(a) => (Int.MinValue, Int.MinValue)
	}
	def atpropToString(in:Atprop, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Atprop_Freevar(a) => "(" + "A?" + " " + stringToString(a, format) + ")"
				case Atpropa(a) => stringToString(a, format)
			}
		case LATEX =>
			in match {
				case Atprop_Freevar(a) => "?" + " " + stringToString(a, format)
				case Atpropa(a) => stringToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Atprop_Freevar(a) => "(" + "?\\<^sub>A" + " " + stringToString(a, format) + ")"
				case Atpropa(a) => "(" + "Atprop" + " " + stringToString(a, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Atprop_Freevar(a) => stringToString(a, format)
				case Atpropa(a) => "(" + "Atprop" + " " + stringToString(a, format) + ")"
			}
	}

	def atpropPrec(in:Atprop) : Tuple2[Int, Int] = in match {
		case Atprop_Freevar(a) => (Int.MinValue, Int.MinValue)
		case Atpropa(a) => (Int.MinValue, Int.MinValue)
	}
	def formulaToString(in:Formula, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_Agent(a) => agentToString(a, format)
				case Formula_Action_Formula(a,b,c) => "(" + formula_action_formula_opToString(a, format) + " " + actionToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Agent_Formula(a,b,c) => "(" + formula_agent_formula_opToString(a, format) + " " + agentToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Action(a) => actionToString(a, format)
				case Formula_Bin(a,b,c) => "(" + formulaToString(a, format) + " " + formula_bin_opToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Zer(a) => formula_zer_opToString(a, format)
				case Formula_Precondition(a) => "(" + "One" + " " + actionToString(a, format) + ")"
				case Formula_Freevar(a) => "(" + "F?" + " " + stringToString(a, format) + ")"
				case Formula_Atprop(a) => atpropToString(a, format)
			}
		case LATEX =>
			in match {
				case Formula_Agent(a) => agentToString(a, format)
				case Formula_Action_Formula(a,b,c) => formula_action_formula_opToString(a, format).split("_")(0) + " " + actionToString(b, format) + " " + formula_action_formula_opToString(a, format).split("_")(1) + " " + bracketIf( formulaToString(c, format), formulaPrec(Formula_Action_Formula(a,b,c))._2 < formulaPrec(c)._1 )
				case Formula_Agent_Formula(a,b,c) => formula_agent_formula_opToString(a, format).split("_")(0) + " " + agentToString(b, format) + " " + formula_agent_formula_opToString(a, format).split("_")(1) + " " + bracketIf( formulaToString(c, format), formulaPrec(Formula_Agent_Formula(a,b,c))._2 < formulaPrec(c)._1 )
				case Formula_Action(a) => actionToString(a, format)
				case Formula_Bin(a,b,c) => bracketIf( formulaToString(a, format), formulaPrec(Formula_Bin(a,b,c))._1 <= formulaPrec(a)._1 ) + " " + formula_bin_opToString(b, format) + " " + bracketIf( formulaToString(c, format), formulaPrec(Formula_Bin(a,b,c))._2 < formulaPrec(c)._1 )
				case Formula_Zer(a) => formula_zer_opToString(a, format)
				case Formula_Precondition(a) => "1_{" + " " + actionToString(a, format) + " " + "}"
				case Formula_Freevar(a) => "?" + " " + stringToString(a, format)
				case Formula_Atprop(a) => atpropToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Formula_Agent(a) => "(" + "Formula_Agent" + " " + agentToString(a, format) + ")"
				case Formula_Action_Formula(a,b,c) => "(" + "ActF\\<^sub>F" + " " + formula_action_formula_opToString(a, format) + " " + actionToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Agent_Formula(a,b,c) => "(" + "AgF\\<^sub>F" + " " + formula_agent_formula_opToString(a, format) + " " + agentToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Action(a) => "(" + "Formula_Action" + " " + actionToString(a, format) + ")"
				case Formula_Bin(a,b,c) => "(" + "B\\<^sub>F" + " " + formulaToString(a, format) + " " + formula_bin_opToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Zer(a) => "(" + "Z\\<^sub>F" + " " + formula_zer_opToString(a, format) + ")"
				case Formula_Precondition(a) => "(" + "One\\<^sub>F" + " " + actionToString(a, format) + ")"
				case Formula_Freevar(a) => "(" + "?\\<^sub>F" + " " + stringToString(a, format) + ")"
				case Formula_Atprop(a) => "(" + atpropToString(a, format) + " " + "\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_Agent(a) => "(" + "Formula_Agent" + " " + agentToString(a, format) + ")"
				case Formula_Action_Formula(a,b,c) => "(" + formula_action_formula_opToString(a, format) + " " + actionToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Agent_Formula(a,b,c) => "(" + formula_agent_formula_opToString(a, format) + " " + agentToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Action(a) => "(" + "Formula_Action" + " " + actionToString(a, format) + ")"
				case Formula_Bin(a,b,c) => "(" + formulaToString(a, format) + " " + formula_bin_opToString(b, format) + " " + formulaToString(c, format) + ")"
				case Formula_Zer(a) => formula_zer_opToString(a, format)
				case Formula_Precondition(a) => "(" + "One\\<^sub>F" + " " + actionToString(a, format) + ")"
				case Formula_Freevar(a) => stringToString(a, format)
				case Formula_Atprop(a) => "(" + atpropToString(a, format) + " " + "\\<^sub>F" + ")"
			}
	}

	def formulaPrec(in:Formula) : Tuple2[Int, Int] = in match {
		case Formula_Agent(a) => (Int.MinValue, Int.MinValue)
		case Formula_Action_Formula(a,b,c) => a match {
			case Formula_FboxA() => (200, 200)
			case Formula_FdiamA() => (200, 200)
			case Formula_BboxA() => (200, 200)
			case Formula_BdiamA() => (200, 200)
		}
		case Formula_Agent_Formula(a,b,c) => a match {
			case Formula_FboxK() => (200, 200)
			case Formula_FdiamK() => (200, 200)
			case Formula_BboxK() => (200, 200)
			case Formula_BdiamK() => (200, 200)
		}
		case Formula_Action(a) => (Int.MinValue, Int.MinValue)
		case Formula_Bin(a,b,c) => b match {
			case Formula_And() => (400, 401)
			case Formula_ImpL() => (500, 501)
			case Formula_DImpL() => (500, 501)
			case Formula_DImpR() => (500, 501)
			case Formula_Or() => (400, 401)
			case Formula_ImpR() => (500, 501)
		}
		case Formula_Zer(a) => (Int.MinValue, Int.MinValue)
		case Formula_Precondition(a) => (Int.MinValue, Int.MinValue)
		case Formula_Freevar(a) => (Int.MinValue, Int.MinValue)
		case Formula_Atprop(a) => (Int.MinValue, Int.MinValue)
	}
	def formula_action_formula_opToString(in:Formula_Action_Formula_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_FboxA() => "fboxA"
				case Formula_FdiamA() => "fdiamA"
				case Formula_BboxA() => "bboxA"
				case Formula_BdiamA() => "bdiamA"
			}
		case LATEX =>
			in match {
				case Formula_FboxA() => "[_]"
				case Formula_FdiamA() => "\\langle_\\rangle"
				case Formula_BboxA() => "\\,\\rotatebox[origin=c]{90}{$[\\kern{1.8mu}\\rotatebox[origin=c]{-90}{$_$}\\kern{1.8mu}]$}\\,"
				case Formula_BdiamA() => "\\,\\rotatebox[origin=c]{90}{$\\langle\\rotatebox[origin=c]{-90}{$_$}\\rangle$}\\,"
			}
		case ISABELLE =>
			in match {
				case Formula_FboxA() => "(" + "fboxA\\<^sub>F" + ")"
				case Formula_FdiamA() => "(" + "fdiamA\\<^sub>F" + ")"
				case Formula_BboxA() => "(" + "bboxA\\<^sub>F" + ")"
				case Formula_BdiamA() => "(" + "bdiamA\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_FboxA() => "fboxA\\<^sub>F"
				case Formula_FdiamA() => "fdiamA\\<^sub>F"
				case Formula_BboxA() => "bboxA\\<^sub>F"
				case Formula_BdiamA() => "bdiamA\\<^sub>F"
			}
	}

	def formula_agent_formula_opToString(in:Formula_Agent_Formula_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_FboxK() => "fboxK"
				case Formula_FdiamK() => "fdiamK"
				case Formula_BboxK() => "bboxK"
				case Formula_BdiamK() => "bdiamK"
			}
		case LATEX =>
			in match {
				case Formula_FboxK() => "[_]"
				case Formula_FdiamK() => "\\langle_\\rangle"
				case Formula_BboxK() => "\\,\\rotatebox[origin=c]{90}{$[\\kern{1.8mu}\\rotatebox[origin=c]{-90}{$_$}\\kern{1.8mu}]$}\\,"
				case Formula_BdiamK() => "\\,\\rotatebox[origin=c]{90}{$\\langle\\rotatebox[origin=c]{-90}{$_$}\\rangle$}\\,"
			}
		case ISABELLE =>
			in match {
				case Formula_FboxK() => "(" + "fboxK\\<^sub>F" + ")"
				case Formula_FdiamK() => "(" + "fdiamK\\<^sub>F" + ")"
				case Formula_BboxK() => "(" + "bboxK\\<^sub>F" + ")"
				case Formula_BdiamK() => "(" + "bdiamK\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_FboxK() => "fboxK\\<^sub>F"
				case Formula_FdiamK() => "fdiamK\\<^sub>F"
				case Formula_BboxK() => "bboxK\\<^sub>F"
				case Formula_BdiamK() => "bdiamK\\<^sub>F"
			}
	}

	def formula_bin_opToString(in:Formula_Bin_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_And() => "/\\"
				case Formula_ImpL() => "<"
				case Formula_DImpL() => "-<"
				case Formula_DImpR() => ">-"
				case Formula_Or() => "\\/"
				case Formula_ImpR() => ">"
			}
		case LATEX =>
			in match {
				case Formula_And() => "\\wedge"
				case Formula_ImpL() => "\\leftarrow"
				case Formula_DImpL() => "-<"
				case Formula_DImpR() => ">-"
				case Formula_Or() => "\\vee"
				case Formula_ImpR() => "\\rightarrow"
			}
		case ISABELLE =>
			in match {
				case Formula_And() => "(" + "\\<and>\\<^sub>F" + ")"
				case Formula_ImpL() => "(" + "\\<leftarrow>\\<^sub>F" + ")"
				case Formula_DImpL() => "(" + "-<\\<^sub>F" + ")"
				case Formula_DImpR() => "(" + ">-\\<^sub>F" + ")"
				case Formula_Or() => "(" + "\\<or>\\<^sub>F" + ")"
				case Formula_ImpR() => "(" + "\\<rightarrow>\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_And() => "\\<and>\\<^sub>F"
				case Formula_ImpL() => "\\<leftarrow>\\<^sub>F"
				case Formula_DImpL() => "-<\\<^sub>F"
				case Formula_DImpR() => ">-\\<^sub>F"
				case Formula_Or() => "\\<or>\\<^sub>F"
				case Formula_ImpR() => "\\<rightarrow>\\<^sub>F"
			}
	}

	def formula_zer_opToString(in:Formula_Zer_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Formula_Top() => "T"
				case Formula_Bot() => "B"
			}
		case LATEX =>
			in match {
				case Formula_Top() => "\\top"
				case Formula_Bot() => "\\bot"
			}
		case ISABELLE =>
			in match {
				case Formula_Top() => "(" + "\\<top>\\<^sub>F" + ")"
				case Formula_Bot() => "(" + "\\<bottom>\\<^sub>F" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Formula_Top() => "\\<top>\\<^sub>F"
				case Formula_Bot() => "\\<bottom>\\<^sub>F"
			}
	}

	def sequentToString(in:Sequent, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Sequent_Structure(a) => structureToString(a, format)
				case Sequenta(a,b) => "(" + structureToString(a, format) + " " + "|-" + " " + structureToString(b, format) + ")"
			}
		case LATEX =>
			in match {
				case Sequent_Structure(a) => structureToString(a, format)
				case Sequenta(a,b) => structureToString(a, format) + " " + "\\vdash" + " " + structureToString(b, format)
			}
		case ISABELLE =>
			in match {
				case Sequent_Structure(a) => "(" + "Sequent_Structure" + " " + structureToString(a, format) + ")"
				case Sequenta(a,b) => "(" + structureToString(a, format) + " " + "\\<turnstile>\\<^sub>S" + " " + structureToString(b, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Sequent_Structure(a) => "(" + "Sequent_Structure" + " " + structureToString(a, format) + ")"
				case Sequenta(a,b) => "(" + structureToString(a, format) + " " + "\\<turnstile>\\<^sub>S" + " " + structureToString(b, format) + ")"
			}
	}

	def sequentPrec(in:Sequent) : Tuple2[Int, Int] = in match {
		case Sequent_Structure(a) => (Int.MinValue, Int.MinValue)
		case Sequenta(a,b) => (Int.MinValue, Int.MinValue)
	}
	def structureToString(in:Structure, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_Bigcomma(a) => "(" + ";;" + " " + structure_listToString(a, format) + ")"
				case Structure_Bin(a,b,c) => "(" + structureToString(a, format) + " " + structure_bin_opToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Agent_Structure(a,b,c) => "(" + structure_agent_structure_opToString(a, format) + " " + agentToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Formula(a) => formulaToString(a, format)
				case Structure_Phi(a) => "(" + "Phi" + " " + actionToString(a, format) + ")"
				case Structure_Zer(a) => structure_zer_opToString(a, format)
				case Structure_Action_Structure(a,b,c) => "(" + structure_action_structure_opToString(a, format) + " " + actionToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Freevar(a) => "(" + "?" + " " + stringToString(a, format) + ")"
			}
		case LATEX =>
			in match {
				case Structure_Bigcomma(a) => "\\mbox{\\Large" + " " + "{\\bf" + " " + ";}}" + " " + structure_listToString(a, format) + " " + ""
				case Structure_Bin(a,b,c) => bracketIf( structureToString(a, format), structurePrec(Structure_Bin(a,b,c))._1 <= structurePrec(a)._1 ) + " " + structure_bin_opToString(b, format) + " " + bracketIf( structureToString(c, format), structurePrec(Structure_Bin(a,b,c))._2 < structurePrec(c)._1 )
				case Structure_Agent_Structure(a,b,c) => structure_agent_structure_opToString(a, format).split("_")(0) + " " + agentToString(b, format) + " " + structure_agent_structure_opToString(a, format).split("_")(1) + " " + bracketIf( structureToString(c, format), structurePrec(Structure_Agent_Structure(a,b,c))._2 < structurePrec(c)._1 )
				case Structure_Formula(a) => formulaToString(a, format)
				case Structure_Phi(a) => "Phi(" + " " + actionToString(a, format) + " " + ")"
				case Structure_Zer(a) => structure_zer_opToString(a, format)
				case Structure_Action_Structure(a,b,c) => structure_action_structure_opToString(a, format).split("_")(0) + " " + actionToString(b, format) + " " + structure_action_structure_opToString(a, format).split("_")(1) + " " + bracketIf( structureToString(c, format), structurePrec(Structure_Action_Structure(a,b,c))._2 < structurePrec(c)._1 )
				case Structure_Freevar(a) => "?" + " " + stringToString(a, format)
			}
		case ISABELLE =>
			in match {
				case Structure_Bigcomma(a) => "(" + ";;\\<^sub>S" + " " + structure_listToString(a, format) + ")"
				case Structure_Bin(a,b,c) => "(" + "B\\<^sub>S" + " " + structureToString(a, format) + " " + structure_bin_opToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Agent_Structure(a,b,c) => "(" + "AgS\\<^sub>S" + " " + structure_agent_structure_opToString(a, format) + " " + agentToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Formula(a) => "(" + formulaToString(a, format) + " " + "\\<^sub>S" + ")"
				case Structure_Phi(a) => "(" + "Phi\\<^sub>S" + " " + actionToString(a, format) + ")"
				case Structure_Zer(a) => "(" + "Z\\<^sub>S" + " " + structure_zer_opToString(a, format) + ")"
				case Structure_Action_Structure(a,b,c) => "(" + "ActS\\<^sub>S" + " " + structure_action_structure_opToString(a, format) + " " + actionToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Freevar(a) => "(" + "?\\<^sub>S" + " " + stringToString(a, format) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_Bigcomma(a) => "(" + ";;\\<^sub>S" + " " + structure_listToString(a, format) + ")"
				case Structure_Bin(a,b,c) => "(" + structureToString(a, format) + " " + structure_bin_opToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Agent_Structure(a,b,c) => "(" + structure_agent_structure_opToString(a, format) + " " + agentToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Formula(a) => "(" + formulaToString(a, format) + " " + "\\<^sub>S" + ")"
				case Structure_Phi(a) => "(" + "Phi\\<^sub>S" + " " + actionToString(a, format) + ")"
				case Structure_Zer(a) => structure_zer_opToString(a, format)
				case Structure_Action_Structure(a,b,c) => "(" + structure_action_structure_opToString(a, format) + " " + actionToString(b, format) + " " + structureToString(c, format) + ")"
				case Structure_Freevar(a) => stringToString(a, format)
			}
	}

	def structurePrec(in:Structure) : Tuple2[Int, Int] = in match {
		case Structure_Bigcomma(a) => (Int.MinValue, Int.MinValue)
		case Structure_Bin(a,b,c) => b match {
			case Structure_Comma() => (400, 401)
			case Structure_ImpL() => (500, 501)
			case Structure_ImpR() => (500, 501)
		}
		case Structure_Agent_Structure(a,b,c) => a match {
			case Structure_BackK() => (200, 200)
			case Structure_ForwK() => (200, 200)
		}
		case Structure_Formula(a) => (Int.MinValue, Int.MinValue)
		case Structure_Phi(a) => (Int.MinValue, Int.MinValue)
		case Structure_Zer(a) => (Int.MinValue, Int.MinValue)
		case Structure_Action_Structure(a,b,c) => a match {
			case Structure_ForwA() => (200, 200)
			case Structure_BackA() => (200, 200)
		}
		case Structure_Freevar(a) => (Int.MinValue, Int.MinValue)
	}
	def structure_action_structure_opToString(in:Structure_Action_Structure_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_ForwA() => "forwA"
				case Structure_BackA() => "backA"
			}
		case LATEX =>
			in match {
				case Structure_ForwA() => "\\{_\\}"
				case Structure_BackA() => "\\,\\rotatebox[origin=c]{90}{$\\{\\rotatebox[origin=c]{-90}{$_$}\\}$}\\,"
			}
		case ISABELLE =>
			in match {
				case Structure_ForwA() => "(" + "forwA\\<^sub>S" + ")"
				case Structure_BackA() => "(" + "backA\\<^sub>S" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_ForwA() => "forwA\\<^sub>S"
				case Structure_BackA() => "backA\\<^sub>S"
			}
	}

	def structure_agent_structure_opToString(in:Structure_Agent_Structure_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_BackK() => "backK"
				case Structure_ForwK() => "forwK"
			}
		case LATEX =>
			in match {
				case Structure_BackK() => "\\,\\rotatebox[origin=c]{90}{$\\{\\rotatebox[origin=c]{-90}{$_$}\\}$}\\,"
				case Structure_ForwK() => "\\{_\\}"
			}
		case ISABELLE =>
			in match {
				case Structure_BackK() => "(" + "backK\\<^sub>S" + ")"
				case Structure_ForwK() => "(" + "forwK\\<^sub>S" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_BackK() => "backK\\<^sub>S"
				case Structure_ForwK() => "forwK\\<^sub>S"
			}
	}

	def structure_bin_opToString(in:Structure_Bin_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_Comma() => ";"
				case Structure_ImpL() => "<<"
				case Structure_ImpR() => ">>"
			}
		case LATEX =>
			in match {
				case Structure_Comma() => ";"
				case Structure_ImpL() => "<<"
				case Structure_ImpR() => ">>"
			}
		case ISABELLE =>
			in match {
				case Structure_Comma() => "(" + ";\\<^sub>S" + ")"
				case Structure_ImpL() => "(" + "\\<leftarrow>\\<^sub>S" + ")"
				case Structure_ImpR() => "(" + "\\<rightarrow>\\<^sub>S" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_Comma() => ";\\<^sub>S"
				case Structure_ImpL() => "\\<leftarrow>\\<^sub>S"
				case Structure_ImpR() => "\\<rightarrow>\\<^sub>S"
			}
	}

	def structure_zer_opToString(in:Structure_Zer_Op, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Structure_Neutral() => "I"
			}
		case LATEX =>
			in match {
				case Structure_Neutral() => "I"
			}
		case ISABELLE =>
			in match {
				case Structure_Neutral() => "(" + "I\\<^sub>S" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Structure_Neutral() => "I\\<^sub>S"
			}
	}

/*print_calc_structure-END*/

/*print_calc_structure_rules-BEGIN*/
	def rulebigcommaToString(in:RuleBigcomma, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Bigcomma_Nil_R() => "Bigcomma_Nil_R"
				case Bigcomma_Cons_R() => "Bigcomma_Cons_R"
				case Bigcomma_Cons_L2() => "Bigcomma_Cons_L2"
				case Bigcomma_Nil_L2() => "Bigcomma_Nil_L2"
				case Bigcomma_Cons_R2() => "Bigcomma_Cons_R2"
				case Bigcomma_Cons_L() => "Bigcomma_Cons_L"
				case Bigcomma_Nil_R2() => "Bigcomma_Nil_R2"
				case Bigcomma_Nil_L() => "Bigcomma_Nil_L"
			}
		case LATEX =>
			in match {
				case Bigcomma_Nil_R() => "Bigcomma_Nil_R"
				case Bigcomma_Cons_R() => "Bigcomma_Cons_R"
				case Bigcomma_Cons_L2() => "Bigcomma_Cons_L"
				case Bigcomma_Nil_L2() => "Bigcomma_Nil_L"
				case Bigcomma_Cons_R2() => "Bigcomma_Cons_R"
				case Bigcomma_Cons_L() => "Bigcomma_Cons_L"
				case Bigcomma_Nil_R2() => "Bigcomma_Nil_R"
				case Bigcomma_Nil_L() => "Bigcomma_Nil_L"
			}
		case ISABELLE =>
			in match {
				case Bigcomma_Nil_R() => "(" + "Bigcomma_Nil_R" + ")"
				case Bigcomma_Cons_R() => "(" + "Bigcomma_Cons_R" + ")"
				case Bigcomma_Cons_L2() => "(" + "Bigcomma_Cons_L2" + ")"
				case Bigcomma_Nil_L2() => "(" + "Bigcomma_Nil_L2" + ")"
				case Bigcomma_Cons_R2() => "(" + "Bigcomma_Cons_R2" + ")"
				case Bigcomma_Cons_L() => "(" + "Bigcomma_Cons_L" + ")"
				case Bigcomma_Nil_R2() => "(" + "Bigcomma_Nil_R2" + ")"
				case Bigcomma_Nil_L() => "(" + "Bigcomma_Nil_L" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Bigcomma_Nil_R() => "Bigcomma_Nil_R"
				case Bigcomma_Cons_R() => "Bigcomma_Cons_R"
				case Bigcomma_Cons_L2() => "Bigcomma_Cons_L2"
				case Bigcomma_Nil_L2() => "Bigcomma_Nil_L2"
				case Bigcomma_Cons_R2() => "Bigcomma_Cons_R2"
				case Bigcomma_Cons_L() => "Bigcomma_Cons_L"
				case Bigcomma_Nil_R2() => "Bigcomma_Nil_R2"
				case Bigcomma_Nil_L() => "Bigcomma_Nil_L"
			}
	}

	def rulecutToString(in:RuleCut, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case SingleCut() => "Cut"
			}
		case LATEX =>
			in match {
				case SingleCut() => "Cut"
			}
		case ISABELLE =>
			in match {
				case SingleCut() => "(" + "SingleCut" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case SingleCut() => "SingleCut"
			}
	}

	def ruledispToString(in:RuleDisp, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Comma_impL_disp() => "Comma_impL_disp"
				case Comma_impR_disp2() => "Comma_impR_disp2"
				case ImpL_comma_disp2() => "ImpL_comma_disp2"
				case ImpR_comma_disp2() => "ImpR_comma_disp2"
				case ImpR_comma_disp() => "ImpR_comma_disp"
				case ImpL_comma_disp() => "ImpL_comma_disp"
				case Comma_impR_disp() => "Comma_impR_disp"
				case Comma_impL_disp2() => "Comma_impL_disp2"
			}
		case LATEX =>
			in match {
				case Comma_impL_disp() => "(;," + " " + "<)"
				case Comma_impR_disp2() => "(;," + " " + ">)"
				case ImpL_comma_disp2() => "(<," + " " + ";)"
				case ImpR_comma_disp2() => "(>," + " " + ";)"
				case ImpR_comma_disp() => "(>," + " " + ";)"
				case ImpL_comma_disp() => "(<," + " " + ";)"
				case Comma_impR_disp() => "(;," + " " + ">)"
				case Comma_impL_disp2() => "(;," + " " + "<)"
			}
		case ISABELLE =>
			in match {
				case Comma_impL_disp() => "(" + "Comma_impL_disp" + ")"
				case Comma_impR_disp2() => "(" + "Comma_impR_disp2" + ")"
				case ImpL_comma_disp2() => "(" + "ImpL_comma_disp2" + ")"
				case ImpR_comma_disp2() => "(" + "ImpR_comma_disp2" + ")"
				case ImpR_comma_disp() => "(" + "ImpR_comma_disp" + ")"
				case ImpL_comma_disp() => "(" + "ImpL_comma_disp" + ")"
				case Comma_impR_disp() => "(" + "Comma_impR_disp" + ")"
				case Comma_impL_disp2() => "(" + "Comma_impL_disp2" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Comma_impL_disp() => "Comma_impL_disp"
				case Comma_impR_disp2() => "Comma_impR_disp2"
				case ImpL_comma_disp2() => "ImpL_comma_disp2"
				case ImpR_comma_disp2() => "ImpR_comma_disp2"
				case ImpR_comma_disp() => "ImpR_comma_disp"
				case ImpL_comma_disp() => "ImpL_comma_disp"
				case Comma_impR_disp() => "Comma_impR_disp"
				case Comma_impL_disp2() => "Comma_impL_disp2"
			}
	}

	def ruledispactToString(in:RuleDispAct, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Back_forw_A() => "Back_forw_A"
				case Forw_back_A2() => "Forw_back_A2"
				case Forw_back_A() => "Forw_back_A"
				case Back_forw_A2() => "Back_forw_A2"
			}
		case LATEX =>
			in match {
				case Back_forw_A() => "Back_forw_A"
				case Forw_back_A2() => "Forw_back_A2"
				case Forw_back_A() => "Forw_back_A"
				case Back_forw_A2() => "Back_forw_A2"
			}
		case ISABELLE =>
			in match {
				case Back_forw_A() => "(" + "Back_forw_A" + ")"
				case Forw_back_A2() => "(" + "Forw_back_A2" + ")"
				case Forw_back_A() => "(" + "Forw_back_A" + ")"
				case Back_forw_A2() => "(" + "Back_forw_A2" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Back_forw_A() => "Back_forw_A"
				case Forw_back_A2() => "Forw_back_A2"
				case Forw_back_A() => "Forw_back_A"
				case Back_forw_A2() => "Back_forw_A2"
			}
	}

	def ruledispkToString(in:RuleDispK, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Back_forw_K2() => "Back_forw_K2"
				case Back_forw_K() => "Back_forw_K"
				case Forw_back_K2() => "Forw_back_K2"
				case Forw_back_K() => "Forw_back_K"
			}
		case LATEX =>
			in match {
				case Back_forw_K2() => "Back_forw_K2"
				case Back_forw_K() => "Back_forw_K"
				case Forw_back_K2() => "Forw_back_K2"
				case Forw_back_K() => "Forw_back_K"
			}
		case ISABELLE =>
			in match {
				case Back_forw_K2() => "(" + "Back_forw_K2" + ")"
				case Back_forw_K() => "(" + "Back_forw_K" + ")"
				case Forw_back_K2() => "(" + "Forw_back_K2" + ")"
				case Forw_back_K() => "(" + "Forw_back_K" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Back_forw_K2() => "Back_forw_K2"
				case Back_forw_K() => "Back_forw_K"
				case Forw_back_K2() => "Forw_back_K2"
				case Forw_back_K() => "Forw_back_K"
			}
	}

	def rulegrishToString(in:RuleGrish, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Grishin_R2() => "Grishin_R2"
				case Grishin_R() => "Grishin_R"
				case Grishin_L() => "Grishin_L"
				case Grishin_L2() => "Grishin_L2"
			}
		case LATEX =>
			in match {
				case Grishin_R2() => "Grishin_R"
				case Grishin_R() => "Grishin_R"
				case Grishin_L() => "Grishin_L"
				case Grishin_L2() => "Grishin_L"
			}
		case ISABELLE =>
			in match {
				case Grishin_R2() => "(" + "Grishin_R2" + ")"
				case Grishin_R() => "(" + "Grishin_R" + ")"
				case Grishin_L() => "(" + "Grishin_L" + ")"
				case Grishin_L2() => "(" + "Grishin_L2" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Grishin_R2() => "Grishin_R2"
				case Grishin_R() => "Grishin_R"
				case Grishin_L() => "Grishin_L"
				case Grishin_L2() => "Grishin_L2"
			}
	}

	def ruleknowledgeToString(in:RuleKnowledge, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Refl_ForwK() => "Refl_ForwK"
			}
		case LATEX =>
			in match {
				case Refl_ForwK() => "Refl_FboxK"
			}
		case ISABELLE =>
			in match {
				case Refl_ForwK() => "(" + "Refl_ForwK" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Refl_ForwK() => "Refl_ForwK"
			}
	}

	def ruleopToString(in:RuleOp, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Bot_R() => "Bot_R"
				case Top_L() => "Top_L"
				case DImpR_L() => "DImpR_L"
				case ImpL_R() => "ImpL_R"
				case DImpL_R() => "DImpL_R"
				case And_L() => "And_L"
				case ImpR_R() => "ImpR_R"
				case Or_L() => "Or_L"
				case Or_R() => "Or_R"
				case ImpR_L() => "ImpR_L"
				case DImpL_L() => "DImpL_L"
				case And_R() => "And_R"
				case DImpR_R() => "DImpR_R"
				case ImpL_L() => "ImpL_L"
				case Top_R() => "Top_R"
				case Bot_L() => "Bot_L"
			}
		case LATEX =>
			in match {
				case Bot_R() => "\\bot_R"
				case Top_L() => "\\top_L"
				case DImpR_L() => ">-_L"
				case ImpL_R() => "\\leftarrow_R"
				case DImpL_R() => "-<_R"
				case And_L() => "\\wedge_L"
				case ImpR_R() => "\\rightarrow_R"
				case Or_L() => "\\vee_L"
				case Or_R() => "\\vee_R"
				case ImpR_L() => "\\rightarrow_L"
				case DImpL_L() => "-<_L"
				case And_R() => "\\wedge_R"
				case DImpR_R() => ">-_R"
				case ImpL_L() => "\\leftarrow_L"
				case Top_R() => "\\top_R"
				case Bot_L() => "\\bot_L"
			}
		case ISABELLE =>
			in match {
				case Bot_R() => "(" + "Bot_R" + ")"
				case Top_L() => "(" + "Top_L" + ")"
				case DImpR_L() => "(" + "DImpR_L" + ")"
				case ImpL_R() => "(" + "ImpL_R" + ")"
				case DImpL_R() => "(" + "DImpL_R" + ")"
				case And_L() => "(" + "And_L" + ")"
				case ImpR_R() => "(" + "ImpR_R" + ")"
				case Or_L() => "(" + "Or_L" + ")"
				case Or_R() => "(" + "Or_R" + ")"
				case ImpR_L() => "(" + "ImpR_L" + ")"
				case DImpL_L() => "(" + "DImpL_L" + ")"
				case And_R() => "(" + "And_R" + ")"
				case DImpR_R() => "(" + "DImpR_R" + ")"
				case ImpL_L() => "(" + "ImpL_L" + ")"
				case Top_R() => "(" + "Top_R" + ")"
				case Bot_L() => "(" + "Bot_L" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Bot_R() => "Bot_R"
				case Top_L() => "Top_L"
				case DImpR_L() => "DImpR_L"
				case ImpL_R() => "ImpL_R"
				case DImpL_R() => "DImpL_R"
				case And_L() => "And_L"
				case ImpR_R() => "ImpR_R"
				case Or_L() => "Or_L"
				case Or_R() => "Or_R"
				case ImpR_L() => "ImpR_L"
				case DImpL_L() => "DImpL_L"
				case And_R() => "And_R"
				case DImpR_R() => "DImpR_R"
				case ImpL_L() => "ImpL_L"
				case Top_R() => "Top_R"
				case Bot_L() => "Bot_L"
			}
	}

	def ruleopactToString(in:RuleOpAct, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case FdiamA_L() => "FdiamA_L"
				case One_R() => "One_R"
				case BdiamA_R() => "BdiamA_R"
				case FboxA_R() => "FboxA_R"
				case Pre_L() => "Pre_L"
				case BboxA_R() => "BboxA_R"
				case BboxA_L() => "BboxA_L"
				case FboxA_L() => "FboxA_L"
				case BdiamA_L() => "BdiamA_L"
				case One_L() => "One_L"
				case FdiamA_R() => "FdiamA_R"
			}
		case LATEX =>
			in match {
				case FdiamA_L() => "FdiamA_L"
				case One_R() => "One_R"
				case BdiamA_R() => "BdiamA_R"
				case FboxA_R() => "FboxA_R"
				case Pre_L() => "Pre_L"
				case BboxA_R() => "BboxA_R"
				case BboxA_L() => "BboxA_L"
				case FboxA_L() => "FboxA_L"
				case BdiamA_L() => "BdiamA_L"
				case One_L() => "One_L"
				case FdiamA_R() => "FdiamA_R"
			}
		case ISABELLE =>
			in match {
				case FdiamA_L() => "(" + "FdiamA_L" + ")"
				case One_R() => "(" + "One_R" + ")"
				case BdiamA_R() => "(" + "BdiamA_R" + ")"
				case FboxA_R() => "(" + "FboxA_R" + ")"
				case Pre_L() => "(" + "Pre_L" + ")"
				case BboxA_R() => "(" + "BboxA_R" + ")"
				case BboxA_L() => "(" + "BboxA_L" + ")"
				case FboxA_L() => "(" + "FboxA_L" + ")"
				case BdiamA_L() => "(" + "BdiamA_L" + ")"
				case One_L() => "(" + "One_L" + ")"
				case FdiamA_R() => "(" + "FdiamA_R" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case FdiamA_L() => "FdiamA_L"
				case One_R() => "One_R"
				case BdiamA_R() => "BdiamA_R"
				case FboxA_R() => "FboxA_R"
				case Pre_L() => "Pre_L"
				case BboxA_R() => "BboxA_R"
				case BboxA_L() => "BboxA_L"
				case FboxA_L() => "FboxA_L"
				case BdiamA_L() => "BdiamA_L"
				case One_L() => "One_L"
				case FdiamA_R() => "FdiamA_R"
			}
	}

	def ruleopkToString(in:RuleOpK, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case BdiamK_L() => "BdiamK_L"
				case FdiamK_R() => "FdiamK_R"
				case FboxK_R() => "FboxK_R"
				case BboxK_L() => "BboxK_L"
				case BboxK_R() => "BboxK_R"
				case FboxK_L() => "FboxK_L"
				case FdiamK_L() => "FdiamK_L"
				case BdiamK_R() => "BdiamK_R"
			}
		case LATEX =>
			in match {
				case BdiamK_L() => "BdiamK_L"
				case FdiamK_R() => "FdiamK_R"
				case FboxK_R() => "FboxK_R"
				case BboxK_L() => "BboxK_L"
				case BboxK_R() => "BboxK_R"
				case FboxK_L() => "FboxK_L"
				case FdiamK_L() => "FdiamK_L"
				case BdiamK_R() => "BdiamK_R"
			}
		case ISABELLE =>
			in match {
				case BdiamK_L() => "(" + "BdiamK_L" + ")"
				case FdiamK_R() => "(" + "FdiamK_R" + ")"
				case FboxK_R() => "(" + "FboxK_R" + ")"
				case BboxK_L() => "(" + "BboxK_L" + ")"
				case BboxK_R() => "(" + "BboxK_R" + ")"
				case FboxK_L() => "(" + "FboxK_L" + ")"
				case FdiamK_L() => "(" + "FdiamK_L" + ")"
				case BdiamK_R() => "(" + "BdiamK_R" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case BdiamK_L() => "BdiamK_L"
				case FdiamK_R() => "FdiamK_R"
				case FboxK_R() => "FboxK_R"
				case BboxK_L() => "BboxK_L"
				case BboxK_R() => "BboxK_R"
				case FboxK_L() => "FboxK_L"
				case FdiamK_L() => "FdiamK_L"
				case BdiamK_R() => "BdiamK_R"
			}
	}

	def rulestructToString(in:RuleStruct, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case W_impL_R() => "W_impL_R"
				case ImpL_I() => "ImpL_I"
				case W_impL_L() => "W_impL_L"
				case ImpR_I2() => "ImpR_I2"
				case E_R() => "E_R"
				case IW_R() => "IW_R"
				case IW_L() => "IW_L"
				case A_L2() => "A_L2"
				case E_L() => "E_L"
				case A_R() => "A_R"
				case W_impR_R() => "W_impR_R"
				case C_L() => "C_L"
				case C_R() => "C_R"
				case ImpR_I() => "ImpR_I"
				case W_impR_L() => "W_impR_L"
				case A_L() => "A_L"
				case A_R2() => "A_R2"
				case I_impR2() => "I_impR2"
				case I_impL() => "I_impL"
				case I_impR() => "I_impR"
				case ImpL_I2() => "ImpL_I2"
				case I_impL2() => "I_impL2"
			}
		case LATEX =>
			in match {
				case W_impL_R() => "W" + " " + "<_R"
				case ImpL_I() => "<_R" + " " + "I"
				case W_impL_L() => "W" + " " + "<_L"
				case ImpR_I2() => ">_R" + " " + "I"
				case E_R() => "E_R"
				case IW_R() => "\\textrm{I}" + " " + "W_{R}"
				case IW_L() => "\\textrm{I}" + " " + "W_{L}"
				case A_L2() => "A_L"
				case E_L() => "E_L"
				case A_R() => "A_R"
				case W_impR_R() => "W" + " " + ">_R"
				case C_L() => "C_L"
				case C_R() => "C_R"
				case ImpR_I() => ">_R" + " " + "I"
				case W_impR_L() => "W" + " " + ">_L"
				case A_L() => "A_L"
				case A_R2() => "A_R"
				case I_impR2() => "I" + " " + ">_R"
				case I_impL() => "I" + " " + "<_R"
				case I_impR() => "I" + " " + ">_R"
				case ImpL_I2() => "<_R" + " " + "I"
				case I_impL2() => "I" + " " + "<_R"
			}
		case ISABELLE =>
			in match {
				case W_impL_R() => "(" + "W_impL_R" + ")"
				case ImpL_I() => "(" + "ImpL_I" + ")"
				case W_impL_L() => "(" + "W_impL_L" + ")"
				case ImpR_I2() => "(" + "ImpR_I2" + ")"
				case E_R() => "(" + "E_R" + ")"
				case IW_R() => "(" + "IW_R" + ")"
				case IW_L() => "(" + "IW_L" + ")"
				case A_L2() => "(" + "A_L2" + ")"
				case E_L() => "(" + "E_L" + ")"
				case A_R() => "(" + "A_R" + ")"
				case W_impR_R() => "(" + "W_impR_R" + ")"
				case C_L() => "(" + "C_L" + ")"
				case C_R() => "(" + "C_R" + ")"
				case ImpR_I() => "(" + "ImpR_I" + ")"
				case W_impR_L() => "(" + "W_impR_L" + ")"
				case A_L() => "(" + "A_L" + ")"
				case A_R2() => "(" + "A_R2" + ")"
				case I_impR2() => "(" + "I_impR2" + ")"
				case I_impL() => "(" + "I_impL" + ")"
				case I_impR() => "(" + "I_impR" + ")"
				case ImpL_I2() => "(" + "ImpL_I2" + ")"
				case I_impL2() => "(" + "I_impL2" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case W_impL_R() => "W_impL_R"
				case ImpL_I() => "ImpL_I"
				case W_impL_L() => "W_impL_L"
				case ImpR_I2() => "ImpR_I2"
				case E_R() => "E_R"
				case IW_R() => "IW_R"
				case IW_L() => "IW_L"
				case A_L2() => "A_L2"
				case E_L() => "E_L"
				case A_R() => "A_R"
				case W_impR_R() => "W_impR_R"
				case C_L() => "C_L"
				case C_R() => "C_R"
				case ImpR_I() => "ImpR_I"
				case W_impR_L() => "W_impR_L"
				case A_L() => "A_L"
				case A_R2() => "A_R2"
				case I_impR2() => "I_impR2"
				case I_impL() => "I_impL"
				case I_impR() => "I_impR"
				case ImpL_I2() => "ImpL_I2"
				case I_impL2() => "I_impL2"
			}
	}

	def rulestructactToString(in:RuleStructAct, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case A_nec_L() => "A_nec_L"
				case A_mon_L() => "A_mon_L"
				case Mon_A_R() => "Mon_A_R"
				case Nec_A_L() => "Nec_A_L"
				case FS_A_L() => "FS_A_L"
				case FS_A_R() => "FS_A_R"
				case A_mon_R() => "A_mon_R"
				case A_FS_R() => "A_FS_R"
				case Nec_A_R() => "Nec_A_R"
				case Mon_A_L() => "Mon_A_L"
				case A_FS_L() => "A_FS_L"
				case A_nec_R() => "A_nec_R"
			}
		case LATEX =>
			in match {
				case A_nec_L() => "A_nec_L"
				case A_mon_L() => "A_mon_L"
				case Mon_A_R() => "Mon_A_R"
				case Nec_A_L() => "Nec_A_L"
				case FS_A_L() => "FS_A_L"
				case FS_A_R() => "FS_A_R"
				case A_mon_R() => "A_mon_R"
				case A_FS_R() => "A_FS_R"
				case Nec_A_R() => "Nec_A_R"
				case Mon_A_L() => "Mon_A_L"
				case A_FS_L() => "A_FS_L"
				case A_nec_R() => "A_nec_R"
			}
		case ISABELLE =>
			in match {
				case A_nec_L() => "(" + "A_nec_L" + ")"
				case A_mon_L() => "(" + "A_mon_L" + ")"
				case Mon_A_R() => "(" + "Mon_A_R" + ")"
				case Nec_A_L() => "(" + "Nec_A_L" + ")"
				case FS_A_L() => "(" + "FS_A_L" + ")"
				case FS_A_R() => "(" + "FS_A_R" + ")"
				case A_mon_R() => "(" + "A_mon_R" + ")"
				case A_FS_R() => "(" + "A_FS_R" + ")"
				case Nec_A_R() => "(" + "Nec_A_R" + ")"
				case Mon_A_L() => "(" + "Mon_A_L" + ")"
				case A_FS_L() => "(" + "A_FS_L" + ")"
				case A_nec_R() => "(" + "A_nec_R" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case A_nec_L() => "A_nec_L"
				case A_mon_L() => "A_mon_L"
				case Mon_A_R() => "Mon_A_R"
				case Nec_A_L() => "Nec_A_L"
				case FS_A_L() => "FS_A_L"
				case FS_A_R() => "FS_A_R"
				case A_mon_R() => "A_mon_R"
				case A_FS_R() => "A_FS_R"
				case Nec_A_R() => "Nec_A_R"
				case Mon_A_L() => "Mon_A_L"
				case A_FS_L() => "A_FS_L"
				case A_nec_R() => "A_nec_R"
			}
	}

	def rulestructeaToString(in:RuleStructEA, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Reduce_R() => "Reduce'R"
				case CompA_R() => "CompA_R"
				case Balance() => "Balance"
				case CompA_L() => "CompA_L"
				case Reduce_L() => "Reduce'L"
			}
		case LATEX =>
			in match {
				case Reduce_R() => "Reduce'R"
				case CompA_R() => "CompA_R"
				case Balance() => "Balance"
				case CompA_L() => "CompA_L"
				case Reduce_L() => "Reduce'L"
			}
		case ISABELLE =>
			in match {
				case Reduce_R() => "(" + "Reduce_R" + ")"
				case CompA_R() => "(" + "CompA_R" + ")"
				case Balance() => "(" + "Balance" + ")"
				case CompA_L() => "(" + "CompA_L" + ")"
				case Reduce_L() => "(" + "Reduce_L" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Reduce_R() => "Reduce_R"
				case CompA_R() => "CompA_R"
				case Balance() => "Balance"
				case CompA_L() => "CompA_L"
				case Reduce_L() => "Reduce_L"
			}
	}

	def rulestructkToString(in:RuleStructK, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case K_nec_R() => "K_nec_R"
				case Nec_K_L() => "Nec_K_L"
				case K_mon_L() => "K_mon_L"
				case Mon_K_L() => "Mon_K_L"
				case FS_K_L() => "FS_K_L"
				case FS_K_R() => "FS_K_R"
				case Mon_K_R() => "Mon_K_R"
				case K_mon_R() => "K_mon_R"
				case K_FS_L() => "K_FS_L"
				case Nec_K_R() => "Nec_K_R"
				case K_FS_R() => "K_FS_R"
				case K_nec_L() => "K_nec_L"
			}
		case LATEX =>
			in match {
				case K_nec_R() => "K_nec_R"
				case Nec_K_L() => "Nec_K_L"
				case K_mon_L() => "K_mon_L"
				case Mon_K_L() => "Mon_K_L"
				case FS_K_L() => "FS_K_L"
				case FS_K_R() => "FS_K_R"
				case Mon_K_R() => "Mon_K_R"
				case K_mon_R() => "K_mon_R"
				case K_FS_L() => "K_FS_L"
				case Nec_K_R() => "Nec_K_R"
				case K_FS_R() => "K_FS_R"
				case K_nec_L() => "K_nec_L"
			}
		case ISABELLE =>
			in match {
				case K_nec_R() => "(" + "K_nec_R" + ")"
				case Nec_K_L() => "(" + "Nec_K_L" + ")"
				case K_mon_L() => "(" + "K_mon_L" + ")"
				case Mon_K_L() => "(" + "Mon_K_L" + ")"
				case FS_K_L() => "(" + "FS_K_L" + ")"
				case FS_K_R() => "(" + "FS_K_R" + ")"
				case Mon_K_R() => "(" + "Mon_K_R" + ")"
				case K_mon_R() => "(" + "K_mon_R" + ")"
				case K_FS_L() => "(" + "K_FS_L" + ")"
				case Nec_K_R() => "(" + "Nec_K_R" + ")"
				case K_FS_R() => "(" + "K_FS_R" + ")"
				case K_nec_L() => "(" + "K_nec_L" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case K_nec_R() => "K_nec_R"
				case Nec_K_L() => "Nec_K_L"
				case K_mon_L() => "K_mon_L"
				case Mon_K_L() => "Mon_K_L"
				case FS_K_L() => "FS_K_L"
				case FS_K_R() => "FS_K_R"
				case Mon_K_R() => "Mon_K_R"
				case K_mon_R() => "K_mon_R"
				case K_FS_L() => "K_FS_L"
				case Nec_K_R() => "Nec_K_R"
				case K_FS_R() => "K_FS_R"
				case K_nec_L() => "K_nec_L"
			}
	}

	def ruleswapinToString(in:RuleSwapin, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Swapin_L() => "swapin'L"
				case Swapin_R() => "swapin'R"
			}
		case LATEX =>
			in match {
				case Swapin_L() => "swapin'L"
				case Swapin_R() => "swapin'R"
			}
		case ISABELLE =>
			in match {
				case Swapin_L() => "(" + "Swapin_L" + ")"
				case Swapin_R() => "(" + "Swapin_R" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Swapin_L() => "Swapin_L"
				case Swapin_R() => "Swapin_R"
			}
	}

	def ruleswapoutToString(in:RuleSwapout, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Swapout_L() => "swapout'L"
				case Swapout_R() => "Swapout'R"
			}
		case LATEX =>
			in match {
				case Swapout_L() => "swapout'L"
				case Swapout_R() => "Swapout'R"
			}
		case ISABELLE =>
			in match {
				case Swapout_L() => "(" + "Swapout_L" + ")"
				case Swapout_R() => "(" + "Swapout_R" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Swapout_L() => "Swapout_L"
				case Swapout_R() => "Swapout_R"
			}
	}

	def rulezerToString(in:RuleZer, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
				case Prem() => "Prem"
				case Partial() => "Partial"
				case Id() => "Id"
				case Atom() => "Atom"
			}
		case LATEX =>
			in match {
				case Prem() => "Prem"
				case Partial() => "Partial"
				case Id() => "Id"
				case Atom() => "Atom"
			}
		case ISABELLE =>
			in match {
				case Prem() => "(" + "Prem" + ")"
				case Partial() => "(" + "Partial" + ")"
				case Id() => "(" + "Id" + ")"
				case Atom() => "(" + "Atom" + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Prem() => "Prem"
				case Partial() => "Partial"
				case Id() => "Id"
				case Atom() => "Atom"
			}
	}

	def ruleToString(in:Rule, format:String = LATEX) : String = format match {
		case ASCII =>
			in match {
             case RuleBigcommaa(a) => rulebigcommaToString(a, format)
             case RuleCuta(a) => rulecutToString(a, format)
             case RuleDispa(a) => ruledispToString(a, format)
             case RuleDispActa(a) => ruledispactToString(a, format)
             case RuleDispKa(a) => ruledispkToString(a, format)
             case RuleGrisha(a) => rulegrishToString(a, format)
             case RuleKnowledgea(a) => ruleknowledgeToString(a, format)
             case RuleOpa(a) => ruleopToString(a, format)
             case RuleOpActa(a) => ruleopactToString(a, format)
             case RuleOpKa(a) => ruleopkToString(a, format)
             case RuleStructa(a) => rulestructToString(a, format)
             case RuleStructActa(a) => rulestructactToString(a, format)
             case RuleStructEAa(a) => rulestructeaToString(a, format)
             case RuleStructKa(a) => rulestructkToString(a, format)
             case RuleSwapina(a) => ruleswapinToString(a, format)
             case RuleSwapouta(a) => ruleswapoutToString(a, format)
             case RuleZera(a) => rulezerToString(a, format)
             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)
			}
		case LATEX | ISABELLE_SE =>
			in match {
             case RuleBigcommaa(a) => rulebigcommaToString(a, format)
             case RuleCuta(a) => rulecutToString(a, format)
             case RuleDispa(a) => ruledispToString(a, format)
             case RuleDispActa(a) => ruledispactToString(a, format)
             case RuleDispKa(a) => ruledispkToString(a, format)
             case RuleGrisha(a) => rulegrishToString(a, format)
             case RuleKnowledgea(a) => ruleknowledgeToString(a, format)
             case RuleOpa(a) => ruleopToString(a, format)
             case RuleOpActa(a) => ruleopactToString(a, format)
             case RuleOpKa(a) => ruleopkToString(a, format)
             case RuleStructa(a) => rulestructToString(a, format)
             case RuleStructActa(a) => rulestructactToString(a, format)
             case RuleStructEAa(a) => rulestructeaToString(a, format)
             case RuleStructKa(a) => rulestructkToString(a, format)
             case RuleSwapina(a) => ruleswapinToString(a, format)
             case RuleSwapouta(a) => ruleswapoutToString(a, format)
             case RuleZera(a) => rulezerToString(a, format)
             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)
			}
		case ISABELLE =>
			in match {
             case RuleBigcommaa(a) => "(" + "RuleBigcomma" + " " + rulebigcommaToString(a, format) + ")"
             case RuleCuta(a) => "(" + "RuleCut" + " " + rulecutToString(a, format) + ")"
             case RuleDispa(a) => "(" + "RuleDisp" + " " + ruledispToString(a, format) + ")"
             case RuleDispActa(a) => "(" + "RuleDispAct" + " " + ruledispactToString(a, format) + ")"
             case RuleDispKa(a) => "(" + "RuleDispK" + " " + ruledispkToString(a, format) + ")"
             case RuleGrisha(a) => "(" + "RuleGrish" + " " + rulegrishToString(a, format) + ")"
             case RuleKnowledgea(a) => "(" + "RuleKnowledge" + " " + ruleknowledgeToString(a, format) + ")"
             case RuleOpa(a) => "(" + "RuleOp" + " " + ruleopToString(a, format) + ")"
             case RuleOpActa(a) => "(" + "RuleOpAct" + " " + ruleopactToString(a, format) + ")"
             case RuleOpKa(a) => "(" + "RuleOpK" + " " + ruleopkToString(a, format) + ")"
             case RuleStructa(a) => "(" + "RuleStruct" + " " + rulestructToString(a, format) + ")"
             case RuleStructActa(a) => "(" + "RuleStructAct" + " " + rulestructactToString(a, format) + ")"
             case RuleStructEAa(a) => "(" + "RuleStructEA" + " " + rulestructeaToString(a, format) + ")"
             case RuleStructKa(a) => "(" + "RuleStructK" + " " + rulestructkToString(a, format) + ")"
             case RuleSwapina(a) => "(" + "RuleSwapin" + " " + ruleswapinToString(a, format) + ")"
             case RuleSwapouta(a) => "(" + "RuleSwapout" + " " + ruleswapoutToString(a, format) + ")"
             case RuleZera(a) => "(" + "RuleZer" + " " + rulezerToString(a, format) + ")"
             case RuleMacro(a, pt) => rulemacroToString(a, pt, format)
			}
	}

/*print_calc_structure_rules-END*/

/*/*uncommentL?core_compiled-BEGIN*/*//*uncommentL?core_compiled-END*/
	def rulemacroToString(a : List[Char], pt : Prooftree, format : String = LATEX) : String = format match { 
		case ASCII => "Macro " + stringToString(a, format) + prooftreeToString(pt, format)
		case ISABELLE => "(RuleMacro " + stringToString(a, format) + prooftreeToString(pt, format) + ")"
		case LATEX => "Macro/" + stringToString(a, format)
	}

	def sequentToLatexString(seq:Sequent) = sequentToString(seq, LATEX)

	def prooftreeListToString(in:List[Prooftree], format:String = LATEX, sequentLatexPrint: Sequent => String = sequentToLatexString) : String = format match {
		case ASCII | ISABELLE => "[" + in.map(x => prooftreeToString(x, format, sequentLatexPrint)).mkString(", ") + "]"
		case LATEX => in.map(x => prooftreeToString(x, format, sequentLatexPrint)).mkString("\n")
		case ISABELLE_SE => in.map(x => prooftreeToString(x, format)).mkString("\n")
	}


	def prooftreeToString(in:Prooftree, format:String = LATEX, sequentLatexPrint: Sequent => String = sequentToLatexString) : String = format match {
		case ASCII =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "<==" + " (" + ruleToString(b, format) + ") " + prooftreeListToString(c, format, sequentLatexPrint) + ")"
			}
		case LATEX =>
			in match {
				case Prooftreea(a,b,List()) => "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\AxiomC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c)) => prooftreeToString(c, format, sequentLatexPrint) + "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\UnaryInfC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c, d)) => prooftreeListToString(List(c, d), format, sequentLatexPrint) + "\\RightLabel{ $" + ruleToString(b) + "$ }\n\\BinaryInfC{$ " + sequentLatexPrint(a)  + " $}"
				case Prooftreea(a,b,List(c, d, e)) => prooftreeListToString(List(c, d, e), format, sequentLatexPrint) + "\\TrinaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
				case Prooftreea(a,b,List(c, d, e, f)) => prooftreeListToString(List(c, d, e, f), format, sequentLatexPrint) + "\\QuaternaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
				case Prooftreea(a,b,list) => prooftreeListToString(list, format, sequentLatexPrint) + "\\QuinaryInfC{$ " + sequentLatexPrint(a)  + " $}\n"
			}
		case ISABELLE =>
			in match {
				case Prooftreea(a,b,c) => "(" + sequentToString(a, format) + " " + "\\<Longleftarrow>" + " " + "PT" + " " + ruleToString(b, format) + " " + prooftreeListToString(c, format, sequentLatexPrint) + ")"
			}
		case ISABELLE_SE =>
			in match {
				case Prooftreea(a,b,c) => "apply (rule_tac derivable." + ruleToString(b, format) + ")\n" + prooftreeListToString(c, format, sequentLatexPrint)
			}
	}
	
	/*def printCalcDef() : String = {
		val buf_Zer = scala.collection.mutable.ListBuffer.empty[String]
		val buf_U = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Op = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Disp = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Bin = scala.collection.mutable.ListBuffer.empty[String]
		val buf_Cut = scala.collection.mutable.ListBuffer.empty[String]

		for (r <- ruleList) {

			val loc = List(RelAKA((x => y => z => true)))
			val ret = prooftreeToString(Prooftreea(fst(rule(loc, r)), r, snd(rule(loc, r))))
			// val ant = fst(rule(r))
			// val cons = snd(rule(r))
			// ret ++= "$" + ruleToString(r) + "$\n"
			// if(cons.length == 1){
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
			// 	ret ++= "\\UnaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// else if(cons.length == 2){
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(0), LATEX) + " $}\n"
			// 	ret ++= "\\AxiomC{$ " + sequentToString(cons(1), LATEX) + " $}\n"
			// 	ret ++= "\\BinaryInfC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// else{
			// 	ret ++= "\\AxiomC{$ " + sequentToString(ant, LATEX) + " $}\n"
			// }
			// ret ++= "\n\\end{prooftree}"
			buf_Zer += ret
			// r match {
		 //        case RuleBina(a) => buf_Bin += ret.toString
		 //        case RuleCuta(a) => buf_Cut += ret.toString
		 //        case RuleDispa(a) => buf_Disp += ret.toString
		 //        case RuleOpa(a) => buf_Op += ret.toString
		 //        case RuleUa(a) => buf_U += ret.toString
		 //        case RuleZera(a) => buf_Zer += ret.toString
			// }
		}
		return "\\subsection{Zer Rules}\n" + buf_Zer.toList.mkString("\n") /*+
				"\\subsection{Unary Rules}\n" + buf_U.toList.mkString("\n") +
				"\\subsection{Display Rules}\n" + buf_Disp.toList.mkString("\n") +
				"\\subsection{Operational Rules}\n" + buf_Op.toList.mkString("\n") +
				"\\subsection{Binary Rules}\n" + buf_Bin.toList.mkString("\n") +
				"\\subsection{Cut Rules}\n" + buf_Cut.toList.mkString("\n")*/

	}
*/
/*uncommentR?core_compiled-BEGIN*//*/*uncommentR?core_compiled-END*/*/
}
