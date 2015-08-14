
import swing.{Button, ListView, FileChooser, Publisher}
import swing.event.Event

import scala.collection.mutable.ListBuffer

import javax.swing.filechooser.FileNameExtensionFilter
import javax.swing.Icon

import java.io.PrintWriter

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/
import PrintCalc._
import Parser._

case class PTChanged(valid : Boolean) extends Event
case class MacroAdded() extends Event

case class CalcSession() extends Publisher {

	/*/*uncommentL?Action?Agent-BEGIN*/*//*uncommentL?Action?Agent-END*/

	var relAKAMap : scala.collection.mutable.Map[Tuple2[Action, Agent], List[Action]] = scala.collection.mutable.Map()

	var preFormulaMap : scala.collection.mutable.Map[Action, Formula] = scala.collection.mutable.Map()

	var relAKAreflexive = true

	def relAKA(alpha : Action)(a : Agent) : List[Action] = relAKAMap.get((alpha, a)) match {
		case Some(h::list) =>
			// makes sure relAKA(a, x, a) is always true if relAKAreflexive is true
			if(alpha != h && list.indexOf(alpha) == -1 && relAKAreflexive) alpha::h::list
			else h::list
		case None => List(alpha)
	}

	def clearRelAKA() = {
		relAKAMap.clear()
	}

	def addRelAKA(a:Action, ag:Agent, a2:Action) = {
		val list = relAKAMap.getOrElse((a, ag), Nil)
		if(!list.contains(a2)) relAKAMap.put((a, ag), list++List(a2))
		println(relAKAMap((a, ag)))

		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def removeRelAKA(a:Action, ag:Agent, a2:Action):Unit = {
		val list = relAKAMap.getOrElse((a, ag), Nil)
		relAKAMap.put((a, ag), list.filter(_ != a2))
		println(relAKAMap((a, ag)))

		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def removeRelAKA(a:String, ag:String, a2:String):Unit = {
		val a_p = parseAction(a)
		val ag_p = parseAgent(ag)
		val a2_p = parseAction(a2)
		if(a_p != None && ag_p != None && a2_p != None) removeRelAKA(a_p.get, ag_p.get, a2_p.get)
	}

	//this function is used for dispalying relAKA in a table (typeset in latex)
	def flattenRelAKA():Array[Array[String]] = {
		val ret = new ListBuffer[Array[String]]()
		relAKAMap.foreach{
			case((a, ag), list) => 
				for (e <- list){
					ret += Array(actionToString(a), agentToString(ag), actionToString(e))
				}
		}
		ret.toArray
	}

	//this one is used for saving relAKA into json file
	def flattenRelAKAStr():List[List[String]] = {
		val ret = new ListBuffer[List[String]]()
		relAKAMap.foreach{
			case((a, ag), list) => 
				for (e <- list){
					ret += List(actionToString(a, PrintCalc.ASCII), agentToString(ag, PrintCalc.ASCII), actionToString(e, PrintCalc.ASCII))
				}
		}
		ret.toList
	}


	def clearPreForm() = {
		preFormulaMap.clear()
	}

	def addPreForm(a:Action, f:Formula) = {
		preFormulaMap.put(a, f)
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def removePreForm(a:Action):Unit = {
		preFormulaMap -= a
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def removePreForm(a:String):Unit = {
		val a_p = parseAction(a)
		if(a_p != None) removePreForm(a_p.get)
	}

	//this function is used for dispalying preFormMap in a table (typeset in latex)
	def flattenPreForm():Array[Array[String]] = {
		val ret = new ListBuffer[Array[String]]()
		preFormulaMap.foreach{
			case(a, f) =>  ret += Array(actionToString(a), formulaToString(f))
		}
		ret.toArray
	}

	//this function is used for saving preFormMap in a JSON file
	def flattenPreFormStr():List[List[String]] = {
		val ret = new ListBuffer[List[String]]()
		preFormulaMap.foreach{
			case(a, f) =>  ret += List(actionToString(a, PrintCalc.ASCII), formulaToString(f, PrintCalc.ASCII))
		}
		ret.toList
	}

	/*uncommentR?Action?Agent-BEGIN*//*/*uncommentR?Action?Agent-END*/*/

	var currentRuleList = ruleList

	var currentSequent : Sequent = Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a')))))

	private var _currentPT : Prooftree = Prooftreea( Sequenta(Structure_Formula(Formula_Atprop(Atpropa(List('a')))),Structure_Formula(Formula_Atprop(Atpropa(List('a'))))), RuleZera(Id()), List())
	
	def currentPT = _currentPT
	def currentPT_= (value:Prooftree):Unit = {
		_currentPT = value
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	var currentPTsel : Int = -1

	val assmsBuffer = ListBuffer[(Icon, Sequent)]()
	val ptBuffer = ListBuffer[(Icon, Prooftree)]()

	val macroBuffer = ListBuffer[(String, Prooftree)]()
	val abbrevMap = scala.collection.mutable.Map[String, String]()
	var abbrevsOn = true


	val listView = new ListView[(Icon, Sequent)]() {
		//maximumSize = new java.awt.Dimension(200, 300)
    	listData = assmsBuffer
    	renderer = ListView.Renderer(_._1)
  	}
  	val ptListView = new ListView[(Icon, Prooftree)]() {  
  		//maximumSize = new java.awt.Dimension(200, 300) 
    	listData = ptBuffer
    	renderer = ListView.Renderer(_._1)
    }

    val macroListView = new ListView[(String, Prooftree)]() {  
  		//maximumSize = new java.awt.Dimension(200, 300) 
    	listData = macroBuffer
    	renderer = ListView.Renderer(_._1)
    }

    def currentLocale : List[Locale] = {
    	val buff = ListBuffer[Locale]()
		buff ++= assmsBuffer.toList.map({case (i,s) => Premise(s)}) 
    	/*uncommentL?Action?Agent-BEGIN*//*/*uncommentL?Action?Agent-END*/*/
    	if (relAKAreflexive) buff += RelAKA(relAKA) 
    	/*uncommentR?Action?Agent-BEGIN*//*/*uncommentR?Action?Agent-END*/*/
		/*/*uncommentL?Action?Formula-BEGIN*/*//*uncommentL?Action?Formula-END*/
		buff ++= preFormulaMap.keys.toList.map{case a => PreFormula(a,preFormulaMap(a))}
		/*uncommentR?Action?Formula-BEGIN*//*/*uncommentR?Action?Formula-END*/*/
		if(buff.isEmpty) buff += Empty()
		buff.toList
    }

    var proofDepth = 5
	/*val addAssmButton = new Button {
		text = "Add assm"
	}
	val removeAssmButton = new Button {
		text = "Remove assm"
		enabled = false
	}

	val addPtButton = new Button {
		text = "Add PT"
		visible = false
	}
	val loadPTButton = new Button {
		text = "Load PT"
		enabled = false
	}
	val removePTsButton = new Button {
		text = "Remove PTs"
		enabled = false
	}*/

    def addAssm(seq:Sequent = currentSequent) = {
		val newAssm = (sequentToIcon(seq), seq)

		assmsBuffer.find(_._2 ==seq) match {
			case Some(r) => 
			case None => 
				assmsBuffer += newAssm
				listView.listData = assmsBuffer
				//if (!removeAssmButton.enabled) removeAssmButton.enabled = true
		}
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}
	
	def removeAssms() = {
		for (i <- listView.selection.items) assmsBuffer -= i
		listView.listData = assmsBuffer
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def reloadAssms() = {
		val assms = assmsBuffer.toList
		assmsBuffer.clear()
		for (i <- assms) addAssm(i._2)
	}

	def clearAssms() = {
		assmsBuffer.clear()
		listView.listData = assmsBuffer
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

    def addPT(pt: Prooftree = currentPT) = {
		val newPt = (ptToIcon(pt), pt)
		ptBuffer += newPt
		ptListView.listData = ptBuffer
		currentPTsel = ptBuffer.indexOf(newPt)

		//if (!removePTsButton.enabled) removePTsButton.enabled = true
		//if (!loadPTButton.enabled) loadPTButton.enabled = true
	}

	def removeMacros(pt:Prooftree = currentPT) = {
		addPT(expandProoftree(pt))
	}

	def savePT(ptSel: Int = currentPTsel, pt : Prooftree = currentPT) = {
		if (ptSel >= 0) {
			println("Saving")
			val sel : (Icon, Prooftree) = ptBuffer(ptSel)
			// if delete or add below was used, we want a new pt....
			if (concl(sel._2) == concl(pt)){
				val newPt = (sel._1, pt)
				ptBuffer.update(ptSel, newPt)
				ptListView.listData = ptBuffer
			} else {
				addPT(pt)
			}
		} else addPT(pt)
		//if (!removePTsButton.enabled) removePTsButton.enabled = true
		//if (!loadPTButton.enabled) loadPTButton.enabled = true
	}

	def loadPT() = {
		var sel = ptListView.selection.items.head
		currentPTsel = ptBuffer.indexOf(sel)
		currentPT = sel._2
		publish(PTChanged(isProofTreeWithCut(currentLocale, currentPT)))
	}

	def removePTs() = {
		val current = ptBuffer(currentPTsel)
		for (i <- ptListView.selection.items) {
			ptBuffer -= i
		}
		ptListView.listData = ptBuffer
		currentPTsel = ptBuffer.indexOf(current)
		/*if (ptListView.listData.isEmpty){
			removePTsButton.enabled = false
			loadPTButton.enabled = false
		}*/
	}

	def reloadPTs() = {
		val pts = ptBuffer.toList
		ptBuffer.clear()
		for (i <- pts) addPT(i._2)
	}

	def clearPT() = {
		ptBuffer.clear()
		currentPTsel = -1
		ptListView.listData = ptBuffer
	}

	def addAssmFromSelPT() : Unit = {
		var sel = ptListView.selection.items.head
		addAssm(concl(sel._2))
	}

	def exportLatexFromSelPT() : Unit = {
		var sel = ptListView.selection.items.head

		val chooser = new FileChooser(new java.io.File(".")) {
			title = "Save LaTeX File"
			fileFilter = new FileNameExtensionFilter("LaTeX (.tex)", "tex")
		}
		val result = chooser.showSaveDialog(null)
		if (result == FileChooser.Result.Approve) {
			val file = if (!chooser.selectedFile.toString.endsWith(".tex")) chooser.selectedFile.toString+".tex" else chooser.selectedFile.toString
			Some(new PrintWriter(file)).foreach{p =>
				//addPT(DEAK.expandProoftree(sel._2))
				if(abbrevsOn){
					def seqToStr(s:Sequent) = sequentToIconStr(s, abbrevMap.toMap)
					p.write(prooftreeToString(expandProoftree(sel._2), PrintCalc.LATEX, seqToStr) + "\\DisplayProof")
				}
		    	else p.write(prooftreeToString(expandProoftree(sel._2)) + "\\DisplayProof")
		    	p.close
		    }
		}

	}

	def rulifyPT() : Unit = {
		var sel = ptListView.selection.items.head
		val ptMacro = rulifyProoftree(sel._2)
		new MacroAddDialog(pt=ptMacro).rule match {
			case Some(str) => 
				if(str != ""){
					println(str)
					macroBuffer += Tuple2(str, ptMacro)

					println("Conclusion: "+sequentToString(concl(ptMacro), PrintCalc.ASCII))

					for (c <- collectPremises(ptMacro)){
						println("Prem: "+sequentToString(c, PrintCalc.ASCII))

					}
					macroListView.listData = macroBuffer

					//publish(MacroAdded())
				}
			case _ => println("cancel")
		}
		//val pt = rulifyProoftree(sel._2)
		//addPT(pt)
	}

	def ptToIcon(pt:Prooftree) : TeXIcon = {
		sequentToIcon(concl(pt))
	}

	def sequentToIcon(seq:Sequent, usingAbbrevs:Boolean = abbrevsOn, size:Int = 15) : TeXIcon = usingAbbrevs match {
		case false =>
			new TeXFormula(sequentToIconStr(seq)).createTeXIcon(TeXConstants.STYLE_DISPLAY, size)
		case true =>
			new TeXFormula(sequentToIconStr(seq, abbrevMap.toMap)).createTeXIcon(TeXConstants.STYLE_DISPLAY, size)
	}
		
    def sequentToIconStr(seq:Sequent, abbrevMap:Map[String, String] = Map()) : String = {
		var text = sequentToString(seq, PrintCalc.ASCII)
    	for(k <- abbrevMap.keys.toList.sortBy(abbrevMap(_).length).reverse)
    		if(text contains abbrevMap(k)) text = text.replaceAllLiterally(abbrevMap(k), k)

	    parseSequent(text) match {
	   		case Some(seq) => 
	   			var ret = sequentToString(seq)
	   			for(k <- abbrevMap.keys.toList.sortBy(_.length).reverse)
	   				if(ret contains k) ret = ret.replaceAllLiterally(k, "\\boldsymbol{"+scramble(k)+"}")
	   			for(k <- abbrevMap.keys.toList.sortBy(_.length).reverse)
	   				if(ret contains scramble(k)) ret = ret.replaceAllLiterally(scramble(k), k)
	   			ret
	   		case None => "error"
	   	}
    }

    def scramble(in:String) : String = {
    	val buf = new scala.collection.mutable.StringBuilder()
    	val l = in.length.toString
    	for (c <- in){
    		buf += c
    		buf ++= "randomtext"
    		buf ++= l
    	}
    	return buf.toString
    }

	def findMatches(seq: Sequent) : List[Prooftree] = for {
		(i, pt) <- ptBuffer.toList
		if concl(pt) == seq
	} yield pt

	def findMatchesMacro(seq: Sequent) : List[Prooftree] = for {
		(i, pt) <- ptBuffer.toList
		if replaceAll(match_Sequent(concl(pt), seq), concl(pt)) == seq
	} yield pt

	def mergePTs(repPt: Prooftree, insertPoint:SequentInPt, root:SequentInPt, children: SequentInPt => Iterable[SequentInPt]) : Prooftree = {
	    if(insertPoint == root) return repPt
	    return Prooftreea( root.seq, root.rule, children(root).toList.map(x => mergePTs(repPt, insertPoint, x, children)) )
	}

	def deleteAbove(deletePoint:SequentInPt, root:SequentInPt, children: SequentInPt => Iterable[SequentInPt]) : Prooftree = {
	    if(deletePoint == root) return Prooftreea(root.seq, RuleZera(Prem()), List())
	    return Prooftreea( root.seq, root.rule, children(root).toList.map( x => deleteAbove(deletePoint, x, children) ) )
	}

	def rebuildFromPoint(root:SequentInPt, children: SequentInPt => Iterable[SequentInPt]) : Prooftree = 
		return Prooftreea( root.seq, root.rule, children(root).toList.map( x => rebuildFromPoint(x, children) ) )

}