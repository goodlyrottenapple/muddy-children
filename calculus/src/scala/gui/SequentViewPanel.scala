import swing.{Action, Button, Component, Dialog, Swing, MenuItem, Graphics2D, ListView, GridPanel}
import swing.event.{ButtonClicked, MouseClicked}

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants}

import javax.swing.KeyStroke.getKeyStroke
import java.awt.event.KeyEvent
import java.awt.Color
import java.awt.Dimension

import java.awt.geom.Rectangle2D

import java.awt.Toolkit;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;


import scala.collection.JavaConversions._

import org.abego.treelayout.TreeLayout
import org.abego.treelayout.util.{DefaultConfiguration, DefaultTreeForTreeLayout}

/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/
import PrintCalc._
import Proofsearch._


case class SequentViewPanel(sequent : Sequent, gapBetweenLevels:Int = 10, gapBetweenNodes:Int = 10, editable : Boolean = false) extends scala.swing.Panel {
	val configuration = new DefaultConfiguration[StructureInPt](gapBetweenLevels, gapBetweenNodes, org.abego.treelayout.Configuration.Location.Top)
	val nodeExtentProvider = new StructureInPtNodeExtentProvider()

	// create the layout
	//println("abbrevMAP:")
	//println(session.abbrevMap.toMap)
	var treeLayout = new TreeLayout[StructureInPt](createSequentTree(sequent), nodeExtentProvider, configuration)

	val OFFSET_X = 20
	val OFFSET_Y = 20

	peer.setLayout(null)
	border = Swing.EmptyBorder(10, 10, 10, 10)


	preferredSize = new Dimension(treeLayout.getBounds().getBounds().getSize().width+2*OFFSET_X, treeLayout.getBounds().getBounds().getSize().height+2*OFFSET_Y)

	var currentSequent = sequent

	def tree = treeLayout.getTree()

	def children(parent:StructureInPt) : Iterable[StructureInPt] = tree.getChildren(parent)

	def boundsOfNode(node:StructureInPt) : Rectangle2D.Double = treeLayout.getNodeBounds().get(node)

	listenTo(mouse.clicks)
	reactions += {
		case ButtonClicked(b) if editable =>
			
			unselect()
			val pressed = b.asInstanceOf[StructureInPt]
			if(pressed.selectable){
				pressed.border = Swing.LineBorder(Color.black)
				pressed.sel = true
			}
			//val b1 = boundsOfNode(pressed)
			//popup.peer.show(b.peer, OFFSET_X, OFFSET_Y)

		case m : MouseClicked => 
			//selectedSequentInPt = None
			println("unselect")
			unselect()

	}


	def unselect(root:StructureInPt = tree.getRoot) : Unit = {
		root.border = Swing.EmptyBorder(0,0,0,0)
		root.sel = false

		for (child <- children(root)) {
			unselect(child)
		}

	}

	def createSequentTreeAux(structure:Structure, size:Int=20, tree:DefaultTreeForTreeLayout[StructureInPt], root:StructureInPt) : Unit = structure match {
		/*/*uncommentL?Structure_Formula-BEGIN*/*//*uncommentL?Structure_Formula-END*/
		case Structure_Formula(f) =>
    		val l = new StructureInPt(Some( Structure_Formula(f) ), size, formulaToString(f))
	   		tree.addChild(root, l)
		/*uncommentR?Structure_Formula-BEGIN*//*/*uncommentR?Structure_Formula-END*/*/
	   	/*/*uncommentL?Structure_Bin-BEGIN*/*//*uncommentL?Structure_Bin-END*/
		case Structure_Bin(lhs, op, rhs) =>
	   		val l = new StructureInPt(Some( Structure_Bin(lhs, op, rhs) ), size, structure_bin_opToString(op))
	   		tree.addChild(root, l)
	   		createSequentTreeAux(lhs, size, tree, l)
	   		createSequentTreeAux(rhs, size, tree, l)
	   	/*uncommentR?Structure_Bin-BEGIN*//*/*uncommentR?Structure_Bin-END*/*/
	   	/*/*uncommentL?Structure_Action_Structure-BEGIN*/*//*uncommentL?Structure_Action_Structure-END*/
	   	case Structure_Action_Structure(op, ac, s) =>
	   		val l = new StructureInPt(Some( Structure_Action_Structure(op, ac, s)  ), size, structure_action_structure_opToString(op, PrintCalc.ASCII))
	   		tree.addChild(root, l)
	   		val action = new StructureInPt(Some( Structure_Formula(Formula_Action(ac))  ), size, actionToString(ac))
	   		tree.addChild(l, action)
	   		createSequentTreeAux(s, size, tree, l)
	   	/*uncommentR?Structure_Action_Structure-BEGIN*//*/*uncommentR?Structure_Action_Structure-END*/*/
	   	/*/*uncommentL?Structure_Agent_Structure-BEGIN*/*//*uncommentL?Structure_Agent_Structure-END*/
	   	case Structure_Agent_Structure(op, ag, s) =>
	   		val l = new StructureInPt(Some( Structure_Agent_Structure(op, ag, s)  ), size, structure_agent_structure_opToString(op, PrintCalc.ASCII))
	   		tree.addChild(root, l)
	   		val agent = new StructureInPt(Some( Structure_Formula(Formula_Agent(ag))  ), size, agentToString(ag))
	   		tree.addChild(l, agent)
	   		createSequentTreeAux(s, size, tree, l)
	   	/*uncommentR?Structure_Agent_Structure-BEGIN*//*/*uncommentR?Structure_Agent_Structure-END*/*/
	   	/*/*uncommentL?Structure_Phi-BEGIN*/*//*uncommentL?Structure_Phi-END*/
	   	case Structure_Phi(ac) =>
	   		val l = new StructureInPt(Some( Structure_Phi(ac) ), size, structureToString(Structure_Phi(ac)))
	   		tree.addChild(root, l)
	   	/*uncommentR?Structure_Phi-BEGIN*//*/*uncommentR?Structure_Phi-END*/*/
	   	/*/*uncommentL?Structure_Zer-BEGIN*/*//*uncommentL?Structure_Zer-END*/
	   	case Structure_Zer(op) =>
	   		val l = new StructureInPt(Some( Structure_Zer(op) ), size, structure_zer_opToString(op))
	   		tree.addChild(root, l)
	   	/*uncommentR?Structure_Zer-BEGIN*//*/*uncommentR?Structure_Zer-END*/*/
	   	/*/*uncommentL?Structure_Bigcomma-BEGIN*/*//*uncommentL?Structure_Bigcomma-END*/
	   	case Structure_Bigcomma(list) =>
	   		val l = new StructureInPt(Some( Structure_Bigcomma(list) ), size, ";;")
	   		tree.addChild(root, l)
	   		list.foreach{ x => createSequentTreeAux(x, size, tree, l) }
	   	/*uncommentR?Structure_Bigcomma-BEGIN*//*/*uncommentR?Structure_Bigcomma-END*/*/
	   	case _ => 
	}

	def createSequentTree(seq: Sequent, size:Int=20)  : DefaultTreeForTreeLayout[StructureInPt] = seq match {
		case Sequenta(lhs, rhs) => {
    		val root = new StructureInPt(None, size, "\\vdash", false)
    		val tree = new DefaultTreeForTreeLayout[StructureInPt](root)
    		createSequentTreeAux(lhs, size, tree, root)
    		createSequentTreeAux(rhs, size, tree, root)
    		return tree
    	}
	}

	def rebuildSeqent(root:StructureInPt, repl:Structure = Structure_Formula(Formula_Atprop( Atpropa(List('X')) )) ) : Option[ Tuple2[Sequent, Option[Structure]] ] = {
		val it = children(root).iterator
		val lhs_StructureInPt = it.next()
		val rhs_StructureInPt = it.next()

		val lhs_new = rebuildStructure(lhs_StructureInPt, repl).getOrElse( Tuple2(lhs_StructureInPt.struct.getOrElse(repl),  None) )
		val rhs_new = rebuildStructure(rhs_StructureInPt, repl).getOrElse( Tuple2(rhs_StructureInPt.struct.getOrElse(repl),  None) )

		val new_repl = if (!lhs_new._2.isEmpty) lhs_new._2 else rhs_new._2
		return Some( Tuple2(Sequenta(lhs_new._1, rhs_new._1), new_repl ) )
	}


	def rebuildStructure(root:StructureInPt, repl:Structure = Structure_Formula(Formula_Atprop( Atpropa(List('X')) )) ) : Option[ Tuple2[Structure, Option[Structure]] ] = {
		if(root.sel) return Some( Tuple2(repl, root.struct) )
		else{

			root.struct match {
				case Some(s) => s match {
				   	/*/*uncommentL?Structure_Bin-BEGIN*/*//*uncommentL?Structure_Bin-END*/
					case Structure_Bin(lhs, op, rhs) =>
				   		// val l = new StructureInPt(Some( Structure_Bin(lhs, op, rhs) ), size, structure_bin_opToString(op))
				   		val it = children(root).iterator
				   		val lhs_StructureInPt = it.next()
				   		val rhs_StructureInPt = it.next()

				   		val lhs_new = rebuildStructure(lhs_StructureInPt, repl).getOrElse( Tuple2(lhs_StructureInPt.struct.getOrElse(repl),  None) )
				   		val rhs_new = rebuildStructure(rhs_StructureInPt, repl).getOrElse( Tuple2(rhs_StructureInPt.struct.getOrElse(repl),  None) )
				   		val new_repl = if (!lhs_new._2.isEmpty) lhs_new._2 else rhs_new._2
				   		return Some( Tuple2(Structure_Bin(lhs_new._1, op, rhs_new._1), new_repl ) )
				   	/*uncommentR?Structure_Bin-BEGIN*//*/*uncommentR?Structure_Bin-END*/*/
				   	/*/*uncommentL?Structure_Action_Structure-BEGIN*/*//*uncommentL?Structure_Action_Structure-END*/
				   	case Structure_Action_Structure(op, ac, s) =>
				   	//children(root).next()
					   	val it = children(root).iterator
					   	it.next()
				   		val s_StructureInPt = it.next()

				   		val s_new = rebuildStructure(s_StructureInPt, repl).getOrElse( Tuple2(s_StructureInPt.struct.getOrElse(repl),  None) )
				   		return Some( Tuple2(Structure_Action_Structure(op, ac, s_new._1), s_new._2 ) )
				   	/*uncommentR?Structure_Action_Structure-BEGIN*//*/*uncommentR?Structure_Action_Structure-END*/*/
				   	/*/*uncommentL?Structure_Agent_Structure-BEGIN*/*//*uncommentL?Structure_Agent_Structure-END*/
				   	case Structure_Agent_Structure(op, ag, s) =>
				   		val it = children(root).iterator
					   	it.next()
				   		val s_StructureInPt = it.next()

				   		val s_new = rebuildStructure(s_StructureInPt, repl).getOrElse( Tuple2(s_StructureInPt.struct.getOrElse(repl),  None) )
				   		return Some( Tuple2(Structure_Agent_Structure(op, ag, s_new._1), s_new._2 ) )
				   	/*uncommentR?Structure_Agent_Structure-BEGIN*//*/*uncommentR?Structure_Agent_Structure-END*/*/
				   	case x =>
				   		return Some( Tuple2(x, None) )
				}

				case None => return None

			}

		}
	}

	

	// def update() = {
	// 	peer.removeAll()
	// 	treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)
	// 	build()
	// 	peer.revalidate()
	// 	peer.repaint()
	// 	val s = treeLayout.getBounds().getBounds().getSize()
	// 	preferredSize = new java.awt.Dimension(s.width + OFFSET_X*8, s.height + OFFSET_Y*2)
	// }

	protected def add(comp: Component, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)
		//comp.ruleButton.peer.setLocation(x+p.getPreferredSize.width+OFFSET_X, y+OFFSET_Y-p.getPreferredSize.height/2)
		//comp.ruleButton.peer.setSize(comp.ruleButton.peer.getPreferredSize)
		p.setSize(p.getPreferredSize)
		peer.add(p)
		listenTo(comp)

	}

	override def repaint() = {
		peer.removeAll()
		val old = treeLayout.getTree()
		treeLayout = new TreeLayout[StructureInPt](old, nodeExtentProvider, configuration)
		build()
		peer.revalidate()
		peer.repaint()
		val s = treeLayout.getBounds().getBounds().getSize()
		preferredSize = new java.awt.Dimension(s.width + OFFSET_X*8, s.height + OFFSET_Y*2)
	}

	def rebuild() = {
		peer.removeAll()
		treeLayout = new TreeLayout[StructureInPt](createSequentTree(currentSequent), nodeExtentProvider, configuration)
		build()
		peer.revalidate()
		peer.repaint()
		val s = treeLayout.getBounds().getBounds().getSize()
		preferredSize = new java.awt.Dimension(s.width + OFFSET_X*8, s.height + OFFSET_Y*2)
	}

	def build() = {
		for (structureInPt <- treeLayout.getNodeBounds().keySet()) {
			val box = boundsOfNode(structureInPt)
			add(structureInPt, (box.x).toInt, (box.y).toInt)
		}
	}

	def paintEdges(g:Graphics2D, parent:StructureInPt) : Unit = {
		val b1 = boundsOfNode(parent)
		val y_p = (b1.getMaxY()).toInt
		var xmin = (b1.getMinX()).toInt
		var xmax = (b1.getMaxX()).toInt //+15
		val x_p = (xmin + xmax) /2


		for (child <- children(parent)) { 
			val b2 = boundsOfNode(child)
			val y_c = (b2.getMinY()).toInt
			xmin = (b2.getMinX()).toInt
			xmax = (b2.getMaxX()).toInt
			val x_c = (xmin + xmax) /2

			g.drawLine( x_p+OFFSET_X, y_p+OFFSET_Y, x_c+OFFSET_X, y_c+OFFSET_Y )
			paintEdges(g, child)
		}

		//g.drawLine( xmin, y, xmax+15, y )
		//g.drawLine( xmin+OFFSET_X, y+OFFSET_Y, xmax+OFFSET_X, y+OFFSET_Y )
		//parent.ruleIcon.paintIcon(null, g, xmax+5+OFFSET_X, y-(parent.ruleIcon.getIconHeight/2)+OFFSET_Y)
		//g.drawString(parent.strule, xmax+5+OFFSET_X, y+5+OFFSET_Y)
	}


	override def paintComponent(g: Graphics2D) = {
		super.paintComponent(g)
		paintEdges(g, tree.getRoot())
    }
}

class StructureInPtNodeExtentProvider extends org.abego.treelayout.NodeExtentProvider[StructureInPt] {
	def getWidth(treeNode:StructureInPt) = treeNode.width
	def getHeight(treeNode:StructureInPt) = treeNode.height
}

case class StructureInPt(struct:Option[Structure], iconSize:Int = 15, latex:String = "", selectable:Boolean = true) extends Button{

	val latXForm = new TeXFormula(latex)
    icon = latXForm.createTeXIcon(TeXConstants.STYLE_DISPLAY, iconSize)

  
  // val macroPtPanel = rule match {
  //   case RuleMacro(s, pt) => 
  //     val macroSession = CalcSession()
  //     macroSession.currentPT = pt
  //     macroSession.abbrevsOn = session.abbrevsOn
  //     macroSession.abbrevMap ++= session.abbrevMap.toMap
  //     val ptPanel = new ProofTreePanel(session=macroSession, editable=false)
  //     ptPanel.build()
  //     //contents+= ptPanel
  //     //preferredSize = ptPanel.preferredSize
  //     Some(ptPanel)
  //   case _ => 
  //     None
  // }

  // val ruleIcon = cutFormula match {
  //     case None => 
  //       val ruleTex = new TeXFormula(ruleToString(rule))
  //       ruleTex.createTeXIcon(TeXConstants.STYLE_DISPLAY, .7f*size)
  //     case Some(form) =>
  //       val ruleTex = new TeXFormula(ruleToString(rule) + "(" + formulaToString(form) +")")
  //       ruleTex.createTeXIcon(TeXConstants.STYLE_DISPLAY, .7f*size)
  //   }
  //   //peer.setIcon(i)

  // val ruleButton = rule match {
  //   case RuleMacro(str, prooftree) => new RuleInPtButton(pt=Some(prooftree), p=this)
  //   case _ => new RuleInPtButton(enabled=false)
  // }

  // ruleButton.peer.setIcon(ruleIcon)
  // ruleButton.peer.setBorder(Swing.EmptyBorder(0, 0, 0, 0))


	var sel = false
	
	//text = seq.toString
	border = Swing.EmptyBorder(0, 0, 0, 0)
	// val s = new Dimension(width, height)
	// //minimumSize = s
 //  //maximumSize = s
 //  preferredSize = s
  //peer.setHorizontalAlignment(SwingConstants.LEFT)

  //preferredSize.width = icon.getIconWidth

  def width: Int =  icon.getIconWidth//+ruleIcon.getIconWidth//()//+5
 
  def height: Int = icon.getIconHeight

}
