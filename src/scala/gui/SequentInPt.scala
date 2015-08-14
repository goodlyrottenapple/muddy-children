import swing.{Button, Swing, GridPanel}

import java.awt.Dimension
import javax.swing.SwingConstants

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants}

/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/
import PrintCalc.{sequentToString, formulaToString, ruleToString}
import Parser.parseSequent

class SequentInPt(val seq:Sequent, val rule:Rule, size:Int = 15, val cutFormula:Option[Formula] = None, 
  session:CalcSession = CalcSession()) extends GridPanel(1,1)
 {
  opaque = false
	//val latXForm = new TeXFormula(sequentToString(seq))
    //icon = latXForm.createTeXIcon(TeXConstants.STYLE_DISPLAY, size)
  val icon = session.sequentToIcon(seq)

  val seqButton = new SequentInPtButton(p=this)
  seqButton.peer.setBorder(Swing.EmptyBorder(0, 0, 0, 0))
  seqButton.peer.setOpaque(false)
  seqButton.peer.setIcon(icon)

  contents+= seqButton

  
  val macroPtPanel = rule match {
    case RuleMacro(s, pt) => 
      val macroSession = CalcSession()
      macroSession.currentPT = pt
      macroSession.abbrevsOn = session.abbrevsOn
      macroSession.abbrevMap ++= session.abbrevMap.toMap
      val ptPanel = new ProofTreePanel(session=macroSession, editable=false)
      ptPanel.build()
      //contents+= ptPanel
      //preferredSize = ptPanel.preferredSize
      Some(ptPanel)
    case _ => 
      None
  }

  val ruleIcon = cutFormula match {
      case None => 
        val ruleTex = new TeXFormula(ruleToString(rule))
        ruleTex.createTeXIcon(TeXConstants.STYLE_DISPLAY, .7f*size)
      case Some(form) =>
        val ruleTex = new TeXFormula(ruleToString(rule) + "(" + formulaToString(form) +")")
        ruleTex.createTeXIcon(TeXConstants.STYLE_DISPLAY, .7f*size)
    }
    //peer.setIcon(i)

  val ruleButton = rule match {
    case RuleMacro(str, prooftree) => new RuleInPtButton(pt=Some(prooftree), p=this)
    case _ => new RuleInPtButton(enabled=false)
  }

  ruleButton.peer.setBorder(Swing.EmptyBorder(0, 0, 0, 0))
  ruleButton.peer.setOpaque(false)
  ruleButton.peer.setIcon(ruleIcon)
	
	border = Swing.EmptyBorder(0, 0, 0, 0)

  def width: Int = {
    if (contents.contains(seqButton)) icon.getIconWidth//+ruleIcon.getIconWidth//()//+5
    else macroPtPanel.get.preferredSize.width
  }
  def height: Int = {
    if (contents.contains(seqButton)) icon.getIconHeight
    else macroPtPanel.get.preferredSize.height
  }

  seqButton.preferredSize = new Dimension(width, height)

}

class SequentInPtButton(enabled: Boolean = true, p:SequentInPt = null) extends Button {
  opaque = false
  val parent = p
  text = "sequent"
  peer.setHorizontalAlignment(SwingConstants.LEFT)
  peer.setEnabled(enabled)
}

class RuleInPtButton(val pt:Option[Prooftree] = None, enabled: Boolean = true, p:SequentInPt = null) extends Button {
  opaque = false
  val parent = p
  text = "rule"
  peer.setHorizontalAlignment(SwingConstants.LEFT)
  val str = "aaaa"
  peer.setEnabled(enabled)
}