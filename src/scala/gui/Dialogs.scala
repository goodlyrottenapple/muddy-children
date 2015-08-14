import swing._
import swing.event.{KeyReleased, Key, SelectionChanged}
import swing.BorderPanel.Position._
import swing.ListView.IntervalMode
import javax.swing.Icon

import swing.event.WindowOpened

import scala.concurrent._
import ExecutionContext.Implicits.global
import java.util.concurrent.atomic.AtomicReference

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/
import Parser._
import PrintCalc._
import Proofsearch.derTree

class SequentListDialog(owner: Window = null, list : List[(Rule, List[Sequent])], session:CalcSession = CalcSession()) extends Dialog(owner) {
  var pair:Option[(Rule, List[Sequent])] = None
  modal = true

  val listView = new ListView[(Icon, Rule, List[Sequent])]() {   
    listData = for((r,l) <- list) yield (new TeXFormula(ruleToString(r) + " - "+ l.map( session.sequentToIconStr(_, session.abbrevMap.toMap) ).mkString(", ")).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15), r, l)
    renderer = ListView.Renderer(_._1)
    selection.intervalMode = IntervalMode.Single
  }

  val b = new Button("Select Sequent") { 
    enabled = false 
  } 

  listenTo(listView.selection, listView.keys)
  reactions += {
    case KeyReleased(s, Key.Enter, _, _) => if(b.enabled) close()
    case SelectionChanged(`listView`) =>
      val sel = listView.selection.items(0)
      pair = Some((sel._2, sel._3))
      if(!b.enabled){
        b.enabled = true
        b.action = Action("Select Sequent"){close()}
      }
  }

  contents = new BorderPanel {
    layout(new Label("Select a rule to apply:")) = North

    layout(listView) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( b )) = South
  }

  centerOnScreen()
  open()
}

class FormulaInputDialog(owner: Window = null) extends Dialog(owner) {
  var formula:Option[Formula] = None
  modal = true

  val in = new TextField { 
    text = ""
    columns = 25
    //horizontalAlignment = Alignment.Right
  }
  
  val inL = new Label

  listenTo(in.keys)
  reactions += {
    case KeyReleased(`in`, k, _, _) =>
      parseFormula(in.text) match {
        case Some(r) =>
          formula = Some(r)
          val latex = formulaToString(r)
          inL.icon = new TeXFormula(latex).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
        case None => ;
      }
  }

  contents = new BorderPanel {
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(5,5,5,5)

      contents += in
      contents += inL
    }) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( Button("Use Formula") { close() } )) = South
  }

  centerOnScreen()
  open()
}



class AgentInputDialog(owner: Window = null) extends Dialog(owner) {
  var agent:Option[Agent] = None
  modal = true

  val in = new TextField { 
    text = ""
    columns = 25
    //horizontalAlignment = Alignment.Right
  }
  
  val inL = new Label

  listenTo(in.keys)
  reactions += {
    case KeyReleased(`in`, k, _, _) =>
      parseAgent(in.text) match {
        case Some(r) =>
          agent = Some(r)
          val latex = agentToString(r)
          inL.icon = new TeXFormula(latex).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
        case None => ;
      }
  }

  contents = new BorderPanel {
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(5,5,5,5)

      contents += in
      contents += inL
    }) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( Button("Use Agent") { close() } )) = South
  }

  centerOnScreen()
  open()
}

class SequentInputDialog(owner: Window = null) extends Dialog(owner) {
  var sequent:Option[Sequent] = None
  modal = true

  val in = new TextField { 
    text = ""
    columns = 25
    //horizontalAlignment = Alignment.Right
  }
  
  val inL = new Label

  listenTo(in.keys)
  reactions += {
    case KeyReleased(`in`, Key.Enter, _, _) =>
      close()
    case KeyReleased(`in`, k, m, _) =>
      parseSequent(in.text) match {
        case Some(r) =>
          sequent = Some(r)
          val latex = sequentToString(r)
          inL.icon = new TeXFormula(latex).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
        case None => ;
      }

  }

  contents = new BorderPanel {
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(5,5,5,5)

      contents += in
      contents += inL
    }) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( Button("Use Sequent") { close() } )) = South
  }

  centerOnScreen()
  open()
}

class RuleSelectDialog(owner: Window = null, list : List[(Rule, List[Sequent])] ) extends Dialog(owner) {
  var pair:Option[(Rule, List[Sequent])] = None
  modal = true

  val listView = new ListView[(Icon, Rule, List[Sequent])]() {   
    listData = for((r,l) <- list) yield (new TeXFormula(ruleToString(r)).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15), r, l)
    renderer = ListView.Renderer(_._1)
    selection.intervalMode = IntervalMode.Single
  }

  val b = new Button("Select Rule") { 
    enabled = false 
  } 

  listenTo(listView.selection)
  reactions += {
    case SelectionChanged(`listView`) =>
      val sel = listView.selection.items(0)
      pair = Some((sel._2, sel._3))
      if(!b.enabled){
        b.enabled = true
        b.action = Action("Select Rule"){close()}
      }
  }

  contents = new BorderPanel {
    layout(new Label("Select a rule to apply:")) = North

    layout(listView) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( b )) = South
  }

  centerOnScreen()
  open()
}



class PSDialog(owner: Window = null, locale : List[Locale] = List(Empty()), seq : Sequent, depth : Int = 5, useRules : List[Rule] = ruleList) extends Dialog(owner) {


  // the following code (interruptableFuture) is from http://stackoverflow.com/questions/16020964/cancellation-with-future-and-promise-in-scala

  def interruptableFuture[T](fun: () => T)(implicit ex: ExecutionContext): (Future[T], () => Boolean) = {
    val p = Promise[T]()
    val f = p.future
    val aref = new AtomicReference[Thread](null)
    p tryCompleteWith Future {
      val thread = Thread.currentThread
      aref.synchronized { aref.set(thread) }
      try fun() finally {
        val wasInterrupted = (aref.synchronized { aref getAndSet null }) ne thread
        //Deal with interrupted flag of this thread in desired
      }
    }

    (f, () => {
      aref.synchronized { Option(aref getAndSet null) foreach { _.interrupt() } }
      p.tryFailure(new CancellationException)
    })
  }


  var pt:Option[Prooftree] = None
  modal = true

  var cancel :() => Boolean = {() => true}

  
  listenTo(this)
  reactions += {
    case WindowOpened(_) =>
      val (f, c) = interruptableFuture[Option[Prooftree]] { () =>
        derTree(depth, locale, seq, 0, useRules)
      }

      cancel = c

      f.onSuccess {
        case result =>
          pt = result
          close()
      }

      f.onFailure { 
        case ex => 
          println(ex.getClass)
          close()
      }
  }

  override def closeOperation { 
    cancel()
    super.closeOperation  
  }

  contents = new BorderPanel {
    layout(new BoxPanel(Orientation.Horizontal) {
      border = Swing.EmptyBorder(5,5,5,5)
      contents += new Label("Searching for a Prooftree...  ")
      contents += new ProgressBar{
        indeterminate = true
      }
    }) = Center

    layout(new FlowPanel(FlowPanel.Alignment.Right)( Button("Cancel") { cancel(); close() } )) = South
  }

  centerOnScreen()

  open()

}



class MacroAddDialog(owner: Window = null, pt : Prooftree, adding : Boolean = true, macroName : String = "", abbrevs : Option[Map[String, String]] = None, editable : Boolean = false) extends Dialog(owner) {

  var rule : Option[String] = None

  val session = CalcSession()
  session.currentPT = pt
  if(abbrevs.isDefined) {
    session.abbrevMap ++= abbrevs.get
    session.abbrevsOn = true
  }

  preferredSize = new java.awt.Dimension(400, 300)
  
  val ptPanel = new ProofTreePanel(session= session, editable=editable)
  ptPanel.build()

  modal = true

  val in = new TextField { 
    text = ""
    columns = 25
    //horizontalAlignment = Alignment.Right
  }

  contents = new BorderPanel {

    if (adding) layout(new Label("Save selected PT as macro?")) = North
    else layout(new Label("Macro " + macroName)) = North
    layout(new ScrollPane(ptPanel){border = Swing.EmptyBorder(0, 0, 0, 0)}) = Center

    if (adding) {
      layout(new BoxPanel(Orientation.Horizontal) {
        border = Swing.EmptyBorder(5,5,5,5)
        contents += new Label("Macro name:")
        contents += in
        contents += Button("Save") { rule = Some(in.text); close() } 
        contents += Button("Cancel") { close() } 
      }) = South
    }
    //layout(new FlowPanel(FlowPanel.Alignment.Right)( )) = South
  }

  centerOnScreen()

  open()

}

class SequentTreeViewDialog(owner: Window = null, sequent : Sequent, selecting:Boolean = false) extends Dialog(owner) {

  preferredSize = new java.awt.Dimension(400, 300)
  
  val seqPanel = new SequentViewPanel(sequent=sequent, editable=selecting)
  seqPanel.build()

  modal = selecting

  lazy val fresh = sequent_fresh_name(seqPanel.sequent)
  var tuple:Option[(Sequent, Option[Structure])] = None

  
  contents = new BorderPanel {
    layout(new ScrollPane(seqPanel){border = Swing.EmptyBorder(0, 0, 0, 0)}) = Center
    if(selecting) layout( Button("Display Selected") { tuple = seqPanel.rebuildSeqent(seqPanel.tree.getRoot(), fresh); close() }  ) = South
  }

  centerOnScreen()

  open()

}


