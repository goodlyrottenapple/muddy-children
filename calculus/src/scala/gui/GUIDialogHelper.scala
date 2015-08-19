import swing.{BorderPanel, BoxPanel, FlowPanel, GridPanel, Panel, Button, Label, Swing, ProgressBar, Orientation, TextField, Table}
import swing.event._

import swing.BorderPanel.Position._

import scala.collection.JavaConversions._
import scala.collection.mutable.ListBuffer

import java.awt.event.{MouseEvent, KeyEvent, ActionEvent}
import javax.swing.{BorderFactory, JPanel, JComponent, KeyStroke, AbstractAction}
import javax.swing.plaf.basic._

import java.awt.{Toolkit, Font, Color, FileDialog, Dimension}
import java.awt.datatransfer.Clipboard
import java.awt.datatransfer.StringSelection

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



class ProofSearchPopup(locale : List[Locale] = List(Empty()), seq : Sequent, depth : Int = 5, useRules : List[Rule] = ruleList) extends BorderPanel with Popup {
	
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
	var cancel :() => Boolean = {() => true}
	var cancelled = false


	def open() = {

		focusable = true
		requestFocus

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

	override def close():Unit = {
		cancel()
		visible = false
	}

	background = new Color(238,238,238)
	border = Swing.EmptyBorder(15,15,15,15)

	layout(new BoxPanel(Orientation.Vertical) {
		contents += new Label("PROOF SEARCH") {
			font = new Font("Roboto-Bold", Font.BOLD, 16)
			foreground = new Color(33,33,33)
		}
		contents += new Label("Searching for a prooftree") {
			font = new Font("Roboto-Light", Font.PLAIN, 12)
			border = Swing.EmptyBorder(15,0,15,0)
			foreground = new Color(33,33,33)
		}
		contents += new ProgressBar{
			border = Swing.EmptyBorder(0,5,0,5)
			indeterminate = true
		}
		opaque = false
	}) = Center

	val cancelButton = new Button(swing.Action("Cancel popup") { cancelled = true; close() }) {
		text = "CANCEL"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(15, 0, 0, 0)
		foreground = new Color(66,133,244)
	}

	listenTo(keys)
	reactions += {
		case KeyReleased(_, Key.Escape, _, _) =>
			cancelled = true; close()
	}

	focusable = true

	layout(new FlowPanel(FlowPanel.Alignment.Right)( cancelButton ){opaque = false}) = South

}

class ErrorPopup(message:String) extends BorderPanel with Popup {
	override def close() = {
		visible = false
	}

	background = new Color(238,238,238)
	border = Swing.EmptyBorder(15,15,15,15)

	layout(new BoxPanel(Orientation.Vertical) {
		//border = Swing.EmptyBorder(5,5,5,5)
		contents += new Label("ERROR") {
			font = new Font("Roboto-Bold", Font.BOLD, 16)
			foreground = new Color(33,33,33)
		}
		contents += new Label(message) {
			font = new Font("Roboto-Light", Font.PLAIN, 12)
			border = Swing.EmptyBorder(15,0,15,0)
			foreground = new Color(33,33,33)
		}
		opaque = false
	}) = Center

	val okButton = new Button(swing.Action("Close popup") { close() }) {
		text = "OK"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 0)
		foreground = new Color(66,133,244)
	}
	

	listenTo(keys)
	reactions += {
		case KeyReleased(_, Key.Escape, _, _) | KeyReleased(_, Key.Enter, _, _) =>
			close()
	}

	focusable = true

	layout(new FlowPanel(FlowPanel.Alignment.Right)( okButton ){opaque = false}) = South //{ cancel(); close() } )) = South
}


class ParsePopup[T](parser:String => Option[T], toStr:T => String, t:String) extends BorderPanel with Popup {
	override def close() = {
		visible = false
	}

	val parsedBottomBarColor = new Color(51,172,113)
	val unParsedBottomBarColor = new Color(255,139,129)

	background = parsedBottomBarColor
	border = Swing.EmptyBorder(15,15,15,15)



	val inputField = new TextField {
		columns = 25
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		//minimumSize = new Dimension(350, 50)
		//maximumSize = new Dimension(800, 50)
		//preferredSize = new Dimension(800, 50)
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
		focusable = true
	}

	val parsedStrIcon = new Label {
		icon = new TeXFormula("").createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
		foreground = Color.white
	}

	val parsedStrIcon_aux = new BorderPanel{
		layout (parsedStrIcon) = Center
		background = parsedBottomBarColor
	}

	val parsedStrIconScrollPane = new PrettyScrollPane(parsedStrIcon_aux){
		preferredSize = new Dimension(300, 50)
	}

	var parsed:Option[T] = None

	listenTo(inputField.keys, keys)
	reactions += {
		case KeyReleased(_, Key.Escape, _, _) => 
			parsed = None
			close
		case KeyReleased(`inputField`, k, _, _) =>
			parser(inputField.text) match {
				case Some(r) =>
					parsedStrIcon.icon = new TeXFormula(toStr(r)).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
					background = parsedBottomBarColor
					parsedStrIcon_aux.background = parsedBottomBarColor

					parsed = Some(r)

					if(k == Key.Enter) close()
				case None => 
					parsedStrIcon.icon = new TeXFormula(inputField.text).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
					background = unParsedBottomBarColor
					parsedStrIcon_aux.background = unParsedBottomBarColor

					parsed = None
			}
	}


	lazy val bottomBar = new GridPanel(1,2) {
		contents += new BorderPanel {
			layout(inputField) = Center
			opaque = false
			border = Swing.EmptyBorder(12, 5, 12, 5)
		}
		contents += parsedStrIconScrollPane
		// layout (parsedStrIconScrollPane) = East
		opaque = false
	}
		
	layout(new FlowPanel(FlowPanel.Alignment.Left)(new Label("INPUT "  + t) {
		font = new Font("Roboto-Bold", Font.BOLD, 16)
		foreground = Color.white
	}){opaque = false}) = North

	layout(bottomBar) = Center

	val okButton = new Button(swing.Action("Close popup") { close() }) {
		text = "OK"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 0)
		foreground = Color.white
	}

	val cancelButton = new Button(swing.Action("Cancel popup") { parsed = None; close() }) {
		text = "CANCEL"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 10)
		foreground = Color.white
	}

	layout(new FlowPanel(FlowPanel.Alignment.Right)( cancelButton, okButton ){opaque = false}) = South //{ cancel(); close() } )) = South
}


class RelAKAParsePopup extends BorderPanel with Popup {
	override def close() = {
		visible = false
	}

	val parsedBottomBarColor = new Color(51,172,113)
	val unParsedBottomBarColor = new Color(255,139,129)

	background = parsedBottomBarColor
	border = Swing.EmptyBorder(15,15,15,15)



	val inputFieldA = new TextField {
		columns = 25
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
	}

	val inputFieldAg = new TextField {
		columns = 25
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
	}

	val inputFieldA2 = new TextField {
		columns = 25
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
	}

	lazy val barA = new BoxPanel(Orientation.Horizontal) {
		contents += new Label("Action: ") {
			font = new Font("Roboto-Bold", Font.BOLD, 12)
			foreground = Color.white
			border = Swing.EmptyBorder(0, 0, 0, 10)
		}
		contents += inputFieldA
		//opaque = false
		background = parsedBottomBarColor
		border = Swing.EmptyBorder(10, 0, 10, 0)
	}

	lazy val barAg = new BoxPanel(Orientation.Horizontal) {
		contents += new Label("Agent:  ") {
			font = new Font("Roboto-Bold", Font.BOLD, 12)
			foreground = Color.white
			border = Swing.EmptyBorder(0, 0, 0, 10)
	 }
		contents += inputFieldAg
		background = parsedBottomBarColor
		border = Swing.EmptyBorder(10, 0, 10, 0)
	}

	lazy val barA2 = new BoxPanel(Orientation.Horizontal) {
		contents += new Label("Action: ") {
			font = new Font("Roboto-Bold", Font.BOLD, 12)
			foreground = Color.white
			border = Swing.EmptyBorder(0, 0, 0, 10)
	 }
		contents += inputFieldA2
		background = parsedBottomBarColor
		border = Swing.EmptyBorder(10, 0, 10, 0)
	}
	
	var parsedA:Option[Action] = None
	var parsedAg:Option[Agent] = None
	var parsedA2:Option[Action] = None

	listenTo(inputFieldA.keys, inputFieldAg.keys, inputFieldA2.keys)
	reactions += {
		case KeyReleased(`inputFieldA`, k, _, _) =>
			parseAction(inputFieldA.text) match {
				case Some(r) =>
					parsedA = Some(r)
					barA.background = parsedBottomBarColor
					if(k == Key.Enter && parsedAg != None && parsedA2 != None) close()
				case None => 
					barA.background = unParsedBottomBarColor
					parsedA = None
			}
		case KeyReleased(`inputFieldAg`, k, _, _) =>
			parseAgent(inputFieldAg.text) match {
				case Some(r) =>
					parsedAg = Some(r)
					barAg.background = parsedBottomBarColor
					if(k == Key.Enter && parsedA != None && parsedA2 != None) close()
				case None => 
					barAg.background = unParsedBottomBarColor
					parsedAg = None
			}
		case KeyReleased(`inputFieldA2`, k, _, _) =>
			parseAction(inputFieldA2.text) match {
				case Some(r) =>
					parsedA2 = Some(r)
					barA2.background = parsedBottomBarColor
					if(k == Key.Enter && parsedAg != None && parsedA != None) close()
				case None => 
					barA2.background = unParsedBottomBarColor
					parsedA2 = None
			}
	}
		
	layout(new FlowPanel(FlowPanel.Alignment.Left)(new Label("INPUT A RELAKA") {
		font = new Font("Roboto-Bold", Font.BOLD, 16)
		foreground = Color.white
	}){opaque = false}) = North

	layout(new BoxPanel(Orientation.Vertical) {
		contents += barA
		contents += barAg
		contents += barA2
		opaque = false
	}) = Center

	val okButton = new Button(swing.Action("Close popup") { close() }) {
		text = "OK"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 0)
		foreground = Color.white
	}

	val cancelButton = new Button(swing.Action("Cancel popup") { 
		parsedA = None
		parsedAg = None
		parsedA2 = None
		close() 
	}) {
		text = "CANCEL"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 10)
		foreground = Color.white
	}

	layout(new FlowPanel(FlowPanel.Alignment.Right)( cancelButton, okButton ){opaque = false}) = South //{ cancel(); close() } )) = South
}

class PreFormParsePopup extends BorderPanel with Popup  {
	override def close() = {
		visible = false
	}

	val parsedBottomBarColor = new Color(51,172,113)
	val unParsedBottomBarColor = new Color(255,139,129)

	background = parsedBottomBarColor
	border = Swing.EmptyBorder(15,15,15,15)

	val inputFieldA = new TextField {
		columns = 25
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
	}

	val inputFieldF = new TextField {
		columns = 25
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
	}

	lazy val barA = new BoxPanel(Orientation.Horizontal) {
		contents += new Label("Action:    ") {
			font = new Font("Roboto-Bold", Font.BOLD, 12)
			foreground = Color.white
			border = Swing.EmptyBorder(0, 0, 0, 10)
		}
		contents += inputFieldA
		//opaque = false
		background = parsedBottomBarColor
		border = Swing.EmptyBorder(10, 0, 10, 0)
	}

	lazy val barF = new BoxPanel(Orientation.Horizontal) {
		contents += new Label("Formula: ") {
			font = new Font("Roboto-Bold", Font.BOLD, 12)
			foreground = Color.white
			border = Swing.EmptyBorder(0, 0, 0, 10)
	 }
		contents += inputFieldF
		background = parsedBottomBarColor
		border = Swing.EmptyBorder(10, 0, 10, 0)
	}
	
	var parsedA:Option[Action] = None
	var parsedF:Option[Formula] = None

	listenTo(inputFieldA.keys, inputFieldF.keys)
	reactions += {
		case KeyReleased(`inputFieldA`, k, _, _) =>
			parseAction(inputFieldA.text) match {
				case Some(r) =>
					parsedA = Some(r)
					barA.background = parsedBottomBarColor

					if(k == Key.Enter && parsedF != None) close()
				case None => 
					barA.background = unParsedBottomBarColor
					parsedA = None
			}
		case KeyReleased(`inputFieldF`, k, _, _) =>
			parseFormula(inputFieldF.text) match {
				case Some(r) =>
					parsedF = Some(r)
					barF.background = parsedBottomBarColor

					if(k == Key.Enter && parsedA != None) close()
				case None => 
					barF.background = unParsedBottomBarColor
					parsedF = None
			}
	}
		
	layout(new FlowPanel(FlowPanel.Alignment.Left)(new Label("INPUT A PREFORM") {
		font = new Font("Roboto-Bold", Font.BOLD, 16)
		foreground = Color.white
	}){opaque = false}) = North

	layout(new BoxPanel(Orientation.Vertical) {
		contents += barA
		contents += barF
		opaque = false
	}) = Center

	val okButton = new Button(swing.Action("Close popup") { close() }) {
		text = "OK"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 0)
		foreground = Color.white
	}

	val cancelButton = new Button(swing.Action("Cancel popup") { 
		parsedA = None
		parsedF = None
		close() 
	}) {
		text = "CANCEL"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 10)
		foreground = Color.white
	}

	layout(new FlowPanel(FlowPanel.Alignment.Right)( cancelButton, okButton ){opaque = false}) = South //{ cancel(); close() } )) = South
}

class SequentListPopup(ruleList : List[(Rule, List[Sequent])], session:CalcSession = CalcSession()) extends BorderPanel with Popup {
	override def close() = {
		visible = false
	}

	var pair:Option[Tuple2[Rule, List[Sequent]]] = None

	val sideBarColorLight = new Color(250,250,250)
	def cols:Int = ruleList.map(_._2.length).sorted.reverse.head + 1

	def padList(len:Int):List[String] = {
		val ret = ListBuffer[String]()
		for (i <- 0 to len-1) ret += ""
		return ret.toList
	}

	def padArrayI(len:Int):Array[Int] = {
		val ret = ListBuffer[Int]()
		for (i <- 0 to len-1) ret += 0
		return ret.toArray
	}

	var ruleColWidth = padArrayI(cols)
	var ruleColHeight = 0

	def flattenedList:Array[Array[String]] = {
		val ret = new ListBuffer[Array[String]]()
		val columns = cols-1
		ruleList.foreach{ 
			case (a, list) => 
				ret += ((ruleToString(a) :: list.map(sequentToString(_))) ++ padList(columns-list.length)).toArray
				if (GUIHelper.createTeXIcon(ruleToString(a)).getIconWidth > ruleColWidth(0)) ruleColWidth(0) = GUIHelper.createTeXIcon(ruleToString(a)).getIconWidth
				for (i <- 0 to list.length-1) {
					// print(i)
					// print(" : ")
					// println(list(i))
					val icon = GUIHelper.createTeXIcon(sequentToString(list(i)))
					if (icon.getIconWidth > ruleColWidth(i+1)) ruleColWidth(i+1) = icon.getIconWidth
					if (icon.getIconHeight > ruleColHeight) ruleColHeight = icon.getIconHeight
				}

				println(((ruleToString(a) :: list.map(sequentToString(_))) ++ padList(columns-list.length)))
		}
		println(ruleColWidth)
		return ret.toArray
	}

	def resizeTable() = {
		ruleListTable.peer.setAutoResizeMode( javax.swing.JTable.AUTO_RESIZE_OFF )
		print("col count: ")
		println(ruleListTable.model.getColumnCount())
		for ( c <- 0 to cols-1 ) {
			println( ruleColWidth(c) )
			val tableColumn = ruleListTable.peer.getColumnModel().getColumn(c)
			tableColumn.setMinWidth( ruleColWidth(c) )
		}
	}
	
	val ruleListTable = new Table(ruleList.length, cols){
		selection.elementMode = Table.ElementMode.Row
		background = sideBarColorLight
		opaque = false
		peer.getTableHeader().setOpaque(false)
		peer.getTableHeader().setFont(new Font("Roboto-Bold", Font.BOLD, 12))
		peer.setDefaultRenderer(classOf[String], new TexRenderer())

		val header = List("Rule", "Sequent(s)") ++ padList(cols-2)

		model = new MyTableModel( flattenedList , header )

	}

	background = new Color(238,238,238)
	//border = Swing.EmptyBorder(15,15,15,15)


	//layout(ruleListTable) = Center

	val prettyTable = new PrettyScrollPane(ruleListTable){
		scrollPane.peer.getViewport().setBackground(sideBarColorLight)
	}
	layout(prettyTable) = Center


	ruleListTable.peer.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).put(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0), "Enter")
	ruleListTable.peer.getActionMap().put("Enter", new AbstractAction() {
		override def actionPerformed(ae:ActionEvent) {
			val selectedRowIndex = ruleListTable.peer.getSelectedRow
			if( 0 <= selectedRowIndex && selectedRowIndex < ruleListTable.model.getRowCount ){
				pair = Some(ruleList(selectedRowIndex))
				close()
			}
			else pair = None
		}
	})
	ruleListTable.peer.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).put(KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), "Escape")
	ruleListTable.peer.getActionMap().put("Escape", new AbstractAction() {
		override def actionPerformed(ae:ActionEvent) {
			pair = None
			close()
		}
	})


	ruleListTable.listenTo(ruleListTable.mouse.clicks)
	ruleListTable.reactions += {
		case m : MouseClicked if m.clicks == 2 => 
			val selectedRowIndex = ruleListTable.peer.getSelectedRow
			if( 0 <= selectedRowIndex && selectedRowIndex < ruleListTable.model.getRowCount ){
				pair = Some(ruleList(selectedRowIndex))
				close()
			}
			else pair = None
	}


	class ForcedListSelectionModel extends javax.swing.DefaultListSelectionModel {
		setSelectionMode(javax.swing.ListSelectionModel.SINGLE_SELECTION)

		override def clearSelection() {}
		override def removeSelectionInterval(index0:Int, index1:Int) {}
	}

	ruleListTable.peer.setSelectionModel(new ForcedListSelectionModel())

	layout(new FlowPanel(FlowPanel.Alignment.Left)(new Label("SELECT A RULE TO APPLY") {
		font = new Font("Roboto-Bold", Font.BOLD, 16)
		foreground = new Color(33,33,33)
		border = Swing.EmptyBorder(15, 15, 15, 15)
	}){ opaque = false }) = North



	val okButton = new Button(swing.Action("Close popup") { 
		val selectedRowIndex = ruleListTable.peer.getSelectedRow
		if( 0 <= selectedRowIndex && selectedRowIndex < ruleListTable.model.getRowCount ){
			pair = Some(ruleList(selectedRowIndex))
		}
		else pair = None
		close() 
	}) {
		text = "OK"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 0)
		foreground = new Color(66,133,244)
	}

	val cancelButton = new Button(swing.Action("Cancel popup") { 
		pair = None
		close() 
	}) {
		text = "CANCEL"
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		border = Swing.EmptyBorder(0, 0, 0, 10)
		foreground = new Color(66,133,244)
	}

	layout(new FlowPanel(FlowPanel.Alignment.Right)( cancelButton, okButton ){
		border = Swing.EmptyBorder(15, 15, 15, 15)
		opaque = false
	}) = South

	resizeTable

	//ruleListTable.peer.setFocusable(true)
	//peer.requestFocusInWindow
}


trait Popup extends Panel {
	def close()
}

class PopupPanel extends Panel {
	override lazy val peer = {
		val fixedPanel = new JPanel(new java.awt.GridBagLayout())
		fixedPanel.setOpaque(false)
		fixedPanel
	}

	var currentPopup:Option[Popup] = None

	def add(p:Popup, scaling:Boolean = false) = {
		if(scaling){
			val c = new java.awt.GridBagConstraints()
			c.weightx = 1.0
			c.weighty = 1.0
			c.fill = java.awt.GridBagConstraints.BOTH
			c.insets = new java.awt.Insets(0, 30, 0, 30)
			peer.add(p.peer, c)
		}
		else peer.add(p.peer)

		currentPopup = Some(p)
	}
	def removeAll = {
		currentPopup match {
			case Some(p) => 
				p.close
				currentPopup = None
			case None => ;
		}
		peer.removeAll
	}

	def displayPopup(panel:Popup, scaling:Boolean = false) = {
		removeAll
		add(panel, scaling)
		panel.visible = true
		revalidate
		repaint
	}
}