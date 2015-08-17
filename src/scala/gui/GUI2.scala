import swing._
import swing.event._

import swing.BorderPanel.Position._

import scala.collection.JavaConversions._
import scala.collection.mutable.ListBuffer

import java.awt.event.MouseEvent
import javax.swing._
import javax.swing.plaf.basic.BasicScrollBarUI

import java.awt.{Toolkit, Font, Color}
import java.io.File
import java.awt.datatransfer.Clipboard
import java.awt.datatransfer.StringSelection

import java.io.PrintWriter

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}

/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/
import Parser._
import PrintCalc._
import Proofsearch.derTree

object GUI2 extends SimpleSwingApplication {
	// misc stuff -------------------------

	val ge = java.awt.GraphicsEnvironment.getLocalGraphicsEnvironment()
	ge.registerFont(Font.createFont(Font.TRUETYPE_FONT, new File("src/scala/gui/img/Roboto-Bold.ttf")))
	ge.registerFont(Font.createFont(Font.TRUETYPE_FONT, new File("src/scala/gui/img/Roboto-Light.ttf")))

	val tabHighlightColor = new Color(255,82,82)
	val parsedBottomBarColor = new Color(51,172,113)
	val unParsedBottomBarColor = new Color(255,139,129)
	val sideBarColor = new Color(66,133,244)
	val sideBarColor2 = new Color(238,238,238)
	val sideBarColorLight = new Color(250,250,250)//= new Color(238,238,238) //new Color(66,133,244)
	val tableHeader = new Color(171,171,171)
	val textColor = new Color(238,238,238)
	val textColor2 = new Color(33,33,33)

	// calculus init ---------------------
	lazy val session = CalcSession()

	// bottom bar --------------------------

	val addButton = new ToggleButton {

		val image : java.awt.image.BufferedImage = javax.imageio.ImageIO.read(new java.io.File("src/scala/gui/img/add_button.png"))
		icon = new Icon() {
			override def paintIcon(c:java.awt.Component, g:java.awt.Graphics, x:Int, y:Int) = {
				val graphics = g.create().asInstanceOf[Graphics2D]
				graphics.scale(0.5f, 0.5f)
				graphics.drawImage(image, x, y, c)
			}
			override def getIconWidth() = 50
			override def getIconHeight() = 50
		}


		val image2 : java.awt.image.BufferedImage = javax.imageio.ImageIO.read(new java.io.File("src/scala/gui/img/add_button_toggled.png"))
		selectedIcon = new Icon() {
			override def paintIcon(c:java.awt.Component, g:java.awt.Graphics, x:Int, y:Int) = {
				val graphics = g.create().asInstanceOf[Graphics2D]
				graphics.scale(0.5f, 0.5f)
				graphics.drawImage(image2, x, y, c)
			}
			override def getIconWidth() = 50 
			override def getIconHeight() = 50
		}
		// icon = new ImageIcon(new ImageIcon("src/scala/gui/img/add_button.png").getImage().getScaledInstance(50, 50, java.awt.Image.SCALE_SMOOTH))
		// selectedIcon = new ImageIcon(new ImageIcon("src/scala/gui/img/add_button_toggled.png").getImage().getScaledInstance(50, 50, java.awt.Image.SCALE_SMOOTH))
		border = Swing.EmptyBorder(0, 0, 0, 0)
	}


	val inputField = new TextField {
		columns = 25
		visible = false
		val d = new Dimension(600, 20)
		preferredSize = d
		minimumSize = d
		opaque = false
		font = new Font("Roboto-Bold", Font.BOLD, 12)
		foreground = Color.white
		//minimumSize = new Dimension(350, 50)
		//maximumSize = new Dimension(800, 50)
		//preferredSize = new Dimension(800, 50)
		border = BorderFactory.createMatteBorder(0, 0, 1, 0, Color.white)
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
		visible = false
	}

	lazy val bottomBar = new BorderPanel {
		layout (addButton) = West
		layout (new GridPanel(1,2) {
			contents += new BorderPanel{
				layout(inputField) = Center
				opaque = false
				border = Swing.EmptyBorder(12, 5, 12, 5)
			}
			contents += parsedStrIconScrollPane
			// layout (parsedStrIconScrollPane) = East
			opaque = false
		}) = Center
		
		background = parsedBottomBarColor
		border = Swing.EmptyBorder(5, 5, 5, 5)
		opaque = false
	}

	listenTo(addButton, inputField.keys)
	reactions += {
		case ButtonClicked(`addButton`) => 
			inputField.visible = addButton.selected
			parsedStrIconScrollPane.visible = addButton.selected
			bottomBar.opaque = addButton.selected
			bottomBar.revalidate
			bottomBar.repaint

		case KeyReleased(`inputField`, k, _, _) =>
			parseSequent(inputField.text) match {
				case Some(r) =>
					session.currentSequent = r
					parsedStrIcon.icon = session.sequentToIcon(r)
					bottomBar.background = parsedBottomBarColor
					parsedStrIcon_aux.background = parsedBottomBarColor

					if(k == Key.Enter){
						session.currentPT = Prooftreea( session.currentSequent, RuleZera(Prem()), Nil )
						session.addPT()
						ptPanel.update()

						//hide the bottom bar 
						addButton.selected = !addButton.selected
						inputField.visible = addButton.selected
						parsedStrIconScrollPane.visible = addButton.selected
						bottomBar.opaque = addButton.selected
						bottomBar.revalidate
						bottomBar.repaint
					}
				case None => 
					parsedStrIcon.icon = new TeXFormula(inputField.text).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
					bottomBar.background = unParsedBottomBarColor
					parsedStrIcon_aux.background = unParsedBottomBarColor


			}
	}

	// sidebar ---------------------------------

	val menuButton = new ToggleButton {
		val image : java.awt.image.BufferedImage = javax.imageio.ImageIO.read(new java.io.File("src/scala/gui/img/menu_button.png"))
		icon = new Icon() {
			override def paintIcon(c:java.awt.Component, g:java.awt.Graphics, x:Int, y:Int) = {
				val graphics = g.create().asInstanceOf[Graphics2D]
				graphics.scale(0.5f, 0.5f)
				graphics.drawImage(image, x, y, c)
			}
			override def getIconWidth() = 25
			override def getIconHeight() = 25
		}
		border = Swing.EmptyBorder(10, 0, 0, 10)
	}

	val newButton = new Button("NEW") {
		font = new Font("Roboto-BOLD", Font.BOLD, 12)
		foreground = textColor
		val image : java.awt.image.BufferedImage = javax.imageio.ImageIO.read(new java.io.File("src/scala/gui/img/new_button.png"))
		icon = new Icon() {
			override def paintIcon(c:java.awt.Component, g:java.awt.Graphics, x:Int, y:Int) = {
				val graphics = g.create().asInstanceOf[Graphics2D]
				graphics.scale(0.5f, 0.5f)
				graphics.drawImage(image, x, y, c)
			}
			override def getIconWidth() = 25
			override def getIconHeight() = 25
		}

		border = Swing.EmptyBorder(0, 0, 0, 0)
	}

	val openButton = new Button("OPEN") {
		font = new Font("Roboto-BOLD", Font.BOLD, 12)
		foreground = textColor
		val image : java.awt.image.BufferedImage = javax.imageio.ImageIO.read(new java.io.File("src/scala/gui/img/open_button.png"))
		icon = new Icon() {
			override def paintIcon(c:java.awt.Component, g:java.awt.Graphics, x:Int, y:Int) = {
				val graphics = g.create().asInstanceOf[Graphics2D]
				graphics.scale(0.5f, 0.5f)
				graphics.drawImage(image, x, y, c)
			}
			override def getIconWidth() = 25
			override def getIconHeight() = 25
		}
		border = Swing.EmptyBorder(0, 0, 0, 0)
	}

	val saveButton = new Button("SAVE") {
		font = new Font("Roboto-BOLD", Font.BOLD, 12)
		foreground = textColor
		val image : java.awt.image.BufferedImage = javax.imageio.ImageIO.read(new java.io.File("src/scala/gui/img/save_button.png"))
		icon = new Icon() {
			override def paintIcon(c:java.awt.Component, g:java.awt.Graphics, x:Int, y:Int) = {
				val graphics = g.create().asInstanceOf[Graphics2D]
				graphics.scale(0.5f, 0.5f)
				graphics.drawImage(image, x, y, c)
			}
			override def getIconWidth() = 25
			override def getIconHeight() = 25
		}
		border = Swing.EmptyBorder(0, 0, 0, 0)
	}


	listenTo(menuButton, openButton, newButton, saveButton)
	reactions += {
		case ButtonClicked(`menuButton`) => 
			sideBar.visible = menuButton.selected
			sideBar.revalidate
			sideBar.repaint

		case ButtonClicked(`openButton`) => 
			GUIHelper.fileOpenDialog("Open a session file") match {
				case Some(file) =>
					// shoudl these be called here???
					session.clearRelAKA
					session.clearPreForm
					GUIHelper.openCSFile(file, session)
					relAKAtable.reload
					preFormTable.reload
				case None => ;
			}

		case ButtonClicked(`newButton`) => 
			session.clearAssms
			session.clearPT
			session.clearRelAKA
			session.clearPreForm
			relAKAtable.reload
			preFormTable.reload

		case ButtonClicked(`saveButton`) => 
			//if(saveFile == None){

			GUIHelper.fileSaveDialog() match {
				case Some(file) => GUIHelper.saveCSFile(file, session)
				case None => ;
			}
			

	}

	// assms and pts section --------------------------


	val ptList = new PrettyScrollPane(session.ptListView){ 
		session.ptListView.background = sideBarColorLight
		//border = BorderFactory.createMatteBorder(1, 0, 0, 0, sideBarColorSeparator)
	}

	val assmsList = new PrettyScrollPane(session.listView){ 
		session.listView.background = sideBarColorLight
	}

	val assmsAdd = new Button("ADD"){
		border = Swing.EmptyBorder(0,0,0,0)
		font = new Font("Roboto-BOLD", Font.BOLD, 12)
		foreground = sideBarColor
	}

	val assmsBar = new BorderPanel {
		layout(new BoxPanel(Orientation.Horizontal) {
			contents+= new Label("Assumptions"){
				font = new Font("Roboto-Light", Font.PLAIN, 16)
				foreground = textColor2
				border = Swing.EmptyBorder(15, 10, 15, 20)
			}
			contents+= assmsAdd
		}) = North
		layout(assmsList) = Center
	}

	val ptBar = new BorderPanel {
		layout(new BoxPanel(Orientation.Horizontal) {
			contents+= new Label("Proof Trees"){
				font = new Font("Roboto-Light", Font.PLAIN, 16)
				foreground = textColor2
				border = Swing.EmptyBorder(15, 10, 15, 20)
			}
		}) = North
		layout(ptList) = Center
	}

	val tab1 = new BoxPanel(Orientation.Vertical) {
		contents+= assmsBar
		//assmsList.foreground = Color.white
		contents+= ptBar
		background = sideBarColor2
	}

	def sequentToString_Aux(in:Sequent) = sequentToString(in) 
	val parseAssmPopup = new ParsePopup[Sequent](parseSequent, sequentToString_Aux,  "SEQUENT")


	listenTo(session.listView.keys, session.ptListView.keys, assmsAdd)
	reactions += {
		case ButtonClicked(`assmsAdd`) => 
			popupPanel.displayPopup(parseAssmPopup)
			addCallback(parseAssmPopup)(() => {
				parseAssmPopup.parsed match {
					case Some(rSeq) => session.addAssm(rSeq)
					case None => ;
				}
			})
		case KeyReleased(session.listView, Key.BackSpace, _, _) => session.removeAssms
		case KeyReleased(session.listView, Key.Delete, _, _) => session.removeAssms
		case KeyReleased(session.ptListView, Key.BackSpace, _, _) => session.removePTs
		case KeyReleased(session.ptListView, Key.Delete, _, _) => session.removePTs
	}


	// pt list popup menu --------------------------

	session.ptListView.listenTo(session.ptListView.mouse.clicks)
	session.ptListView.reactions += {
		case m : MouseClicked if !session.ptListView.selection.items.isEmpty && m.clicks == 2 => 
			session.loadPT
			ptPanel.update
		case m : MouseClicked if m.peer.getButton == MouseEvent.BUTTON3 => 
			val row = session.ptListView.peer.locationToIndex(m.peer.getPoint)
			if(row != -1) session.ptListView.peer.setSelectedIndex(row)
			if(!session.ptListView.selection.items.isEmpty) ptListPopupMenu.peer.show(m.peer.getComponent, m.peer.getX, m.peer.getY)
	}

	val ptListPopupMenu = new scala.swing.PopupMenu {
		contents += new MenuItem(swing.Action("Add as assumption") {
			session.addAssmFromSelPT()
		})

		contents += new MenuItem(swing.Action("Delete tree") {
			session.removePTs()
			session.ptListView.revalidate()
			session.ptListView.repaint()
		})

		contents += new MenuItem(swing.Action("Export tree to LaTeX") {
			session.exportLatexFromSelPT()
		})

		contents += new MenuItem(swing.Action("Copy tree as Isabelle") {
			session.ptListView.selection.items.head match {
				case (icn, pt) => 
					// adapted from http://www.avajava.com/tutorials/lessons/how-do-i-copy-a-string-to-the-clipboard.html
					val str = prooftreeToString(pt, PrintCalc.ISABELLE)
					val toolkit = Toolkit.getDefaultToolkit()
					val clipboard = toolkit.getSystemClipboard()
					val strSel = new StringSelection(str)
					clipboard.setContents(strSel, null)
			}
		})

		contents += new MenuItem(swing.Action("Copy tree as Isabelle SE") {
			session.ptListView.selection.items.head  match {
				case (icn, pt) => 
					// adapted from http://www.avajava.com/tutorials/lessons/how-do-i-copy-a-string-to-the-clipboard.html
					val str = prooftreeToString(pt, PrintCalc.ISABELLE_SE)
					val toolkit = Toolkit.getDefaultToolkit()
					val clipboard = toolkit.getSystemClipboard()
					val strSel = new StringSelection(str)
					clipboard.setContents(strSel, null)
			}
		})
	}

	// relaka and preform --------------------------

	/*/*uncommentL?Action?Agent-BEGIN*/*//*uncommentL?Action?Agent-END*/

	val relAKAreflexive = new CheckBox("relAKA is reflexive"){
		border = Swing.EmptyBorder(10,10,10,10)
		font = new Font("Roboto-Light", Font.PLAIN, 12)
		foreground = textColor2
		selected = true
	}

	val relAKAadd = new Button("ADD"){
		border = Swing.EmptyBorder(0,0,0,0)
		font = new Font("Roboto-BOLD", Font.BOLD, 12)
		foreground = sideBarColor
		//preferredSize = new Dimension(50, 25)
	}

	val relAKAtable = new Table(1, 3){
		selection.elementMode = Table.ElementMode.Row
		background = sideBarColorLight
		opaque = false
		peer.getTableHeader().setOpaque(false)
		peer.getTableHeader().setFont(new Font("Roboto-Bold", Font.BOLD, 12))
		peer.setDefaultRenderer(classOf[String], new TexRenderer())

		val headers = List("Action", "Agent", "Action")

		def reload() = {
			model = new MyTableModel( session.flattenRelAKA, headers )
			revalidate
			repaint
		}
		reload
	}


	val relAKAbar = new BorderPanel {
		layout(new BoxPanel(Orientation.Horizontal) {
			contents+= new Label("RelAKA"){
				font = new Font("Roboto-Light", Font.PLAIN, 16)
				foreground = textColor2
				border = Swing.EmptyBorder(15, 10, 15, 20)
				//preferredSize = new Dimension(400, 50)
			}
			contents+= relAKAadd
		}) = North
		layout(new PrettyScrollPane(relAKAtable){scrollPane.peer.getViewport().setBackground(sideBarColorLight)}) = Center
		layout(relAKAreflexive) = South
	}


	val preFormAdd = new Button("ADD"){
		border = Swing.EmptyBorder(0,0,0,0)
		font = new Font("Roboto-BOLD", Font.BOLD, 12)
		foreground = sideBarColor
		//preferredSize = new Dimension(50, 25)
	}

	val preFormTable = new Table(1, 2){
		selection.elementMode = Table.ElementMode.Row
		background = sideBarColorLight
		opaque = false
		peer.getTableHeader().setOpaque(false)
		peer.getTableHeader().setFont(new Font("Roboto-Bold", Font.BOLD, 12))
		peer.setDefaultRenderer(classOf[String], new TexRenderer())

		val headers = List("Action", "Formula")

		def reload() = {
			model = new MyTableModel( session.flattenPreForm , headers )
			revalidate
			repaint
		}

		reload
	}

	val preFormBar = new BorderPanel {
		layout(new BoxPanel(Orientation.Horizontal) {
			contents+= new Label("Pre Formulas"){
				font = new Font("Roboto-Light", Font.PLAIN, 16)
				foreground = textColor2
				border = Swing.EmptyBorder(15, 10, 15, 20)
			}
			contents+= preFormAdd
		}) = North
		layout(new PrettyScrollPane(preFormTable){scrollPane.peer.getViewport().setBackground(sideBarColorLight)}) = Center
		// layout(relAKAreflexive) = South

		border = BorderFactory.createMatteBorder(1, 0, 0, 0, sideBarColorLight)

	}

	val tab3 = new BoxPanel(Orientation.Vertical) {
		contents+= relAKAbar
		contents+= preFormBar
		background = sideBarColor2
	}



	val relAKAaddPopup = new RelAKAParsePopup
	val preFormAddPopup = new PreFormParsePopup

	listenTo(relAKAreflexive, relAKAadd, preFormAdd, relAKAtable.keys, preFormTable.keys)

	reactions+={
		case ButtonClicked(`relAKAreflexive`) => session.relAKAreflexive = relAKAreflexive.selected
		case ButtonClicked(`relAKAadd`) => 
			popupPanel.displayPopup(relAKAaddPopup)
			addCallback(relAKAaddPopup)(() =>{
				if(relAKAaddPopup.parsedA != None && relAKAaddPopup.parsedAg != None && relAKAaddPopup.parsedA2 != None) {
					session.addRelAKA(relAKAaddPopup.parsedA.get, relAKAaddPopup.parsedAg.get, relAKAaddPopup.parsedA2.get)
					relAKAtable.reload
				}
			})
		case KeyReleased(`relAKAtable`, Key.BackSpace, _, _) | 
			KeyReleased(`relAKAtable`, Key.Delete, _, _) => 
			val selectedRowIndex = relAKAtable.peer.getSelectedRow
			val a = relAKAtable.model.getValueAt(selectedRowIndex, 0).asInstanceOf[String]
			val ag = relAKAtable.model.getValueAt(selectedRowIndex, 1).asInstanceOf[String]
			val a2 = relAKAtable.model.getValueAt(selectedRowIndex, 2).asInstanceOf[String]
			session.removeRelAKA(a, ag, a2)
			relAKAtable.reload
		case ButtonClicked(`preFormAdd`) => 
			popupPanel.displayPopup(preFormAddPopup)
			addCallback(preFormAddPopup)(() =>{
				if(preFormAddPopup.parsedA != None && preFormAddPopup.parsedF != None) {
					session.addPreForm(preFormAddPopup.parsedA.get, preFormAddPopup.parsedF.get)
					preFormTable.reload
				}
			})
		case KeyReleased(`preFormTable`, Key.BackSpace, _, _) | 
			KeyReleased(`preFormTable`, Key.Delete, _, _) => 
			val selectedRowIndex = preFormTable.peer.getSelectedRow
			val a = preFormTable.model.getValueAt(selectedRowIndex, 0).asInstanceOf[String]
			session.removePreForm(a)
			preFormTable.reload
	}

	/*uncommentR?Action?Agent-BEGIN*//*/*uncommentR?Action?Agent-END*/*/

	// -----------------------------------------------
	val tabPane = new JTabbedPane(SwingConstants.RIGHT)
	tabPane.setBorder(Swing.EmptyBorder(0, 0, 0, 0))
	tabPane.setUI(new MyTabbedPaneUI())


	tabPane.addTab(null, tab1.peer)
	tabPane.addTab(null, new JButton("aaaaaaa"))
	tabPane.addTab(null, tab3.peer)


	// Create vertical labels to render tab titles
	val labTab1 = new JLabel("Assms & P'Trees")
	labTab1.setUI(new VerticalLabelUI(true))
	labTab1.setFont(new Font("Roboto-Bold", Font.BOLD, 12))
	labTab1.setForeground(textColor)
	tabPane.setTabComponentAt(0, labTab1) // For component1

	val labTab2 = new JLabel("Abbreviations")
	labTab2.setUI(new VerticalLabelUI(true))
	labTab2.setFont(new Font("Roboto-Bold", Font.BOLD, 12))
	labTab2.setForeground(textColor)
	tabPane.setTabComponentAt(1, labTab2) // For component2

	val labTab3 = new JLabel("Locales")
	labTab3.setUI(new VerticalLabelUI(true))
	labTab3.setFont(new Font("Roboto-Bold", Font.BOLD, 12))
	labTab3.setForeground(textColor)
	tabPane.setTabComponentAt(2, labTab3) // For component3


	lazy val sideBar = new BorderPanel {
		layout (new FlowPanel(FlowPanel.Alignment.Left)(newButton, new Label {border = Swing.EmptyBorder(0, 5, 0, 0)}, openButton, new Label {border = Swing.EmptyBorder(0, 5, 0, 0)}, saveButton) {
			opaque = false
			border = Swing.EmptyBorder(5, 5, 0, 10)
		}) = North
		layout(Component.wrap(tabPane)) = Center
		
		background = sideBarColor
		visible = false
		preferredSize = new Dimension(350, 400)

	}

	// main view ------------------------------

	val popupPanel = new PopupPanel

	def addCallback(panel:Panel)(callback: () => Unit){
		listenTo(panel)
		reactions += {
			case UIElementHidden(`panel`) => 
				callback()
				deafTo(panel)
		}
	}

	lazy val ui = new BorderPanel {
		border = Swing.EmptyBorder(0, 0, 0, 0)
		layout (bottomBar) = South
		// layout (sideBar) = East

		layout(popupPanel) = Center

		layout (new FlowPanel(FlowPanel.Alignment.Right)(menuButton) {
			opaque = false
			preferredSize = menuButton.preferredSize
			minimumSize = menuButton.minimumSize
			maximumSize = menuButton.maximumSize
		}) = North


		opaque = false
		// background = new Color(224,224,224)
	}

	// proof tree view ---------------------------

	val ptPanel = new ProofTreePanel(session=session, popupPanel=Some(popupPanel)) {
		opaque = false
	}
	ptPanel.build()

	val validPT = new Label("This proof tree is invalid"){
		foreground = new Color(244, 67, 54)
		font = new Font("Roboto-Light", Font.PLAIN, 12)
		visible = false
	}

	listenTo(session)
	reactions += {
		case c : PTChanged => 
			validPT.visible = !c.valid
	}



	lazy val ui2 = new BorderPanel {
		border = Swing.EmptyBorder(0, 0, 0, 0)
		layout (sideBar) = East
		layout (validPT) = South
		opaque = false
	}
	
	val ptPanelScrollPane = new PrettyScrollPane(ptPanel)
	val main = new LayeredPanel(ptPanelScrollPane, ui, ui2){
		background = new Color(250,250,250)
	}

	def top = new MainFrame {
		title = "Calculus Toolbox"
		contents = main
		minimumSize = new Dimension(600,400)

		// os x specific settings
		val osName = System.getProperty("os.name").toLowerCase()
		if (osName.startsWith("mac os x")) {
			System.setProperty("apple.laf.useScreenMenuBar", "true")
			com.apple.eawt.FullScreenUtilities.setWindowCanFullScreen(peer,true)
		}

		ptPanel.requestFocus
	}
	
}

class TexRenderer extends javax.swing.table.DefaultTableCellRenderer {
	override def getTableCellRendererComponent(table:JTable, value:Object, isSelected:Boolean, hasFocus:Boolean, row:Int, column:Int):java.awt.Component = {
		val cellComponent = super.getTableCellRendererComponent(table, value, isSelected, hasFocus, row, column).asInstanceOf[JLabel]
		val str = value.asInstanceOf[String]
		val icon = new TeXFormula(str).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
		cellComponent.setIcon(icon)
		cellComponent.setText("")
		if (table.getRowHeight < cellComponent.getPreferredSize().height) {
			table.setRowHeight(cellComponent.getPreferredSize().height)
		}
		return cellComponent
	}
}


class MyTableModel( var rowData: Array[Array[String]], val columnNames: Seq[String] ) extends javax.swing.table.AbstractTableModel {
	override def getColumnName(column: Int) = columnNames(column).toString
	def getRowCount() = rowData.length
	def getColumnCount() = columnNames.length
	def getValueAt(row: Int, col: Int): String = rowData(row)(col)
	override def isCellEditable(row: Int, column: Int) = false
	def setValueAt(value: String, row: Int, col: Int) = {
		rowData(row)(col) = value
	}    
	def addRow(data: Array[String]) = {
		rowData ++= Array(data)
	}
}


class MyTableModel2( var rowData: Array[Array[Any]], val columnNames: Seq[String] ) extends javax.swing.table.AbstractTableModel {
	override def getColumnName(column: Int) = columnNames(column).toString
	def getRowCount() = rowData.length
	def getColumnCount() = columnNames.length
	def getValueAt(row: Int, col: Int): AnyRef = rowData(row)(col).asInstanceOf[AnyRef]
	override def isCellEditable(row: Int, column: Int) = false
	override def setValueAt(value: Any, row: Int, col: Int) = {
		rowData(row)(col) = value
	}    
	def addRow(data: Array[AnyRef]) = {
		rowData ++= Array(data.asInstanceOf[Array[Any]])
	}
}