import swing._
import swing.event._

import swing.BorderPanel.Position._

import scala.collection.JavaConversions._
import scala.collection.mutable.ListBuffer

import java.awt.event.MouseEvent
import javax.swing._
import javax.swing.plaf.basic._

import java.awt.{Toolkit, Font, Color, FileDialog}
import java.awt.datatransfer.Clipboard
import java.awt.datatransfer.StringSelection

import java.io.PrintWriter

import org.scilab.forge.jlatexmath.{TeXFormula, TeXConstants, TeXIcon}
import scala.util.parsing.json.{JSON, JSONObject, JSONArray}


// import java.util._
import javax.swing.plaf._

/*calc_import-BEGIN*/
import DEAK._
/*calc_import-END*/
import Parser._
import PrintCalc._
object GUIHelper {

  def createTeXIcon(str:String):TeXIcon = {
    val icon = new TeXFormula(str).createTeXIcon(TeXConstants.STYLE_DISPLAY, 15)
    return icon
  }

	def fileOpenDialog(title:String):Option[java.io.File] = {
		val fd = new FileDialog(null: java.awt.Dialog, title, FileDialog.LOAD)
        fd.setDirectory(".")
          fd.setFilenameFilter(new CSFilter())
          fd.setVisible(true)
          val filename = fd.getFile()
          if (filename != null) {
            val file = new java.io.File(fd.getDirectory() + filename)
            return Some(file)
          }
          else
            return None
	}

	def openCSFile(file:java.io.File, session:CalcSession) = {
    val jsonStr = scala.io.Source.fromFile(file).getLines.mkString
    Some(JSON.parseFull(jsonStr)) match {
      case Some(M(map)) =>
        map.get("assms") match {
          case L(assms) =>
            val ass = assms.map(parseSequent(_))
            session.clearAssms
            for (Some(a) <- ass){
              session.addAssm(a)
            }
          case _ => 
        }
        map.get("pts") match {
          case LLL(pts) =>
            //println(pts.toString())
            session.clearPT
            for (pt <- pts){
              session.addPT(readPT(pt))
            }
            // }
          case _ => println("fail")
        }
        /*/*uncommentL?Action?Agent-BEGIN*/*//*uncommentL?Action?Agent-END*/
        map.get("relAKA") match {
          case LLS(relAKA) =>
            session.clearRelAKA
            for (a <- relAKA){
              if(a.length == 3) {
                val action = parseAction(a(0))
                val agent = parseAgent(a(1))
                val action2 = parseAction(a(2))
                if (action != None && agent != None && action2 != None) {
                  session.addRelAKA(action.get, agent.get, action2.get)
                }
              }
            }
          case _ => 
        }

        map.get("preForm") match {
          case LLS(preForm) =>
            session.clearPreForm
            for (a <- preForm){
              if(a.length == 2) {
                val action = parseAction(a(0))
                val formula = parseFormula(a(1))
                if (action != None && formula != None) {
                  println(a)
                  session.addPreForm(action.get, formula.get)
                }
              }
            }
          case _ => 
        }
        /*uncommentR?Action?Agent-BEGIN*//*/*uncommentR?Action?Agent-END*/*/
      case _ => 
    }
  }

  def readPT(map : Map[String, Any]):Prooftree = {
        map.get("seq") match {
          case S(str_seq) => 
            val seq = parseSequent(str_seq)
            map.get("rule") match {
              case S(str_rule) => 
                val rule = parseRule(str_rule)
                map.get("pts") match {
                  case LLL(pts_str) => 
                    // val pts = List[Prooftree]()
                    // for ( Some(a) <-  ){ pts += a }
                    seq match {
                      case Some(s)=>
                        rule match {
                          case Some(r)=> 
                            return Prooftreea(s, r, pts_str.map(readPT))
                        }
                    }
                }
              case None =>

                map.get("macro") match {
                  case M(macro_rule) => 
                    val macroName = macro_rule.keys.head
                    println(macroName)
                    val rule = macro_rule.get(macroName) match {
                      case M(map) => Some(RuleMacro(macroName.toList, readPT(map)))
                      case _ => None
                    }
                      
                    map.get("pts") match {
                      case LLL(pts_str) => 
                        // val pts = List[Prooftree]()
                        // for ( Some(a) <-  ){ pts += a }
                        seq match {
                          case Some(s)=>
                            rule match {
                              case Some(r)=> 
                                return Prooftreea(s, r, pts_str.map(readPT))
                            }
                        }
                    }
                }

            }
        }
  }

  def readPTold(map : Map[String, Any]):Prooftree = {
        map.get("seq") match {
          case S(str_seq) => 
            val seq = parseSequent(str_seq)
            map.get("rule") match {
              case S(str_rule) => 
                val rule = parseRule(str_rule)
                map.get("pts") match {
                  case LLL(pts_str) => 
                    // val pts = List[Prooftree]()
                    // for ( Some(a) <-  ){ pts += a }
                    seq match {
                      case Some(s)=>
                        rule match {
                          case Some(r)=> 
                            return Prooftreea(s, r, pts_str.map(readPT))
                        }
                    }
                }
            }
        }
  }




// save ----------------------------

def fileSaveDialog():Option[java.io.File] = {
    val fd = new FileDialog(null: java.awt.Dialog, "Save a session file", FileDialog.SAVE)
    fd.setDirectory(".")
    fd.setFilenameFilter(new CSFilter())
    fd.setVisible(true)
    val filename = fd.getFile()
    if (filename != null){
      val file = if (!filename.endsWith(".cs")) new java.io.File(fd.getDirectory() + filename + ".cs") else new java.io.File(fd.getDirectory() + filename)
      return Some(file)
    }
    else
      return None
}

def saveCSFile(file:java.io.File, session:CalcSession) = {  
    Some(new PrintWriter(file)).foreach{p =>
      p.write(
        JSONObject( 
          Map( 
            "assms" -> JSONArray( session.assmsBuffer.toList.map{case (i,s) => sequentToString(s, PrintCalc.ASCII)} )
            ,"pts"   -> JSONArray( session.ptBuffer.toList.map{ case (i,s) => JSONObject(savePT(s)) } )
            /*/*uncommentL?Action?Agent-BEGIN*/*//*uncommentL?Action?Agent-END*/
            ,"relAKA"  -> JSONArray( session.flattenRelAKAStr.map(JSONArray) )
            ,"preForm"  -> JSONArray( session.flattenPreFormStr.map(JSONArray) )
            /*uncommentR?Action?Agent-BEGIN*//*/*uncommentR?Action?Agent-END*/*/ ) )
          .toString())
      p.close
      // session.ptBuffer.toList(0) match {
      //   case (i,s) => println(JSONObject(savePT(s)).toString())
      // }
    }
}

def savePT(pt:Prooftree):Map[String, Any] = pt match {
    case Prooftreea(s, RuleMacro(str, pt), pts) =>
      Map( 
        "seq" -> sequentToString(s, PrintCalc.ASCII),
        "macro"-> JSONObject( 
          Map( 
            str.mkString -> JSONObject( savePT(pt) )
          )),
        "pts"-> JSONArray( pts.map(x => JSONObject(savePT(x)) ) )   )

    case Prooftreea(s, r, pts) =>
      Map( 
        "seq" -> sequentToString(s, PrintCalc.ASCII),
        "rule"-> ruleToString(r, PrintCalc.ASCII),
        "pts"-> JSONArray( pts.map(x => JSONObject(savePT(x)) ) )   )
}

}

class CSFilter extends java.io.FilenameFilter {
  def accept(directory: java.io.File, filename : String): Boolean = {
    if (filename.endsWith(".cs")) return true
    return false
  }
}

object S extends CC[String]
object LL extends CC[List[Any]]
object LLS extends CC[List[List[String]]]
object LLL extends CC[List[Map[String,Any]]]
object M extends CC[Map[String, Any]]
object MM extends CC[Map[String, String]]


// adapted from: http://ui-ideas.blogspot.co.uk/2012/06/mac-os-x-mountain-lion-scrollbars-in.html
class PrettyScrollPane(component:Component) extends scala.swing.Component {
  val scrollPane = new ScrollPane(component) {
    border = Swing.EmptyBorder(0, 0, 0, 0)
    opaque = false
    peer.getVerticalScrollBar().setUnitIncrement(20)
    peer.getHorizontalScrollBar().setUnitIncrement(20)
  }
  var hScrollBar = scrollPane.peer.getHorizontalScrollBar()
  hScrollBar.setVisible(false)
  hScrollBar.setOpaque(false)
  hScrollBar.setUI(new MyScrollBarUI)

  val vScrollBar = scrollPane.peer.getVerticalScrollBar()

  vScrollBar.setVisible(false)
  vScrollBar.setOpaque(false)
  vScrollBar.setUI(new MyScrollBarUI)

  val layeredPane = new JLayeredPane()
  layeredPane.setLayer(vScrollBar, JLayeredPane.PALETTE_LAYER)
  layeredPane.setLayer(hScrollBar, JLayeredPane.PALETTE_LAYER)

  scrollPane.peer.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED)
  scrollPane.peer.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED)
  scrollPane.peer.setLayout(new ScrollPaneLayout() {
    override def layoutContainer(parent:java.awt.Container) {
      super.layoutContainer(parent)

      val insets = parent.getInsets();

      val availR = new Rectangle(0, 0, peer.getWidth(), peer.getHeight())
      availR.x = insets.left
      availR.y = insets.top
      availR.width -= insets.left + insets.right
      availR.height -= insets.top + insets.bottom


      val colHeadR = new Rectangle(0, availR.y, 0, 0)

      if ((colHead != null) && (colHead.isVisible())) {
        val colHeadHeight = Math.min(availR.height, colHead.getPreferredSize().height)
        colHeadR.height = colHeadHeight
        availR.y += colHeadHeight
        availR.height -= colHeadHeight
      }

      viewport.setBounds(availR)
      SwingUtilities.invokeLater(new Runnable() {
        override def run() {
          displayScrollBarsIfNecessary(viewport)
        }
      })
    }
  })

  layeredPane.add(hScrollBar)
  layeredPane.add(vScrollBar)
  layeredPane.add(scrollPane.peer)

  peer.setLayout(new java.awt.BorderLayout() {
    override def layoutContainer(target:java.awt.Container) = {
      super.layoutContainer(target)
      val width = peer.getWidth()
      val height = peer.getHeight()

      scrollPane.peer.setBounds(0, 0, width, height)

      val scrollBarSize = 12
      val cornerOffset = if (vScrollBar.isVisible() &&
        hScrollBar.isVisible()) scrollBarSize else 0
      if (vScrollBar.isVisible()) {
        vScrollBar.setBounds(width - scrollBarSize, 0,
          scrollBarSize, height - cornerOffset)
      }
      if (hScrollBar.isVisible()) {
        hScrollBar.setBounds(0, height - scrollBarSize,
          width - cornerOffset, scrollBarSize)
      }
    }
  })
  peer.add(layeredPane, java.awt.BorderLayout.CENTER)
  //layeredPane.setBackground(Color.BLUE)

  def displayScrollBarsIfNecessary(viewPort:JViewport) = {
    displayVerticalScrollBarIfNecessary(viewPort)
    displayHorizontalScrollBarIfNecessary(viewPort)
  }

  def displayVerticalScrollBarIfNecessary(viewPort:JViewport) = {
    val viewRect = viewPort.getViewRect()
    val viewSize = viewPort.getViewSize()
    val shouldDisplayVerticalScrollBar = viewSize.getHeight() > viewRect.getHeight()
    vScrollBar.setVisible(shouldDisplayVerticalScrollBar)
  }

  def displayHorizontalScrollBarIfNecessary(viewPort:JViewport) = {
    val viewRect = viewPort.getViewRect()
    val viewSize = viewPort.getViewSize()
    val shouldDisplayHorizontalScrollBar = viewSize.getWidth() > viewRect.getWidth()
    hScrollBar.setVisible(shouldDisplayHorizontalScrollBar)
  }

  // custom scroll bars

}


class MyScrollBarUI extends BasicScrollBarUI {

  val SCROLL_BAR_ALPHA_ROLLOVER = 150
  val SCROLL_BAR_ALPHA = 100
  val THUMB_BORDER_SIZE = 2
  val THUMB_SIZE = 8
  val THUMB_COLOR = Color.BLACK

  class MyScrollBarButton extends JButton {
    setOpaque(false)
    setFocusable(false)
    setFocusPainted(false)
    setBorderPainted(false)
    setBorder(BorderFactory.createEmptyBorder())
  }

  override def createDecreaseButton(orientation:Int):javax.swing.JButton = {
      return new MyScrollBarButton
  }

  override def createIncreaseButton(orientation:Int):javax.swing.JButton = {
      return new MyScrollBarButton
  }

  override def paintTrack(g:java.awt.Graphics, c:JComponent, trackBounds:Rectangle) = {
  }

  override def paintThumb(g:java.awt.Graphics, c:JComponent, thumbBounds:Rectangle) = {
    val alpha = if(isThumbRollover()) SCROLL_BAR_ALPHA_ROLLOVER else SCROLL_BAR_ALPHA
    val orientation = scrollbar.getOrientation()
    val arc = THUMB_SIZE
    val x = thumbBounds.x + THUMB_BORDER_SIZE
    val y = thumbBounds.y + THUMB_BORDER_SIZE

    var width = if (orientation ==  java.awt.Adjustable.VERTICAL)
            THUMB_SIZE else thumbBounds.width - (THUMB_BORDER_SIZE * 2)
    width = Math.max(width, THUMB_SIZE)

    var height = if (orientation ==  java.awt.Adjustable.VERTICAL)
            thumbBounds.height - (THUMB_BORDER_SIZE * 2) else THUMB_SIZE
    height = Math.max(height, THUMB_SIZE)

    val graphics2D = g.create().asInstanceOf[java.awt.Graphics2D]
    graphics2D.setRenderingHint(java.awt.RenderingHints.KEY_ANTIALIASING,
      java.awt.RenderingHints.VALUE_ANTIALIAS_ON)
    graphics2D.setColor(new Color(THUMB_COLOR.getRed(),
      THUMB_COLOR.getGreen(), THUMB_COLOR.getBlue(), alpha))
    graphics2D.fillRoundRect(x, y, width, height, arc, arc)
    graphics2D.dispose()
  }
}

class MyTabbedPaneUI extends BasicTabbedPaneUI {

    val inclTab = 4
    var anchoFocoV = inclTab
    val anchoFocoH = 4
    val anchoCarpetas = 18
    // private Polygon shape

    // def createUI(c:JComponent):ComponentUI = return new CustomTabbedPaneUI()

    override def installDefaults() = {
        super.installDefaults()
        //selectedTabPadInsets = tabInsets
        //tabAreaInsets = tabInsets
        // val selectColor = new Color(250, 192, 192)
        // valdeSelectColor = new Color(197, 193, 168)
        tabInsets.top = 10
        tabInsets.left = 10
                tabInsets.right = 5

    }

    // override def paintTabArea(g:java.awt.Graphics, tabPlacement:Int, selectedIndex:Int) = {}
	

	override def paintContentBorder(g:java.awt.Graphics, tabPlacement:Int , selectedIndex:Int) = {}
    override def paintTabBackground(g:java.awt.Graphics, tabPlacement:Int , selectedIndex:Int, x:Int, y:Int, w:Int, h:Int, isSelected:Boolean) = {
    	if(isSelected) {

    		val savedColor = g.getColor()
	        g.setColor(new Color(255,82,82))
	        g.fillRect(rects(selectedIndex).x+1, rects(selectedIndex).y, 
	               2, rects(selectedIndex).height)
	        // g.setColor(Color.BLUE)
	        // g.drawRect(rects[tabIndex].x, rects[tabIndex].y, 
	        //        rects[tabIndex].width, rects[tabIndex].height)
	        g.setColor(savedColor)
    		//super.paintTabBackground(g, tabPlacement, selectedIndex, x, y, w, h, isSelected)
    	}
    }


	override def paintTabBorder(g:java.awt.Graphics, tabPlacement:Int, tabIndex:Int, x:Int, y:Int, w:Int, h:Int, isSelected:Boolean) = {}
  override def paintFocusIndicator(g:java.awt.Graphics, tabPlacement:Int, rects: Array[Rectangle], tabIndex:Int, iconRect:Rectangle, textRect:Rectangle, isSelected:Boolean) = {}
}


class LayeredPanel(component:Component, ui:Component, ui2:Component = null) extends swing.Component {
  val layeredPane = new JLayeredPane()

  layeredPane.add(component.peer)
  

  layeredPane.setLayer(ui.peer, JLayeredPane.PALETTE_LAYER)
  layeredPane.add(ui.peer)

  if(ui2 != null){
    layeredPane.setLayer(ui2.peer, JLayeredPane.PALETTE_LAYER)
    layeredPane.add(ui2.peer)
  }


  peer.setLayout(new java.awt.BorderLayout() {
    override def layoutContainer(target:java.awt.Container) = {
      super.layoutContainer(target)
      val width = peer.getWidth()
      val height = peer.getHeight()
      component.peer.setBounds(0, 0, width, height)
      ui.peer.setBounds(0, 0, width, height)
        if(ui2 != null) ui2.peer.setBounds(0, 0, width, height)

    }
  })
  peer.add(layeredPane, java.awt.BorderLayout.CENTER)
  layeredPane.setBackground(Color.BLUE)
}
