import swing.{Action, Component, Dialog, Swing, MenuItem, Graphics2D, ListView, PopupMenu}
import swing.event.{ButtonClicked, MouseClicked, KeyPressed, KeyReleased, Key}

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
import Parser._

import Proofsearch._


class ProofTreePanel(session : CalcSession, gapBetweenLevels:Int = 10, gapBetweenNodes:Int = 80, editable : Boolean = true, popupPanel:Option[PopupPanel] = None) extends scala.swing.Panel {
	val configuration = new DefaultConfiguration[SequentInPt](gapBetweenLevels, gapBetweenNodes, org.abego.treelayout.Configuration.Location.Bottom)
	val nodeExtentProvider = new SequentInPtNodeExtentProvider()

	// create the layout
	//println("abbrevMAP:")
	//println(session.abbrevMap.toMap)
	var treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)


	val b1 = boundsOfNode(tree.getRoot())
	def OFFSET_X : Int = {
		val s = treeLayout.getBounds().getBounds().getSize()
		val pSize = peer.getSize()
		return (pSize.width - s.width)/2
	}

	def OFFSET_Y : Int = {
		val s = treeLayout.getBounds().getBounds().getSize()
		val pSize = peer.getSize()
		return (pSize.height - s.height - 50)
	}

	peer.setLayout(null)
	border = Swing.EmptyBorder(10, 10, 10, 10)

	

	var selectedSequentInPt : Option[SequentInPt] = None

	def prefSize : Dimension = {
		return new Dimension(treeLayout.getBounds().getBounds().getSize().width + 150 , treeLayout.getBounds().getBounds().getSize().height + 100)		
	}

	preferredSize = prefSize

	var seqTreeViewDialog : Option[SequentTreeViewDialog] = None//new SequentTreeViewDialog(null, concl(session.currentPT))

	def tree = treeLayout.getTree()

	def children(parent:SequentInPt) : Iterable[SequentInPt] = tree.getChildren(parent)

	def parent(child:SequentInPt, root:SequentInPt = tree.getRoot) : Option[SequentInPt] = {
		for (c <- children(root)){
			if(child == c) return Some(root)
			else {
				parent(child, c) match {
					case Some(res) => return Some(res)
					case None => ;
				}
			}
		}
		return None
	}

	def findMatchingSeqentInPt(seq:SequentInPt, root:SequentInPt = tree.getRoot) : Option[SequentInPt] = {
		if(root.eq(seq)) return Some(root)
		for (c <- children(root)){
			if(c.eq(seq)) return Some(c)
			else {
				findMatchingSeqentInPt(seq, c) match {
					case Some(res) => return Some(res)
					case None => ;
				}
			}
		}
		return None
	}

	def boundsOfNode(node:SequentInPt) : Rectangle2D.Double = treeLayout.getNodeBounds().get(node)

	private var id_counter = 0

	def resetIdCounter = {
		id_counter = 0
	}

	def returnId:Int = {
		id_counter += 1
		return id_counter
	}

	def createPTreeAux(proof: Prooftree, tree: DefaultTreeForTreeLayout[SequentInPt], root:SequentInPt, size:Int=20) : Unit = proof match {
		case Prooftreea(seq, r, list) => {
			val l = new SequentInPt(seq, r, returnId, size, None, session)
			tree.addChild(root, l)
			list.foreach( x => createPTreeAux(x, tree, l, size) )
		}
	}

	def createPTree(proof: Prooftree, size:Int=20)  : DefaultTreeForTreeLayout[SequentInPt] = proof match {
		case Prooftreea(seq, r, list) => {
			resetIdCounter
			val l = new SequentInPt(seq, r, returnId, size, None, session)
			val tree = new DefaultTreeForTreeLayout[SequentInPt](l)
			list.foreach( x => createPTreeAux(x, tree, l) )
			return tree
		}
	}


	listenTo(keys)
	reactions += {
		case KeyPressed(_, Key.Up, _, _) => moveUp
		case KeyPressed(_, Key.Down, _, _) => moveDown
		case KeyPressed(_, Key.Left, _, _) => moveLeft
		case KeyPressed(_, Key.Right, _, _) => moveRight
		case KeyReleased(_, Key.Space, _, _)=>
			selectedSequentInPt match {
				case Some(seq) => popup.show(seq, 20, 20)
				case None => ;
			}
		case KeyReleased(_, Key.A, _, _) => addAbove
		case KeyReleased(_, Key.F, _, _) => findPTa
		case KeyReleased(_, Key.C, _, _) => cut
		case KeyReleased(_, Key.D, _, _) => deleteAbove
		case KeyReleased(_, Key.X, _, _) => displayXa
	}

	def moveUp = {
		selectedSequentInPt match {
			case Some(seq) =>
				children(seq).headOption match {
					case Some(child) =>
						select(child)
					case None => println("up-no child")
				}
			case None => 
				select(tree.getRoot)
		}
	}

	def moveDown = {
		selectedSequentInPt match {
			case Some(seq) =>
				parent(seq) match {
					case Some(parent) =>
						select(parent)
					case None => println("down-no parent")
				}
			case None => 
				select(tree.getRoot)
		}
	}

	def moveRight = {
		selectedSequentInPt match {
			case Some(seq) =>
				parent(seq) match {
					case Some(parent) =>
						var flag = false
						var selected:Option[SequentInPt] = None
						for(c <-children(parent)){
							if(flag) selected = Some(c)
							if(c == seq) flag = true
						}
						selected match {
							case Some(s) => select(s)
							case None => 
								println("right-no sibling, moving down")
								moveDown
						}
					case None => println("right-no parent")
				}
			case None => 
				select(tree.getRoot)
		}
	}

	def moveLeft = {
		selectedSequentInPt match {
			case Some(seq) =>
				parent(seq) match {
					case Some(parent) =>
						var selected:Option[SequentInPt] = None
						var prev:Option[SequentInPt] = None
						for(c <-children(parent)){
							if(c == seq) selected = prev
							prev = Some(c)
						}
						selected match {
							case Some(s) => select(s)
							case None => 
								println("right-no sibling, moving up")
								moveUp
						}
					case None => moveUp
				}
			case None => 
				select(tree.getRoot)
		}
	}
	focusable = true

	protected def add(comp: SequentInPt, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)
		comp.ruleButton.peer.setSize(comp.ruleButton.peer.getPreferredSize)
		p.setSize(p.getPreferredSize)
		
		peer.add(p)
		peer.add(comp.ruleButton.peer)

		val b1 = boundsOfNode(comp)
		val yy = (b1.getMinY()).toInt-3
		var xmin = (b1.getMinX()).toInt
		var xmax = (b1.getMaxX()).toInt //+15

		for (child <- children(comp)) { 
			val b2 = boundsOfNode(child)
			if( (b2.getMinX()).toInt < xmin) xmin = (b2.getMinX()).toInt
			if( (b2.getMaxX()).toInt > xmax) xmax = (b2.getMaxX()).toInt
		}
		comp.ruleButton.peer.setLocation(xmax+5+OFFSET_X, yy-(comp.ruleIcon.getIconHeight/2)+OFFSET_Y)
		listenTo(comp.seqButton)
		listenTo(comp.ruleButton)
	}

	protected def add(comp: Component, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)
		//comp.ruleButton.peer.setLocation(x+p.getPreferredSize.width+OFFSET_X, y+OFFSET_Y-p.getPreferredSize.height/2)
		//comp.ruleButton.peer.setSize(comp.ruleButton.peer.getPreferredSize)
		p.setSize(p.getPreferredSize)
		peer.add(p)
		listenTo(comp)
	}


	listenTo(mouse.clicks)
	reactions += {
		case ButtonClicked(b) =>
			b.text match {
				case "rule" =>
					val pressed = b.asInstanceOf[RuleInPtButton]
					if(pressed.parent.seqButton.visible){
						// println("old bounds: " + boundsOfNode(pressed.parent))
						// println("old height: " + pressed.parent.height)
						pressed.parent.contents -= pressed.parent.seqButton
						pressed.parent.preferredSize = pressed.parent.macroPtPanel.get.preferredSize
						pressed.parent.contents += pressed.parent.macroPtPanel.get
						// println("new bounds: " + boundsOfNode(pressed.parent))
						// println("new height: " + pressed.parent.height)

					} else {
						// println("old bounds: " + boundsOfNode(pressed.parent))
						// println("old height: " + pressed.parent.height)
						pressed.parent.contents -= pressed.parent.macroPtPanel.get
						pressed.parent.preferredSize = pressed.parent.seqButton.preferredSize
						pressed.parent.contents += pressed.parent.seqButton
						// println("new bounds: " + boundsOfNode(pressed.parent))
						// println("new height: " + pressed.parent.height)
					}
					pressed.parent.seqButton.visible = !pressed.parent.seqButton.visible

					repaint()
					//update()


				case "sequent" if editable =>
					val pressed = b.asInstanceOf[SequentInPtButton]
					select(pressed.parent)

					seqTreeViewDialog match {
						case Some(dialog) => 
							dialog.seqPanel.currentSequent = pressed.parent.seq
							dialog.seqPanel.rebuild()
						case None => ;
					}

					popup.peer.show(b.peer, 20, 20)
				case _ =>
					println("what could this possibly be????")
					//unselect()

			}
		case m : MouseClicked => 
			requestFocus
			unselect()

	}


	def addCallback(panel:scala.swing.Panel)(callback: () => Unit){
		listenTo(panel)
		reactions += { case scala.swing.event.UIElementHidden(`panel`) => 	    	
			callback()
			deafTo(panel)
		}
	}

	val popup = new PopupMenu

	val copy = new MenuItem(Action("Copy") {
		selectedSequentInPt match {
			case Some(seqIPT) => 
				// adapted from http://www.avajava.com/tutorials/lessons/how-do-i-copy-a-string-to-the-clipboard.html
				val str = sequentToString(seqIPT.seq, PrintCalc.ASCII)
				val toolkit = Toolkit.getDefaultToolkit()
				val clipboard = toolkit.getSystemClipboard()
				val strSel = new StringSelection(str)
				clipboard.setContents(strSel, null)
		}
		requestFocus
	})
	popup.contents += copy

	val copy_isa_se = new MenuItem(Action("Copy (Isabelle SE)") {
		selectedSequentInPt match {
			case Some(seqIPT) => 
				// adapted from http://www.avajava.com/tutorials/lessons/how-do-i-copy-a-string-to-the-clipboard.html
				val str = sequentToString(seqIPT.seq, PrintCalc.ISABELLE_SE)
				val toolkit = Toolkit.getDefaultToolkit()
				val clipboard = toolkit.getSystemClipboard()
				val strSel = new StringSelection(str)
				clipboard.setContents(strSel, null)
			case None => ;
		}
		requestFocus
	})
	popup.contents += copy_isa_se

	
	val addAssm = new MenuItem(Action("Add as assm") {
		selectedSequentInPt match {
			case Some(seqIPT) => session.addAssm(seqIPT.seq)
			case None => ;
		}
		requestFocus
	})
	popup.contents += addAssm

	val merge = new MenuItem(Action("Merge above") {
		selectedSequentInPt match {
			case Some(selSeq) =>
				session.findMatches(selSeq.seq) match {
					case List() => 
						Dialog.showMessage(null, "No matching pt found!", "Error")
					case (x::xs) => 
						session.currentPT = session.mergePTs(x, selSeq, tree.getRoot(), children)
						session.savePT()

						update()
						//session.addPT()
				}
			case None => ;
				
		}
		requestFocus
	})
	popup.contents += merge


	def findPTa = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				tree.isLeaf(selSeq) match {
					case true => popupPanel match {
						case None => 
							new PSDialog(depth=session.proofDepth, locale=session.currentLocale, seq=selSeq.seq).pt match {
								case Some(r) => 
									session.currentPT = session.mergePTs(r, selSeq, tree.getRoot(), children)
									session.savePT()
									update()
								case None =>
									Dialog.showMessage(null, "PT couldn't be found", "Error")
							}
						case Some(panel) =>
							val ps = new ProofSearchPopup(depth=session.proofDepth, locale=session.currentLocale, seq=selSeq.seq)
							ps.open()
							panel.displayPopup(ps)
							ps.requestFocus
							addCallback(ps)(()=>{
								ps.pt match {
									case Some(r) => 
										session.currentPT = session.mergePTs(r, selSeq, tree.getRoot(), children)
										session.savePT()
										update()
									case None =>
										if(!ps.cancelled){
											val error = new ErrorPopup("Proof tree couldn't be found")
											panel.displayPopup(error)
											error.requestFocus
											addCallback(error)(()=> requestFocus)
										}
								}
								requestFocus
							})
					}
				case false => popupPanel match {
					case None => Dialog.showMessage(null, "Sequent not a premise", "Error")
					case Some(panel) =>
						val error = new ErrorPopup("The selected sequent is not a leaf. Please use 'Delete above' to proceed.")
						panel.displayPopup(error)
						error.requestFocus
						addCallback(error)(()=> requestFocus)
				}
			}
			case None => ;
				
		}
	}

	val findPT = new MenuItem(new Action("FindPT") {
		accelerator = Some(getKeyStroke('f'))
		def apply = findPTa
	})
	popup.contents += findPT


	def addAbove = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				popupPanel match {
					case None =>
						if(tree.isLeaf(selSeq)) {
							val list = derAll(session.currentLocale, selSeq.seq, Nil, session.currentRuleList).filter{case (r, l) => r != RuleZera(Prem())} ++ derAllM(session.currentLocale, selSeq.seq, session.macroBuffer.toList)
							new SequentListDialog(list=list, session=session).pair match {
								case None => ;
								case Some((rule, derList)) =>
									val m = derList.map(x => Prooftreea(x, RuleZera(Prem()), Nil) )
									val pt = rule match {
										case RuleZera(r) => if (m.length > 0) m(0) else Prooftreea( selSeq.seq, RuleZera(r), Nil )
										case Fail() => m(0)
										case r => Prooftreea( selSeq.seq, r, m )
									}
									session.currentPT = session.mergePTs(pt, selSeq, tree.getRoot(), children)
									session.savePT()
									update()

							}
						} 
						else Dialog.showMessage(null, "The sequent is not a leaf please delete pt above to proceed", "Error")

					case Some(panel) =>
						if(tree.isLeaf(selSeq)){
							val list = derAll(session.currentLocale, selSeq.seq, Nil, session.currentRuleList).filter{case (r, l) => r != RuleZera(Prem())} ++ derAllM(session.currentLocale, selSeq.seq, session.macroBuffer.toList)
							val ruleList = new SequentListPopup(list)
							panel.displayPopup(ruleList, true)
							ruleList.ruleListTable.requestFocus
							//ruleList.ruleListTable.peer.changeSelection(0, 0, false, false)
							
							addCallback(ruleList)(()=>{
								ruleList.pair match {
									case None => ;
									case Some((rule, derList)) =>
										val m = derList.map(x => Prooftreea(x, RuleZera(Prem()), Nil) )
										val pt = rule match {
											case RuleZera(r) => if (m.length > 0) m(0) else Prooftreea( selSeq.seq, RuleZera(r), Nil )
											case Fail() => m(0)
											case r => Prooftreea( selSeq.seq, r, m )
										}
										session.currentPT = session.mergePTs(pt, selSeq, tree.getRoot(), children)
										session.savePT()
										update()
								}
								requestFocus
							})
						}
						else {
							val error = new ErrorPopup("The selected sequent is not a leaf. Please use 'Delete above' to proceed.")
							panel.displayPopup(error)
							error.requestFocus
							addCallback(error)(()=> requestFocus)
						}
				}
			case None => ;
		}
	}



	val add1 = new MenuItem(new Action("Add above") {
		accelerator = Some(getKeyStroke('a'))
		def apply = addAbove
	})
	popup.contents += add1

	def addBelow() = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				if(tree.getRoot() == selSeq) {
					new SequentInputDialog().sequent match {
						case Some(s) =>
							//println(selSeq.seq)
							//println(derAll(selSeq.seq).filter{ case (r,l) => l.exists(_ == s)})
							val pair = derAll(session.currentLocale, s).filter{ case (r,l) => l.exists(_ == selSeq.seq)} match {
								case List() => None
								case List((rule, derList)) => Some(rule, derList)
								case list => new RuleSelectDialog(list=list).pair 
							}

							pair match {
								case None => Dialog.showMessage(null, "No rule found for the given sequent", "Error")
								case Some((rule, derList)) =>
									val rest = session.rebuildFromPoint(selSeq, children)

									val intersection = derList.map(x => {if(x != concl(rest)) Prooftreea(x, RuleZera(Prem()), List()) else rest})
									session.currentPT = rule match {
										case RuleZera(r) => Prooftreea(s, RuleZera(r), List())
										case Fail() => Prooftreea(s, RuleZera(Prem()), List())
										case r => Prooftreea(s, r, intersection)
									}
									session.savePT()
									update()
							}
						case None => Dialog.showMessage(null, "Invalid sequent entered", "Error")
					}
				} 
				else Dialog.showMessage(null, "The sequent is not a leaf please delete pt above to proceed", "Error")
			case None => ;
		}
		requestFocus
	}


	val add2 = new MenuItem(new Action("Add below") {
		accelerator = Some(getKeyStroke('A'))
		def apply = addBelow()		
	})
	//popup.contents += add2


	def deleteAbove = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				session.currentPT = session.deleteAbove(selSeq, tree.getRoot(), children)
				session.savePT()
				update()
			case None => ;
		}
		requestFocus
	}

	val delete1 = new MenuItem(new Action("Delete above") {
		accelerator = Some(getKeyStroke('d'))
		def apply = deleteAbove
	})
	popup.contents += delete1

	val delete2 = new MenuItem(new Action("Delete below") {
		accelerator = Some(getKeyStroke('D'))
		def apply = {
			selectedSequentInPt match {
				case Some(selSeq) =>
					session.currentPT = session.rebuildFromPoint(selSeq, children)
					session.savePT()
					//update()
				case None => ;
			}
			requestFocus
		}
	})
	popup.contents += delete2


	def cut() = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				if(tree.isLeaf(selSeq)) { 
					popupPanel match {
						case None =>
							new FormulaInputDialog().formula match {
								case Some(f) =>
									val lSeq = Sequenta(ant(selSeq.seq), Structure_Formula(f))
									val rSeq = Sequenta(Structure_Formula(f), consq(selSeq.seq))
									val resR = Prooftreea( rSeq, RuleZera(Prem()), List() )
									val resL = Prooftreea( lSeq, RuleZera(Prem()), List() )
									val mPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
									session.currentPT = session.mergePTs(mPT, selSeq, tree.getRoot(), children)
								  session.savePT()
								  update()
							}
						case Some(panel) =>
							def formulaToString_Aux(in:Formula) = formulaToString(in) 
							val formulaInputPopup = new ParsePopup[Formula](parseFormula, formulaToString_Aux,  "FORMULA")
							panel.displayPopup(formulaInputPopup)
							formulaInputPopup.inputField.peer.requestFocus

							addCallback(formulaInputPopup)(()=>{
								formulaInputPopup.parsed match {
									case Some(f) =>
										val lSeq = Sequenta(ant(selSeq.seq), Structure_Formula(f))
										val rSeq = Sequenta(Structure_Formula(f), consq(selSeq.seq))
										val resR = Prooftreea( rSeq, RuleZera(Prem()), List() )
										val resL = Prooftreea( lSeq, RuleZera(Prem()), List() )
										val mPT = Prooftreea(selSeq.seq, RuleCuta(SingleCut()), List(resL, resR))
										session.currentPT = session.mergePTs(mPT, selSeq, tree.getRoot(), children)
									  session.savePT()
									  update()
									case None => ;
								}
								requestFocus
							})
					}
				}
				else {
					popupPanel match {
						case Some(panel) => 
							val error = new ErrorPopup("The selected sequent is not a leaf. Please use 'Delete above' to proceed.")
							panel.displayPopup(error)
							error.requestFocus
							addCallback(error)(()=> requestFocus)
						case None => ;
					}
				}
			case None => ;
		}
	}

	val cutt = new MenuItem(new Action("Apply Cut") {
		accelerator = Some(getKeyStroke('c'))
		def apply = cut()
	})
	//popup.contents += cutt


	val refl_forwK = new MenuItem(new Action("Apply Refl_forwK") {
		def apply = {
			selectedSequentInPt match {
				case Some(selSeq) =>
					if(tree.isLeaf(selSeq)) { popupPanel match {
						case None =>
							new AgentInputDialog().agent match {
								case Some(a) =>
									val list = derAll(LAgent(a)::session.currentLocale, selSeq.seq, Nil, session.currentRuleList).filter{case (r, l) => r == RuleKnowledgea(Refl_ForwK())} ++ derAllM(session.currentLocale, selSeq.seq, session.macroBuffer.toList)
									list match {
										case (rule, derList)::Nil =>
											val m = derList.map(x => Prooftreea(x, RuleZera(Prem()), List()) )
											val pt = rule match {
												case RuleZera(r) => m(0)
												case Fail() => m(0)
												case ru => Prooftreea( selSeq.seq, ru, m )
											}
											session.currentPT = session.mergePTs(pt, selSeq, tree.getRoot(), children)
											session.savePT()
											update()
										case Nil => ;
									}
							}
						case Some(panel) => 
							def agentToString_Aux(in:Agent) = agentToString(in) 
							val agentInputPopup = new ParsePopup[Agent](parseAgent, agentToString_Aux,  "AGENT")
							panel.displayPopup(agentInputPopup)
							
							addCallback(agentInputPopup)(()=>{
								agentInputPopup.parsed match {
									case Some(a) =>
										val list = derAll(LAgent(a)::session.currentLocale, selSeq.seq, Nil, session.currentRuleList).filter{case (r, l) => r == RuleKnowledgea(Refl_ForwK())} ++ derAllM(session.currentLocale, selSeq.seq, session.macroBuffer.toList)
										list match {
											case (rule, derList)::Nil =>
												val m = derList.map(x => Prooftreea(x, RuleZera(Prem()), List()) )
												val pt = rule match {
													case RuleZera(r) => m(0)
													case Fail() => m(0)
													case ru => Prooftreea( selSeq.seq, ru, m )
												}
												session.currentPT = session.mergePTs(pt, selSeq, tree.getRoot(), children)
												session.savePT()
												update()
											case Nil => 
										}
									case None => ;
								}
							})
						}
					}
				case None => ;
			}
			requestFocus
		}
	})
	//popup.contents += refl_forwK

	val displaySeqTree = new MenuItem(new Action("Display Sequent tree") {
		accelerator = Some(getKeyStroke('t'))
		def apply = {
			seqTreeViewDialog match {
				case None =>
					displayTactic( selectedSequentInPt.get.seq )
					val dialog = new SequentTreeViewDialog(null, selectedSequentInPt.get.seq)
					seqTreeViewDialog = Some(dialog)
				case Some(dialog) => 
					dialog.seqPanel.currentSequent = selectedSequentInPt.get.seq
					dialog.seqPanel.rebuild()
					dialog.open()
			}
			requestFocus
		}
	})
	popup.contents += displaySeqTree

	def displayXa = {
		selectedSequentInPt match {
			case Some(selSeq) =>
				val dialog = new SequentTreeViewDialog(null, selectedSequentInPt.get.seq, true)
				dialog.tuple match {
					case Some((seq, Some(struct))) => 
						displayTactic( seq, dialog.fresh ) match {
						case Some(pt) =>
							val mPT = replace_SFAtprop_into_PT(dialog.fresh, struct, pt)
							session.currentPT = session.mergePTs(mPT, selectedSequentInPt.get, tree.getRoot(), children)
							session.savePT()
							update()
						case None => ;
					}

					case None => ;
				}
			case None => ;
		}
		
		requestFocus
	}

	val displayX = new MenuItem(new Action("Display X") {
		accelerator = Some(getKeyStroke('x'))
		def apply = displayXa
	})
	//popup.contents += displayX

	popup.contents += new swing.Menu("Apply Rule") {
		contents += cutt
		contents += refl_forwK
		contents += displayX
	}

	/*val replaceIntPT = new MenuItem(new Action("Replace into PT") {
		def apply = {
			selectedSequentInPt match {
			case Some(selSeq) =>
				session.findMatchesMacro(selSeq.seq) match {
					case List() => 
						Dialog.showMessage(null, "No matching pt found!", "Error")
					case (x::xs) =>
						session.currentPT = replaceIntoPT(selSeq.seq, x)
						session.addPT()

						update()
						//session.addPT()
				}
				
			}
		}
	})
	popup.contents += replaceIntPT*/


	def unselect() : Unit = {
		//root.sel = false

		selectedSequentInPt match {
			case Some(seq) => seq.seqButton.border = Swing.EmptyBorder(0,0,0,0)
			case None => ;
		}
		selectedSequentInPt = None
	}

	def select(seq:SequentInPt = tree.getRoot) : Unit = {
		unselect()
		seq.seqButton.border = Swing.LineBorder(Color.black)
		selectedSequentInPt = Some(seq)
	}

	def update() = {
		println("update")
		peer.removeAll()
		treeLayout = new TreeLayout[SequentInPt](createPTree(session.currentPT), nodeExtentProvider, configuration)
		build()
		peer.revalidate()
		peer.repaint()
		val s = treeLayout.getBounds().getBounds().getSize()
		preferredSize = prefSize
		selectedSequentInPt match {
			case Some(seq) => 
				findMatchingSeqentInPt(seq) match {
					case Some(sel) => select(sel)
					case None => unselect
				}
			case None => 	;
		}
		OFFSET_X_old = 0
		OFFSET_Y_old = 0
	}

	def build() = {
		for (sequentInPt <- treeLayout.getNodeBounds().keySet()) {
			val box = boundsOfNode(sequentInPt)
			add(sequentInPt, (box.x).toInt, (box.y).toInt)
		}
	}

	def paintSequentInPt(comp: SequentInPt, x: Int, y: Int): Unit = {
		val p = comp.peer
		p.setLocation(x+OFFSET_X, y+OFFSET_Y)

		val b1 = boundsOfNode(comp)
		val yy = (b1.getMinY()).toInt-3
		var xmin = (b1.getMinX()).toInt
		var xmax = (b1.getMaxX()).toInt //+15


		for (child <- children(comp)) { 
			val b2 = boundsOfNode(child)
			if( (b2.getMinX()).toInt < xmin) xmin = (b2.getMinX()).toInt
			if( (b2.getMaxX()).toInt > xmax) xmax = (b2.getMaxX()).toInt
		}

		comp.ruleButton.peer.setLocation(xmax+5+OFFSET_X, yy-(comp.ruleIcon.getIconHeight/2)+OFFSET_Y)
	}

	
	override def repaint() = {
		println("repaint!!!")
		for (sequentInPt <- treeLayout.getNodeBounds().keySet()) {
			val box = boundsOfNode(sequentInPt)
			paintSequentInPt(sequentInPt, (box.x).toInt, (box.y).toInt)
		}

		// selectedSequentInPt match {
		// 	case Some(seq) => 
		// 		println("selseq is not none")
		// 		select(seq)
		// 	case None => 	println("selseq is none")
		// }
	}

	def paintEdges(g:Graphics2D, parent:SequentInPt) : Unit = {
		val b1 = boundsOfNode(parent)
		val y = (b1.getMinY()).toInt-3
		var xmin = (b1.getMinX()).toInt
		var xmax = (b1.getMaxX()).toInt //+15

		for (child <- children(parent)) { 
			val b2 = boundsOfNode(child)
			if( (b2.getMinX()).toInt < xmin) xmin = (b2.getMinX()).toInt
			if( (b2.getMaxX()).toInt > xmax) xmax = (b2.getMaxX()).toInt

			paintEdges(g, child)
		}
		g.drawLine( xmin+OFFSET_X, y+OFFSET_Y, xmax+OFFSET_X, y+OFFSET_Y )
	}

	var OFFSET_X_old = OFFSET_X
	var OFFSET_Y_old = OFFSET_Y
	override def paintComponent(g: Graphics2D) = {
		super.paintComponent(g)
		paintEdges(g, tree.getRoot())
		//only repaints labels (ie repositions on peer) positioning if the OFFSET_X or OFFSET_Y changed
		if(OFFSET_X_old != OFFSET_X || OFFSET_Y_old != OFFSET_Y){
			repaint()
			OFFSET_X_old = OFFSET_X
			OFFSET_Y_old = OFFSET_Y
		}
	}
}

class SequentInPtNodeExtentProvider extends org.abego.treelayout.NodeExtentProvider[SequentInPt] {
	def getWidth(treeNode:SequentInPt) = treeNode.width
	def getHeight(treeNode:SequentInPt) = treeNode.height
}
