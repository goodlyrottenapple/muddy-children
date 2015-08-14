object DEAK {

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

trait equal[A] {
  val `DEAK.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`DEAK.equal`(a, b)

implicit def equal_bool: equal[Boolean] = new equal[Boolean] {
  val `DEAK.equal` = (a: Boolean, b: Boolean) => equal_boola(a, b)
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

implicit def equal_list[A : equal]: equal[List[A]] = new equal[List[A]] {
  val `DEAK.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

implicit def equal_char: equal[Char] = new equal[Char] {
  val `DEAK.equal` = (a: Char, b: Char) => a == b
}

abstract sealed class Structure_Action_Structure_Op
final case class Structure_BackA() extends Structure_Action_Structure_Op
final case class Structure_ForwA() extends Structure_Action_Structure_Op

def equal_Structure_Action_Structure_Op(x0: Structure_Action_Structure_Op,
 x1: Structure_Action_Structure_Op):
      Boolean
  =
  (x0, x1) match {
  case (Structure_BackA(), Structure_ForwA()) => false
  case (Structure_ForwA(), Structure_BackA()) => false
  case (Structure_ForwA(), Structure_ForwA()) => true
  case (Structure_BackA(), Structure_BackA()) => true
}

abstract sealed class Structure_Agent_Structure_Op
final case class Structure_BackK() extends Structure_Agent_Structure_Op
final case class Structure_ForwK() extends Structure_Agent_Structure_Op

def equal_Structure_Agent_Structure_Op(x0: Structure_Agent_Structure_Op,
x1: Structure_Agent_Structure_Op):
      Boolean
  =
  (x0, x1) match {
  case (Structure_BackK(), Structure_ForwK()) => false
  case (Structure_ForwK(), Structure_BackK()) => false
  case (Structure_ForwK(), Structure_ForwK()) => true
  case (Structure_BackK(), Structure_BackK()) => true
}

abstract sealed class Structure_Zer_Op
final case class Structure_Neutral() extends Structure_Zer_Op

def equal_Structure_Zer_Op(x0: Structure_Zer_Op, x1: Structure_Zer_Op): Boolean
  =
  (x0, x1) match {
  case (Structure_Neutral(), Structure_Neutral()) => true
}

abstract sealed class Structure_Bin_Op
final case class Structure_Comma() extends Structure_Bin_Op
final case class Structure_ImpL() extends Structure_Bin_Op
final case class Structure_ImpR() extends Structure_Bin_Op

def equal_Structure_Bin_Op(x0: Structure_Bin_Op, x1: Structure_Bin_Op): Boolean
  =
  (x0, x1) match {
  case (Structure_ImpL(), Structure_ImpR()) => false
  case (Structure_ImpR(), Structure_ImpL()) => false
  case (Structure_Comma(), Structure_ImpR()) => false
  case (Structure_ImpR(), Structure_Comma()) => false
  case (Structure_Comma(), Structure_ImpL()) => false
  case (Structure_ImpL(), Structure_Comma()) => false
  case (Structure_ImpR(), Structure_ImpR()) => true
  case (Structure_ImpL(), Structure_ImpL()) => true
  case (Structure_Comma(), Structure_Comma()) => true
}

abstract sealed class Formula_Action_Formula_Op
final case class Formula_BboxA() extends Formula_Action_Formula_Op
final case class Formula_BdiamA() extends Formula_Action_Formula_Op
final case class Formula_FboxA() extends Formula_Action_Formula_Op
final case class Formula_FdiamA() extends Formula_Action_Formula_Op

abstract sealed class Formula_Agent_Formula_Op
final case class Formula_BboxK() extends Formula_Agent_Formula_Op
final case class Formula_BdiamK() extends Formula_Agent_Formula_Op
final case class Formula_FboxK() extends Formula_Agent_Formula_Op
final case class Formula_FdiamK() extends Formula_Agent_Formula_Op

abstract sealed class Formula_Zer_Op
final case class Formula_Bot() extends Formula_Zer_Op
final case class Formula_Top() extends Formula_Zer_Op

abstract sealed class Formula_Bin_Op
final case class Formula_And() extends Formula_Bin_Op
final case class Formula_DImpL() extends Formula_Bin_Op
final case class Formula_DImpR() extends Formula_Bin_Op
final case class Formula_ImpL() extends Formula_Bin_Op
final case class Formula_ImpR() extends Formula_Bin_Op
final case class Formula_Or() extends Formula_Bin_Op

abstract sealed class Atprop
final case class Atpropa(a: List[Char]) extends Atprop
final case class Atprop_Freevar(a: List[Char]) extends Atprop

abstract sealed class Action
final case class Actiona(a: List[Char]) extends Action
final case class Action_Freevar(a: List[Char]) extends Action

abstract sealed class Agent
final case class Agenta(a: List[Char]) extends Agent
final case class Agent_Freevar(a: List[Char]) extends Agent

abstract sealed class Formula
final case class Formula_Action(a: Action) extends Formula
final case class
  Formula_Action_Formula(a: Formula_Action_Formula_Op, b: Action, c: Formula)
  extends Formula
final case class Formula_Agent(a: Agent) extends Formula
final case class
  Formula_Agent_Formula(a: Formula_Agent_Formula_Op, b: Agent, c: Formula)
  extends Formula
final case class Formula_Atprop(a: Atprop) extends Formula
final case class Formula_Bin(a: Formula, b: Formula_Bin_Op, c: Formula) extends
  Formula
final case class Formula_Freevar(a: List[Char]) extends Formula
final case class Formula_Precondition(a: Action) extends Formula
final case class Formula_Zer(a: Formula_Zer_Op) extends Formula

abstract sealed class Structure
final case class
  Structure_Action_Structure(a: Structure_Action_Structure_Op, b: Action,
                              c: Structure)
  extends Structure
final case class
  Structure_Agent_Structure(a: Structure_Agent_Structure_Op, b: Agent,
                             c: Structure)
  extends Structure
final case class Structure_Bigcomma(a: List[Structure]) extends Structure
final case class Structure_Bin(a: Structure, b: Structure_Bin_Op, c: Structure)
  extends Structure
final case class Structure_Formula(a: Formula) extends Structure
final case class Structure_Freevar(a: List[Char]) extends Structure
final case class Structure_Phi(a: Action) extends Structure
final case class Structure_Zer(a: Structure_Zer_Op) extends Structure

def equal_Formula_Action_Formula_Op(x0: Formula_Action_Formula_Op,
                                     x1: Formula_Action_Formula_Op):
      Boolean
  =
  (x0, x1) match {
  case (Formula_FboxA(), Formula_FdiamA()) => false
  case (Formula_FdiamA(), Formula_FboxA()) => false
  case (Formula_BdiamA(), Formula_FdiamA()) => false
  case (Formula_FdiamA(), Formula_BdiamA()) => false
  case (Formula_BdiamA(), Formula_FboxA()) => false
  case (Formula_FboxA(), Formula_BdiamA()) => false
  case (Formula_BboxA(), Formula_FdiamA()) => false
  case (Formula_FdiamA(), Formula_BboxA()) => false
  case (Formula_BboxA(), Formula_FboxA()) => false
  case (Formula_FboxA(), Formula_BboxA()) => false
  case (Formula_BboxA(), Formula_BdiamA()) => false
  case (Formula_BdiamA(), Formula_BboxA()) => false
  case (Formula_FdiamA(), Formula_FdiamA()) => true
  case (Formula_FboxA(), Formula_FboxA()) => true
  case (Formula_BdiamA(), Formula_BdiamA()) => true
  case (Formula_BboxA(), Formula_BboxA()) => true
}

def equal_Formula_Agent_Formula_Op(x0: Formula_Agent_Formula_Op,
                                    x1: Formula_Agent_Formula_Op):
      Boolean
  =
  (x0, x1) match {
  case (Formula_FboxK(), Formula_FdiamK()) => false
  case (Formula_FdiamK(), Formula_FboxK()) => false
  case (Formula_BdiamK(), Formula_FdiamK()) => false
  case (Formula_FdiamK(), Formula_BdiamK()) => false
  case (Formula_BdiamK(), Formula_FboxK()) => false
  case (Formula_FboxK(), Formula_BdiamK()) => false
  case (Formula_BboxK(), Formula_FdiamK()) => false
  case (Formula_FdiamK(), Formula_BboxK()) => false
  case (Formula_BboxK(), Formula_FboxK()) => false
  case (Formula_FboxK(), Formula_BboxK()) => false
  case (Formula_BboxK(), Formula_BdiamK()) => false
  case (Formula_BdiamK(), Formula_BboxK()) => false
  case (Formula_FdiamK(), Formula_FdiamK()) => true
  case (Formula_FboxK(), Formula_FboxK()) => true
  case (Formula_BdiamK(), Formula_BdiamK()) => true
  case (Formula_BboxK(), Formula_BboxK()) => true
}

def equal_Formula_Zer_Op(x0: Formula_Zer_Op, x1: Formula_Zer_Op): Boolean =
  (x0, x1) match {
  case (Formula_Bot(), Formula_Top()) => false
  case (Formula_Top(), Formula_Bot()) => false
  case (Formula_Top(), Formula_Top()) => true
  case (Formula_Bot(), Formula_Bot()) => true
}

def equal_Formula_Bin_Op(x0: Formula_Bin_Op, x1: Formula_Bin_Op): Boolean =
  (x0, x1) match {
  case (Formula_ImpR(), Formula_Or()) => false
  case (Formula_Or(), Formula_ImpR()) => false
  case (Formula_ImpL(), Formula_Or()) => false
  case (Formula_Or(), Formula_ImpL()) => false
  case (Formula_ImpL(), Formula_ImpR()) => false
  case (Formula_ImpR(), Formula_ImpL()) => false
  case (Formula_DImpR(), Formula_Or()) => false
  case (Formula_Or(), Formula_DImpR()) => false
  case (Formula_DImpR(), Formula_ImpR()) => false
  case (Formula_ImpR(), Formula_DImpR()) => false
  case (Formula_DImpR(), Formula_ImpL()) => false
  case (Formula_ImpL(), Formula_DImpR()) => false
  case (Formula_DImpL(), Formula_Or()) => false
  case (Formula_Or(), Formula_DImpL()) => false
  case (Formula_DImpL(), Formula_ImpR()) => false
  case (Formula_ImpR(), Formula_DImpL()) => false
  case (Formula_DImpL(), Formula_ImpL()) => false
  case (Formula_ImpL(), Formula_DImpL()) => false
  case (Formula_DImpL(), Formula_DImpR()) => false
  case (Formula_DImpR(), Formula_DImpL()) => false
  case (Formula_And(), Formula_Or()) => false
  case (Formula_Or(), Formula_And()) => false
  case (Formula_And(), Formula_ImpR()) => false
  case (Formula_ImpR(), Formula_And()) => false
  case (Formula_And(), Formula_ImpL()) => false
  case (Formula_ImpL(), Formula_And()) => false
  case (Formula_And(), Formula_DImpR()) => false
  case (Formula_DImpR(), Formula_And()) => false
  case (Formula_And(), Formula_DImpL()) => false
  case (Formula_DImpL(), Formula_And()) => false
  case (Formula_Or(), Formula_Or()) => true
  case (Formula_ImpR(), Formula_ImpR()) => true
  case (Formula_ImpL(), Formula_ImpL()) => true
  case (Formula_DImpR(), Formula_DImpR()) => true
  case (Formula_DImpL(), Formula_DImpL()) => true
  case (Formula_And(), Formula_And()) => true
}

def equal_Atpropa(x0: Atprop, x1: Atprop): Boolean = (x0, x1) match {
  case (Atpropa(x1), Atprop_Freevar(x2)) => false
  case (Atprop_Freevar(x2), Atpropa(x1)) => false
  case (Atprop_Freevar(x2), Atprop_Freevar(y2)) => equal_lista[Char](x2, y2)
  case (Atpropa(x1), Atpropa(y1)) => equal_lista[Char](x1, y1)
}

def equal_Actiona(x0: Action, x1: Action): Boolean = (x0, x1) match {
  case (Actiona(x1), Action_Freevar(x2)) => false
  case (Action_Freevar(x2), Actiona(x1)) => false
  case (Action_Freevar(x2), Action_Freevar(y2)) => equal_lista[Char](x2, y2)
  case (Actiona(x1), Actiona(y1)) => equal_lista[Char](x1, y1)
}

def equal_Agenta(x0: Agent, x1: Agent): Boolean = (x0, x1) match {
  case (Agenta(x1), Agent_Freevar(x2)) => false
  case (Agent_Freevar(x2), Agenta(x1)) => false
  case (Agent_Freevar(x2), Agent_Freevar(y2)) => equal_lista[Char](x2, y2)
  case (Agenta(x1), Agenta(y1)) => equal_lista[Char](x1, y1)
}

def equal_Formulaa(x0: Formula, x1: Formula): Boolean = (x0, x1) match {
  case (Formula_Precondition(x8), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Precondition(x8)) => false
  case (Formula_Freevar(x7), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Precondition(x8)) => false
  case (Formula_Precondition(x8), Formula_Freevar(x7)) => false
  case (Formula_Bin(x61, x62, x63), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Bin(x61, x62, x63)) => false
  case (Formula_Bin(x61, x62, x63), Formula_Precondition(x8)) => false
  case (Formula_Precondition(x8), Formula_Bin(x61, x62, x63)) => false
  case (Formula_Bin(x61, x62, x63), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Bin(x61, x62, x63)) => false
  case (Formula_Atprop(x5), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Precondition(x8)) => false
  case (Formula_Precondition(x8), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Bin(x61, x62, x63)) => false
  case (Formula_Bin(x61, x62, x63), Formula_Atprop(x5)) => false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Agent_Formula(x41, x42, x43)) => false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Precondition(x8)) => false
  case (Formula_Precondition(x8), Formula_Agent_Formula(x41, x42, x43)) => false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Agent_Formula(x41, x42, x43)) => false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Bin(x61, x62, x63)) =>
    false
  case (Formula_Bin(x61, x62, x63), Formula_Agent_Formula(x41, x42, x43)) =>
    false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Agent_Formula(x41, x42, x43)) => false
  case (Formula_Agent(x3), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Precondition(x8)) => false
  case (Formula_Precondition(x8), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Bin(x61, x62, x63)) => false
  case (Formula_Bin(x61, x62, x63), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Agent_Formula(x41, x42, x43)) => false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Agent(x3)) => false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Action_Formula(x21, x22, x23)) => false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Precondition(x8)) =>
    false
  case (Formula_Precondition(x8), Formula_Action_Formula(x21, x22, x23)) =>
    false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Action_Formula(x21, x22, x23)) => false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Bin(x61, x62, x63)) =>
    false
  case (Formula_Bin(x61, x62, x63), Formula_Action_Formula(x21, x22, x23)) =>
    false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Action_Formula(x21, x22, x23)) => false
  case (Formula_Action_Formula(x21, x22, x23),
         Formula_Agent_Formula(x41, x42, x43))
    => false
  case (Formula_Agent_Formula(x41, x42, x43),
         Formula_Action_Formula(x21, x22, x23))
    => false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Action_Formula(x21, x22, x23)) => false
  case (Formula_Action(x1), Formula_Zer(x9)) => false
  case (Formula_Zer(x9), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Precondition(x8)) => false
  case (Formula_Precondition(x8), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Freevar(x7)) => false
  case (Formula_Freevar(x7), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Bin(x61, x62, x63)) => false
  case (Formula_Bin(x61, x62, x63), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Atprop(x5)) => false
  case (Formula_Atprop(x5), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Agent_Formula(x41, x42, x43)) => false
  case (Formula_Agent_Formula(x41, x42, x43), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Agent(x3)) => false
  case (Formula_Agent(x3), Formula_Action(x1)) => false
  case (Formula_Action(x1), Formula_Action_Formula(x21, x22, x23)) => false
  case (Formula_Action_Formula(x21, x22, x23), Formula_Action(x1)) => false
  case (Formula_Zer(x9), Formula_Zer(y9)) => equal_Formula_Zer_Op(x9, y9)
  case (Formula_Precondition(x8), Formula_Precondition(y8)) =>
    equal_Actiona(x8, y8)
  case (Formula_Freevar(x7), Formula_Freevar(y7)) => equal_lista[Char](x7, y7)
  case (Formula_Bin(x61, x62, x63), Formula_Bin(y61, y62, y63)) =>
    equal_Formulaa(x61, y61) &&
      (equal_Formula_Bin_Op(x62, y62) && equal_Formulaa(x63, y63))
  case (Formula_Atprop(x5), Formula_Atprop(y5)) => equal_Atpropa(x5, y5)
  case (Formula_Agent_Formula(x41, x42, x43),
         Formula_Agent_Formula(y41, y42, y43))
    => equal_Formula_Agent_Formula_Op(x41, y41) &&
         (equal_Agenta(x42, y42) && equal_Formulaa(x43, y43))
  case (Formula_Agent(x3), Formula_Agent(y3)) => equal_Agenta(x3, y3)
  case (Formula_Action_Formula(x21, x22, x23),
         Formula_Action_Formula(y21, y22, y23))
    => equal_Formula_Action_Formula_Op(x21, y21) &&
         (equal_Actiona(x22, y22) && equal_Formulaa(x23, y23))
  case (Formula_Action(x1), Formula_Action(y1)) => equal_Actiona(x1, y1)
}

implicit def equal_Structure: equal[Structure] = new equal[Structure] {
  val `DEAK.equal` = (a: Structure, b: Structure) => equal_Structurea(a, b)
}

def equal_Structurea(x0: Structure, x1: Structure): Boolean = (x0, x1) match {
  case (Structure_Phi(x7), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Phi(x7)) => false
  case (Structure_Freevar(x6), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Freevar(x6)) => false
  case (Structure_Freevar(x6), Structure_Phi(x7)) => false
  case (Structure_Phi(x7), Structure_Freevar(x6)) => false
  case (Structure_Formula(x5), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Formula(x5)) => false
  case (Structure_Formula(x5), Structure_Phi(x7)) => false
  case (Structure_Phi(x7), Structure_Formula(x5)) => false
  case (Structure_Formula(x5), Structure_Freevar(x6)) => false
  case (Structure_Freevar(x6), Structure_Formula(x5)) => false
  case (Structure_Bin(x41, x42, x43), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Bin(x41, x42, x43)) => false
  case (Structure_Bin(x41, x42, x43), Structure_Phi(x7)) => false
  case (Structure_Phi(x7), Structure_Bin(x41, x42, x43)) => false
  case (Structure_Bin(x41, x42, x43), Structure_Freevar(x6)) => false
  case (Structure_Freevar(x6), Structure_Bin(x41, x42, x43)) => false
  case (Structure_Bin(x41, x42, x43), Structure_Formula(x5)) => false
  case (Structure_Formula(x5), Structure_Bin(x41, x42, x43)) => false
  case (Structure_Bigcomma(x3), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Bigcomma(x3)) => false
  case (Structure_Bigcomma(x3), Structure_Phi(x7)) => false
  case (Structure_Phi(x7), Structure_Bigcomma(x3)) => false
  case (Structure_Bigcomma(x3), Structure_Freevar(x6)) => false
  case (Structure_Freevar(x6), Structure_Bigcomma(x3)) => false
  case (Structure_Bigcomma(x3), Structure_Formula(x5)) => false
  case (Structure_Formula(x5), Structure_Bigcomma(x3)) => false
  case (Structure_Bigcomma(x3), Structure_Bin(x41, x42, x43)) => false
  case (Structure_Bin(x41, x42, x43), Structure_Bigcomma(x3)) => false
  case (Structure_Agent_Structure(x21, x22, x23), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Agent_Structure(x21, x22, x23)) => false
  case (Structure_Agent_Structure(x21, x22, x23), Structure_Phi(x7)) => false
  case (Structure_Phi(x7), Structure_Agent_Structure(x21, x22, x23)) => false
  case (Structure_Agent_Structure(x21, x22, x23), Structure_Freevar(x6)) =>
    false
  case (Structure_Freevar(x6), Structure_Agent_Structure(x21, x22, x23)) =>
    false
  case (Structure_Agent_Structure(x21, x22, x23), Structure_Formula(x5)) =>
    false
  case (Structure_Formula(x5), Structure_Agent_Structure(x21, x22, x23)) =>
    false
  case (Structure_Agent_Structure(x21, x22, x23), Structure_Bin(x41, x42, x43))
    => false
  case (Structure_Bin(x41, x42, x43), Structure_Agent_Structure(x21, x22, x23))
    => false
  case (Structure_Agent_Structure(x21, x22, x23), Structure_Bigcomma(x3)) =>
    false
  case (Structure_Bigcomma(x3), Structure_Agent_Structure(x21, x22, x23)) =>
    false
  case (Structure_Action_Structure(x11, x12, x13), Structure_Zer(x8)) => false
  case (Structure_Zer(x8), Structure_Action_Structure(x11, x12, x13)) => false
  case (Structure_Action_Structure(x11, x12, x13), Structure_Phi(x7)) => false
  case (Structure_Phi(x7), Structure_Action_Structure(x11, x12, x13)) => false
  case (Structure_Action_Structure(x11, x12, x13), Structure_Freevar(x6)) =>
    false
  case (Structure_Freevar(x6), Structure_Action_Structure(x11, x12, x13)) =>
    false
  case (Structure_Action_Structure(x11, x12, x13), Structure_Formula(x5)) =>
    false
  case (Structure_Formula(x5), Structure_Action_Structure(x11, x12, x13)) =>
    false
  case (Structure_Action_Structure(x11, x12, x13), Structure_Bin(x41, x42, x43))
    => false
  case (Structure_Bin(x41, x42, x43), Structure_Action_Structure(x11, x12, x13))
    => false
  case (Structure_Action_Structure(x11, x12, x13), Structure_Bigcomma(x3)) =>
    false
  case (Structure_Bigcomma(x3), Structure_Action_Structure(x11, x12, x13)) =>
    false
  case (Structure_Action_Structure(x11, x12, x13),
         Structure_Agent_Structure(x21, x22, x23))
    => false
  case (Structure_Agent_Structure(x21, x22, x23),
         Structure_Action_Structure(x11, x12, x13))
    => false
  case (Structure_Zer(x8), Structure_Zer(y8)) => equal_Structure_Zer_Op(x8, y8)
  case (Structure_Phi(x7), Structure_Phi(y7)) => equal_Actiona(x7, y7)
  case (Structure_Freevar(x6), Structure_Freevar(y6)) =>
    equal_lista[Char](x6, y6)
  case (Structure_Formula(x5), Structure_Formula(y5)) => equal_Formulaa(x5, y5)
  case (Structure_Bin(x41, x42, x43), Structure_Bin(y41, y42, y43)) =>
    equal_Structurea(x41, y41) &&
      (equal_Structure_Bin_Op(x42, y42) && equal_Structurea(x43, y43))
  case (Structure_Bigcomma(x3), Structure_Bigcomma(y3)) =>
    equal_lista[Structure](x3, y3)
  case (Structure_Agent_Structure(x21, x22, x23),
         Structure_Agent_Structure(y21, y22, y23))
    => equal_Structure_Agent_Structure_Op(x21, y21) &&
         (equal_Agenta(x22, y22) && equal_Structurea(x23, y23))
  case (Structure_Action_Structure(x11, x12, x13),
         Structure_Action_Structure(y11, y12, y13))
    => equal_Structure_Action_Structure_Op(x11, y11) &&
         (equal_Actiona(x12, y12) && equal_Structurea(x13, y13))
}

abstract sealed class Sequent
final case class Sequenta(a: Structure, b: Structure) extends Sequent
final case class Sequent_Structure(a: Structure) extends Sequent

def equal_Sequenta(x0: Sequent, x1: Sequent): Boolean = (x0, x1) match {
  case (Sequenta(x11, x12), Sequent_Structure(x2)) => false
  case (Sequent_Structure(x2), Sequenta(x11, x12)) => false
  case (Sequent_Structure(x2), Sequent_Structure(y2)) =>
    equal_Structurea(x2, y2)
  case (Sequenta(x11, x12), Sequenta(y11, y12)) =>
    equal_Structurea(x11, y11) && equal_Structurea(x12, y12)
}

abstract sealed class RuleStructAct
final case class A_FS_L() extends RuleStructAct
final case class A_FS_R() extends RuleStructAct
final case class A_mon_L() extends RuleStructAct
final case class A_mon_R() extends RuleStructAct
final case class A_nec_L() extends RuleStructAct
final case class A_nec_R() extends RuleStructAct
final case class FS_A_L() extends RuleStructAct
final case class FS_A_R() extends RuleStructAct
final case class Mon_A_L() extends RuleStructAct
final case class Mon_A_R() extends RuleStructAct
final case class Nec_A_L() extends RuleStructAct
final case class Nec_A_R() extends RuleStructAct

def equal_RuleStructAct(x0: RuleStructAct, x1: RuleStructAct): Boolean =
  (x0, x1) match {
  case (Nec_A_L(), Nec_A_R()) => false
  case (Nec_A_R(), Nec_A_L()) => false
  case (Mon_A_R(), Nec_A_R()) => false
  case (Nec_A_R(), Mon_A_R()) => false
  case (Mon_A_R(), Nec_A_L()) => false
  case (Nec_A_L(), Mon_A_R()) => false
  case (Mon_A_L(), Nec_A_R()) => false
  case (Nec_A_R(), Mon_A_L()) => false
  case (Mon_A_L(), Nec_A_L()) => false
  case (Nec_A_L(), Mon_A_L()) => false
  case (Mon_A_L(), Mon_A_R()) => false
  case (Mon_A_R(), Mon_A_L()) => false
  case (FS_A_R(), Nec_A_R()) => false
  case (Nec_A_R(), FS_A_R()) => false
  case (FS_A_R(), Nec_A_L()) => false
  case (Nec_A_L(), FS_A_R()) => false
  case (FS_A_R(), Mon_A_R()) => false
  case (Mon_A_R(), FS_A_R()) => false
  case (FS_A_R(), Mon_A_L()) => false
  case (Mon_A_L(), FS_A_R()) => false
  case (FS_A_L(), Nec_A_R()) => false
  case (Nec_A_R(), FS_A_L()) => false
  case (FS_A_L(), Nec_A_L()) => false
  case (Nec_A_L(), FS_A_L()) => false
  case (FS_A_L(), Mon_A_R()) => false
  case (Mon_A_R(), FS_A_L()) => false
  case (FS_A_L(), Mon_A_L()) => false
  case (Mon_A_L(), FS_A_L()) => false
  case (FS_A_L(), FS_A_R()) => false
  case (FS_A_R(), FS_A_L()) => false
  case (A_nec_R(), Nec_A_R()) => false
  case (Nec_A_R(), A_nec_R()) => false
  case (A_nec_R(), Nec_A_L()) => false
  case (Nec_A_L(), A_nec_R()) => false
  case (A_nec_R(), Mon_A_R()) => false
  case (Mon_A_R(), A_nec_R()) => false
  case (A_nec_R(), Mon_A_L()) => false
  case (Mon_A_L(), A_nec_R()) => false
  case (A_nec_R(), FS_A_R()) => false
  case (FS_A_R(), A_nec_R()) => false
  case (A_nec_R(), FS_A_L()) => false
  case (FS_A_L(), A_nec_R()) => false
  case (A_nec_L(), Nec_A_R()) => false
  case (Nec_A_R(), A_nec_L()) => false
  case (A_nec_L(), Nec_A_L()) => false
  case (Nec_A_L(), A_nec_L()) => false
  case (A_nec_L(), Mon_A_R()) => false
  case (Mon_A_R(), A_nec_L()) => false
  case (A_nec_L(), Mon_A_L()) => false
  case (Mon_A_L(), A_nec_L()) => false
  case (A_nec_L(), FS_A_R()) => false
  case (FS_A_R(), A_nec_L()) => false
  case (A_nec_L(), FS_A_L()) => false
  case (FS_A_L(), A_nec_L()) => false
  case (A_nec_L(), A_nec_R()) => false
  case (A_nec_R(), A_nec_L()) => false
  case (A_mon_R(), Nec_A_R()) => false
  case (Nec_A_R(), A_mon_R()) => false
  case (A_mon_R(), Nec_A_L()) => false
  case (Nec_A_L(), A_mon_R()) => false
  case (A_mon_R(), Mon_A_R()) => false
  case (Mon_A_R(), A_mon_R()) => false
  case (A_mon_R(), Mon_A_L()) => false
  case (Mon_A_L(), A_mon_R()) => false
  case (A_mon_R(), FS_A_R()) => false
  case (FS_A_R(), A_mon_R()) => false
  case (A_mon_R(), FS_A_L()) => false
  case (FS_A_L(), A_mon_R()) => false
  case (A_mon_R(), A_nec_R()) => false
  case (A_nec_R(), A_mon_R()) => false
  case (A_mon_R(), A_nec_L()) => false
  case (A_nec_L(), A_mon_R()) => false
  case (A_mon_L(), Nec_A_R()) => false
  case (Nec_A_R(), A_mon_L()) => false
  case (A_mon_L(), Nec_A_L()) => false
  case (Nec_A_L(), A_mon_L()) => false
  case (A_mon_L(), Mon_A_R()) => false
  case (Mon_A_R(), A_mon_L()) => false
  case (A_mon_L(), Mon_A_L()) => false
  case (Mon_A_L(), A_mon_L()) => false
  case (A_mon_L(), FS_A_R()) => false
  case (FS_A_R(), A_mon_L()) => false
  case (A_mon_L(), FS_A_L()) => false
  case (FS_A_L(), A_mon_L()) => false
  case (A_mon_L(), A_nec_R()) => false
  case (A_nec_R(), A_mon_L()) => false
  case (A_mon_L(), A_nec_L()) => false
  case (A_nec_L(), A_mon_L()) => false
  case (A_mon_L(), A_mon_R()) => false
  case (A_mon_R(), A_mon_L()) => false
  case (A_FS_R(), Nec_A_R()) => false
  case (Nec_A_R(), A_FS_R()) => false
  case (A_FS_R(), Nec_A_L()) => false
  case (Nec_A_L(), A_FS_R()) => false
  case (A_FS_R(), Mon_A_R()) => false
  case (Mon_A_R(), A_FS_R()) => false
  case (A_FS_R(), Mon_A_L()) => false
  case (Mon_A_L(), A_FS_R()) => false
  case (A_FS_R(), FS_A_R()) => false
  case (FS_A_R(), A_FS_R()) => false
  case (A_FS_R(), FS_A_L()) => false
  case (FS_A_L(), A_FS_R()) => false
  case (A_FS_R(), A_nec_R()) => false
  case (A_nec_R(), A_FS_R()) => false
  case (A_FS_R(), A_nec_L()) => false
  case (A_nec_L(), A_FS_R()) => false
  case (A_FS_R(), A_mon_R()) => false
  case (A_mon_R(), A_FS_R()) => false
  case (A_FS_R(), A_mon_L()) => false
  case (A_mon_L(), A_FS_R()) => false
  case (A_FS_L(), Nec_A_R()) => false
  case (Nec_A_R(), A_FS_L()) => false
  case (A_FS_L(), Nec_A_L()) => false
  case (Nec_A_L(), A_FS_L()) => false
  case (A_FS_L(), Mon_A_R()) => false
  case (Mon_A_R(), A_FS_L()) => false
  case (A_FS_L(), Mon_A_L()) => false
  case (Mon_A_L(), A_FS_L()) => false
  case (A_FS_L(), FS_A_R()) => false
  case (FS_A_R(), A_FS_L()) => false
  case (A_FS_L(), FS_A_L()) => false
  case (FS_A_L(), A_FS_L()) => false
  case (A_FS_L(), A_nec_R()) => false
  case (A_nec_R(), A_FS_L()) => false
  case (A_FS_L(), A_nec_L()) => false
  case (A_nec_L(), A_FS_L()) => false
  case (A_FS_L(), A_mon_R()) => false
  case (A_mon_R(), A_FS_L()) => false
  case (A_FS_L(), A_mon_L()) => false
  case (A_mon_L(), A_FS_L()) => false
  case (A_FS_L(), A_FS_R()) => false
  case (A_FS_R(), A_FS_L()) => false
  case (Nec_A_R(), Nec_A_R()) => true
  case (Nec_A_L(), Nec_A_L()) => true
  case (Mon_A_R(), Mon_A_R()) => true
  case (Mon_A_L(), Mon_A_L()) => true
  case (FS_A_R(), FS_A_R()) => true
  case (FS_A_L(), FS_A_L()) => true
  case (A_nec_R(), A_nec_R()) => true
  case (A_nec_L(), A_nec_L()) => true
  case (A_mon_R(), A_mon_R()) => true
  case (A_mon_L(), A_mon_L()) => true
  case (A_FS_R(), A_FS_R()) => true
  case (A_FS_L(), A_FS_L()) => true
}

abstract sealed class RuleKnowledge
final case class Refl_ForwK() extends RuleKnowledge

def equal_RuleKnowledge(x0: RuleKnowledge, x1: RuleKnowledge): Boolean =
  (x0, x1) match {
  case (Refl_ForwK(), Refl_ForwK()) => true
}

abstract sealed class RuleStructEA
final case class Balance() extends RuleStructEA
final case class CompA_L() extends RuleStructEA
final case class CompA_R() extends RuleStructEA
final case class Reduce_L() extends RuleStructEA
final case class Reduce_R() extends RuleStructEA

def equal_RuleStructEA(x0: RuleStructEA, x1: RuleStructEA): Boolean = (x0, x1)
  match {
  case (Reduce_L(), Reduce_R()) => false
  case (Reduce_R(), Reduce_L()) => false
  case (CompA_R(), Reduce_R()) => false
  case (Reduce_R(), CompA_R()) => false
  case (CompA_R(), Reduce_L()) => false
  case (Reduce_L(), CompA_R()) => false
  case (CompA_L(), Reduce_R()) => false
  case (Reduce_R(), CompA_L()) => false
  case (CompA_L(), Reduce_L()) => false
  case (Reduce_L(), CompA_L()) => false
  case (CompA_L(), CompA_R()) => false
  case (CompA_R(), CompA_L()) => false
  case (Balance(), Reduce_R()) => false
  case (Reduce_R(), Balance()) => false
  case (Balance(), Reduce_L()) => false
  case (Reduce_L(), Balance()) => false
  case (Balance(), CompA_R()) => false
  case (CompA_R(), Balance()) => false
  case (Balance(), CompA_L()) => false
  case (CompA_L(), Balance()) => false
  case (Reduce_R(), Reduce_R()) => true
  case (Reduce_L(), Reduce_L()) => true
  case (CompA_R(), CompA_R()) => true
  case (CompA_L(), CompA_L()) => true
  case (Balance(), Balance()) => true
}

abstract sealed class RuleBigcomma
final case class Bigcomma_Cons_L() extends RuleBigcomma
final case class Bigcomma_Cons_L2() extends RuleBigcomma
final case class Bigcomma_Cons_R() extends RuleBigcomma
final case class Bigcomma_Cons_R2() extends RuleBigcomma
final case class Bigcomma_Nil_L() extends RuleBigcomma
final case class Bigcomma_Nil_L2() extends RuleBigcomma
final case class Bigcomma_Nil_R() extends RuleBigcomma
final case class Bigcomma_Nil_R2() extends RuleBigcomma

def equal_RuleBigcomma(x0: RuleBigcomma, x1: RuleBigcomma): Boolean = (x0, x1)
  match {
  case (Bigcomma_Nil_R(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_R(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_R(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_R(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_R(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_R(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Nil_R2()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Nil_R()) => false
  case (Bigcomma_Nil_R(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Nil_L2()) => false
  case (Bigcomma_Nil_L2(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Nil_L()) => false
  case (Bigcomma_Nil_L(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Cons_R2()) => false
  case (Bigcomma_Cons_R2(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Cons_R()) => false
  case (Bigcomma_Cons_R(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Cons_L(), Bigcomma_Cons_L2()) => false
  case (Bigcomma_Cons_L2(), Bigcomma_Cons_L()) => false
  case (Bigcomma_Nil_R2(), Bigcomma_Nil_R2()) => true
  case (Bigcomma_Nil_R(), Bigcomma_Nil_R()) => true
  case (Bigcomma_Nil_L2(), Bigcomma_Nil_L2()) => true
  case (Bigcomma_Nil_L(), Bigcomma_Nil_L()) => true
  case (Bigcomma_Cons_R2(), Bigcomma_Cons_R2()) => true
  case (Bigcomma_Cons_R(), Bigcomma_Cons_R()) => true
  case (Bigcomma_Cons_L2(), Bigcomma_Cons_L2()) => true
  case (Bigcomma_Cons_L(), Bigcomma_Cons_L()) => true
}

abstract sealed class RuleSwapout
final case class Swapout_L() extends RuleSwapout
final case class Swapout_R() extends RuleSwapout

def equal_RuleSwapout(x0: RuleSwapout, x1: RuleSwapout): Boolean = (x0, x1)
  match {
  case (Swapout_L(), Swapout_R()) => false
  case (Swapout_R(), Swapout_L()) => false
  case (Swapout_R(), Swapout_R()) => true
  case (Swapout_L(), Swapout_L()) => true
}

abstract sealed class RuleStructK
final case class FS_K_L() extends RuleStructK
final case class FS_K_R() extends RuleStructK
final case class K_FS_L() extends RuleStructK
final case class K_FS_R() extends RuleStructK
final case class K_mon_L() extends RuleStructK
final case class K_mon_R() extends RuleStructK
final case class K_nec_L() extends RuleStructK
final case class K_nec_R() extends RuleStructK
final case class Mon_K_L() extends RuleStructK
final case class Mon_K_R() extends RuleStructK
final case class Nec_K_L() extends RuleStructK
final case class Nec_K_R() extends RuleStructK

def equal_RuleStructK(x0: RuleStructK, x1: RuleStructK): Boolean = (x0, x1)
  match {
  case (Nec_K_L(), Nec_K_R()) => false
  case (Nec_K_R(), Nec_K_L()) => false
  case (Mon_K_R(), Nec_K_R()) => false
  case (Nec_K_R(), Mon_K_R()) => false
  case (Mon_K_R(), Nec_K_L()) => false
  case (Nec_K_L(), Mon_K_R()) => false
  case (Mon_K_L(), Nec_K_R()) => false
  case (Nec_K_R(), Mon_K_L()) => false
  case (Mon_K_L(), Nec_K_L()) => false
  case (Nec_K_L(), Mon_K_L()) => false
  case (Mon_K_L(), Mon_K_R()) => false
  case (Mon_K_R(), Mon_K_L()) => false
  case (K_nec_R(), Nec_K_R()) => false
  case (Nec_K_R(), K_nec_R()) => false
  case (K_nec_R(), Nec_K_L()) => false
  case (Nec_K_L(), K_nec_R()) => false
  case (K_nec_R(), Mon_K_R()) => false
  case (Mon_K_R(), K_nec_R()) => false
  case (K_nec_R(), Mon_K_L()) => false
  case (Mon_K_L(), K_nec_R()) => false
  case (K_nec_L(), Nec_K_R()) => false
  case (Nec_K_R(), K_nec_L()) => false
  case (K_nec_L(), Nec_K_L()) => false
  case (Nec_K_L(), K_nec_L()) => false
  case (K_nec_L(), Mon_K_R()) => false
  case (Mon_K_R(), K_nec_L()) => false
  case (K_nec_L(), Mon_K_L()) => false
  case (Mon_K_L(), K_nec_L()) => false
  case (K_nec_L(), K_nec_R()) => false
  case (K_nec_R(), K_nec_L()) => false
  case (K_mon_R(), Nec_K_R()) => false
  case (Nec_K_R(), K_mon_R()) => false
  case (K_mon_R(), Nec_K_L()) => false
  case (Nec_K_L(), K_mon_R()) => false
  case (K_mon_R(), Mon_K_R()) => false
  case (Mon_K_R(), K_mon_R()) => false
  case (K_mon_R(), Mon_K_L()) => false
  case (Mon_K_L(), K_mon_R()) => false
  case (K_mon_R(), K_nec_R()) => false
  case (K_nec_R(), K_mon_R()) => false
  case (K_mon_R(), K_nec_L()) => false
  case (K_nec_L(), K_mon_R()) => false
  case (K_mon_L(), Nec_K_R()) => false
  case (Nec_K_R(), K_mon_L()) => false
  case (K_mon_L(), Nec_K_L()) => false
  case (Nec_K_L(), K_mon_L()) => false
  case (K_mon_L(), Mon_K_R()) => false
  case (Mon_K_R(), K_mon_L()) => false
  case (K_mon_L(), Mon_K_L()) => false
  case (Mon_K_L(), K_mon_L()) => false
  case (K_mon_L(), K_nec_R()) => false
  case (K_nec_R(), K_mon_L()) => false
  case (K_mon_L(), K_nec_L()) => false
  case (K_nec_L(), K_mon_L()) => false
  case (K_mon_L(), K_mon_R()) => false
  case (K_mon_R(), K_mon_L()) => false
  case (K_FS_R(), Nec_K_R()) => false
  case (Nec_K_R(), K_FS_R()) => false
  case (K_FS_R(), Nec_K_L()) => false
  case (Nec_K_L(), K_FS_R()) => false
  case (K_FS_R(), Mon_K_R()) => false
  case (Mon_K_R(), K_FS_R()) => false
  case (K_FS_R(), Mon_K_L()) => false
  case (Mon_K_L(), K_FS_R()) => false
  case (K_FS_R(), K_nec_R()) => false
  case (K_nec_R(), K_FS_R()) => false
  case (K_FS_R(), K_nec_L()) => false
  case (K_nec_L(), K_FS_R()) => false
  case (K_FS_R(), K_mon_R()) => false
  case (K_mon_R(), K_FS_R()) => false
  case (K_FS_R(), K_mon_L()) => false
  case (K_mon_L(), K_FS_R()) => false
  case (K_FS_L(), Nec_K_R()) => false
  case (Nec_K_R(), K_FS_L()) => false
  case (K_FS_L(), Nec_K_L()) => false
  case (Nec_K_L(), K_FS_L()) => false
  case (K_FS_L(), Mon_K_R()) => false
  case (Mon_K_R(), K_FS_L()) => false
  case (K_FS_L(), Mon_K_L()) => false
  case (Mon_K_L(), K_FS_L()) => false
  case (K_FS_L(), K_nec_R()) => false
  case (K_nec_R(), K_FS_L()) => false
  case (K_FS_L(), K_nec_L()) => false
  case (K_nec_L(), K_FS_L()) => false
  case (K_FS_L(), K_mon_R()) => false
  case (K_mon_R(), K_FS_L()) => false
  case (K_FS_L(), K_mon_L()) => false
  case (K_mon_L(), K_FS_L()) => false
  case (K_FS_L(), K_FS_R()) => false
  case (K_FS_R(), K_FS_L()) => false
  case (FS_K_R(), Nec_K_R()) => false
  case (Nec_K_R(), FS_K_R()) => false
  case (FS_K_R(), Nec_K_L()) => false
  case (Nec_K_L(), FS_K_R()) => false
  case (FS_K_R(), Mon_K_R()) => false
  case (Mon_K_R(), FS_K_R()) => false
  case (FS_K_R(), Mon_K_L()) => false
  case (Mon_K_L(), FS_K_R()) => false
  case (FS_K_R(), K_nec_R()) => false
  case (K_nec_R(), FS_K_R()) => false
  case (FS_K_R(), K_nec_L()) => false
  case (K_nec_L(), FS_K_R()) => false
  case (FS_K_R(), K_mon_R()) => false
  case (K_mon_R(), FS_K_R()) => false
  case (FS_K_R(), K_mon_L()) => false
  case (K_mon_L(), FS_K_R()) => false
  case (FS_K_R(), K_FS_R()) => false
  case (K_FS_R(), FS_K_R()) => false
  case (FS_K_R(), K_FS_L()) => false
  case (K_FS_L(), FS_K_R()) => false
  case (FS_K_L(), Nec_K_R()) => false
  case (Nec_K_R(), FS_K_L()) => false
  case (FS_K_L(), Nec_K_L()) => false
  case (Nec_K_L(), FS_K_L()) => false
  case (FS_K_L(), Mon_K_R()) => false
  case (Mon_K_R(), FS_K_L()) => false
  case (FS_K_L(), Mon_K_L()) => false
  case (Mon_K_L(), FS_K_L()) => false
  case (FS_K_L(), K_nec_R()) => false
  case (K_nec_R(), FS_K_L()) => false
  case (FS_K_L(), K_nec_L()) => false
  case (K_nec_L(), FS_K_L()) => false
  case (FS_K_L(), K_mon_R()) => false
  case (K_mon_R(), FS_K_L()) => false
  case (FS_K_L(), K_mon_L()) => false
  case (K_mon_L(), FS_K_L()) => false
  case (FS_K_L(), K_FS_R()) => false
  case (K_FS_R(), FS_K_L()) => false
  case (FS_K_L(), K_FS_L()) => false
  case (K_FS_L(), FS_K_L()) => false
  case (FS_K_L(), FS_K_R()) => false
  case (FS_K_R(), FS_K_L()) => false
  case (Nec_K_R(), Nec_K_R()) => true
  case (Nec_K_L(), Nec_K_L()) => true
  case (Mon_K_R(), Mon_K_R()) => true
  case (Mon_K_L(), Mon_K_L()) => true
  case (K_nec_R(), K_nec_R()) => true
  case (K_nec_L(), K_nec_L()) => true
  case (K_mon_R(), K_mon_R()) => true
  case (K_mon_L(), K_mon_L()) => true
  case (K_FS_R(), K_FS_R()) => true
  case (K_FS_L(), K_FS_L()) => true
  case (FS_K_R(), FS_K_R()) => true
  case (FS_K_L(), FS_K_L()) => true
}

abstract sealed class RuleDispAct
final case class Back_forw_A() extends RuleDispAct
final case class Back_forw_A2() extends RuleDispAct
final case class Forw_back_A() extends RuleDispAct
final case class Forw_back_A2() extends RuleDispAct

def equal_RuleDispAct(x0: RuleDispAct, x1: RuleDispAct): Boolean = (x0, x1)
  match {
  case (Forw_back_A(), Forw_back_A2()) => false
  case (Forw_back_A2(), Forw_back_A()) => false
  case (Back_forw_A2(), Forw_back_A2()) => false
  case (Forw_back_A2(), Back_forw_A2()) => false
  case (Back_forw_A2(), Forw_back_A()) => false
  case (Forw_back_A(), Back_forw_A2()) => false
  case (Back_forw_A(), Forw_back_A2()) => false
  case (Forw_back_A2(), Back_forw_A()) => false
  case (Back_forw_A(), Forw_back_A()) => false
  case (Forw_back_A(), Back_forw_A()) => false
  case (Back_forw_A(), Back_forw_A2()) => false
  case (Back_forw_A2(), Back_forw_A()) => false
  case (Forw_back_A2(), Forw_back_A2()) => true
  case (Forw_back_A(), Forw_back_A()) => true
  case (Back_forw_A2(), Back_forw_A2()) => true
  case (Back_forw_A(), Back_forw_A()) => true
}

abstract sealed class RuleSwapin
final case class Swapin_L() extends RuleSwapin
final case class Swapin_R() extends RuleSwapin

def equal_RuleSwapin(x0: RuleSwapin, x1: RuleSwapin): Boolean = (x0, x1) match {
  case (Swapin_L(), Swapin_R()) => false
  case (Swapin_R(), Swapin_L()) => false
  case (Swapin_R(), Swapin_R()) => true
  case (Swapin_L(), Swapin_L()) => true
}

abstract sealed class RuleStruct
final case class A_L() extends RuleStruct
final case class A_L2() extends RuleStruct
final case class A_R() extends RuleStruct
final case class A_R2() extends RuleStruct
final case class C_L() extends RuleStruct
final case class C_R() extends RuleStruct
final case class E_L() extends RuleStruct
final case class E_R() extends RuleStruct
final case class IW_L() extends RuleStruct
final case class IW_R() extends RuleStruct
final case class I_impL() extends RuleStruct
final case class I_impL2() extends RuleStruct
final case class I_impR() extends RuleStruct
final case class I_impR2() extends RuleStruct
final case class ImpL_I() extends RuleStruct
final case class ImpL_I2() extends RuleStruct
final case class ImpR_I() extends RuleStruct
final case class ImpR_I2() extends RuleStruct
final case class W_impL_L() extends RuleStruct
final case class W_impL_R() extends RuleStruct
final case class W_impR_L() extends RuleStruct
final case class W_impR_R() extends RuleStruct

def equal_RuleStruct(x0: RuleStruct, x1: RuleStruct): Boolean = (x0, x1) match {
  case (W_impR_L(), W_impR_R()) => false
  case (W_impR_R(), W_impR_L()) => false
  case (W_impL_R(), W_impR_R()) => false
  case (W_impR_R(), W_impL_R()) => false
  case (W_impL_R(), W_impR_L()) => false
  case (W_impR_L(), W_impL_R()) => false
  case (W_impL_L(), W_impR_R()) => false
  case (W_impR_R(), W_impL_L()) => false
  case (W_impL_L(), W_impR_L()) => false
  case (W_impR_L(), W_impL_L()) => false
  case (W_impL_L(), W_impL_R()) => false
  case (W_impL_R(), W_impL_L()) => false
  case (ImpR_I2(), W_impR_R()) => false
  case (W_impR_R(), ImpR_I2()) => false
  case (ImpR_I2(), W_impR_L()) => false
  case (W_impR_L(), ImpR_I2()) => false
  case (ImpR_I2(), W_impL_R()) => false
  case (W_impL_R(), ImpR_I2()) => false
  case (ImpR_I2(), W_impL_L()) => false
  case (W_impL_L(), ImpR_I2()) => false
  case (ImpR_I(), W_impR_R()) => false
  case (W_impR_R(), ImpR_I()) => false
  case (ImpR_I(), W_impR_L()) => false
  case (W_impR_L(), ImpR_I()) => false
  case (ImpR_I(), W_impL_R()) => false
  case (W_impL_R(), ImpR_I()) => false
  case (ImpR_I(), W_impL_L()) => false
  case (W_impL_L(), ImpR_I()) => false
  case (ImpR_I(), ImpR_I2()) => false
  case (ImpR_I2(), ImpR_I()) => false
  case (ImpL_I2(), W_impR_R()) => false
  case (W_impR_R(), ImpL_I2()) => false
  case (ImpL_I2(), W_impR_L()) => false
  case (W_impR_L(), ImpL_I2()) => false
  case (ImpL_I2(), W_impL_R()) => false
  case (W_impL_R(), ImpL_I2()) => false
  case (ImpL_I2(), W_impL_L()) => false
  case (W_impL_L(), ImpL_I2()) => false
  case (ImpL_I2(), ImpR_I2()) => false
  case (ImpR_I2(), ImpL_I2()) => false
  case (ImpL_I2(), ImpR_I()) => false
  case (ImpR_I(), ImpL_I2()) => false
  case (ImpL_I(), W_impR_R()) => false
  case (W_impR_R(), ImpL_I()) => false
  case (ImpL_I(), W_impR_L()) => false
  case (W_impR_L(), ImpL_I()) => false
  case (ImpL_I(), W_impL_R()) => false
  case (W_impL_R(), ImpL_I()) => false
  case (ImpL_I(), W_impL_L()) => false
  case (W_impL_L(), ImpL_I()) => false
  case (ImpL_I(), ImpR_I2()) => false
  case (ImpR_I2(), ImpL_I()) => false
  case (ImpL_I(), ImpR_I()) => false
  case (ImpR_I(), ImpL_I()) => false
  case (ImpL_I(), ImpL_I2()) => false
  case (ImpL_I2(), ImpL_I()) => false
  case (I_impR2(), W_impR_R()) => false
  case (W_impR_R(), I_impR2()) => false
  case (I_impR2(), W_impR_L()) => false
  case (W_impR_L(), I_impR2()) => false
  case (I_impR2(), W_impL_R()) => false
  case (W_impL_R(), I_impR2()) => false
  case (I_impR2(), W_impL_L()) => false
  case (W_impL_L(), I_impR2()) => false
  case (I_impR2(), ImpR_I2()) => false
  case (ImpR_I2(), I_impR2()) => false
  case (I_impR2(), ImpR_I()) => false
  case (ImpR_I(), I_impR2()) => false
  case (I_impR2(), ImpL_I2()) => false
  case (ImpL_I2(), I_impR2()) => false
  case (I_impR2(), ImpL_I()) => false
  case (ImpL_I(), I_impR2()) => false
  case (I_impR(), W_impR_R()) => false
  case (W_impR_R(), I_impR()) => false
  case (I_impR(), W_impR_L()) => false
  case (W_impR_L(), I_impR()) => false
  case (I_impR(), W_impL_R()) => false
  case (W_impL_R(), I_impR()) => false
  case (I_impR(), W_impL_L()) => false
  case (W_impL_L(), I_impR()) => false
  case (I_impR(), ImpR_I2()) => false
  case (ImpR_I2(), I_impR()) => false
  case (I_impR(), ImpR_I()) => false
  case (ImpR_I(), I_impR()) => false
  case (I_impR(), ImpL_I2()) => false
  case (ImpL_I2(), I_impR()) => false
  case (I_impR(), ImpL_I()) => false
  case (ImpL_I(), I_impR()) => false
  case (I_impR(), I_impR2()) => false
  case (I_impR2(), I_impR()) => false
  case (I_impL2(), W_impR_R()) => false
  case (W_impR_R(), I_impL2()) => false
  case (I_impL2(), W_impR_L()) => false
  case (W_impR_L(), I_impL2()) => false
  case (I_impL2(), W_impL_R()) => false
  case (W_impL_R(), I_impL2()) => false
  case (I_impL2(), W_impL_L()) => false
  case (W_impL_L(), I_impL2()) => false
  case (I_impL2(), ImpR_I2()) => false
  case (ImpR_I2(), I_impL2()) => false
  case (I_impL2(), ImpR_I()) => false
  case (ImpR_I(), I_impL2()) => false
  case (I_impL2(), ImpL_I2()) => false
  case (ImpL_I2(), I_impL2()) => false
  case (I_impL2(), ImpL_I()) => false
  case (ImpL_I(), I_impL2()) => false
  case (I_impL2(), I_impR2()) => false
  case (I_impR2(), I_impL2()) => false
  case (I_impL2(), I_impR()) => false
  case (I_impR(), I_impL2()) => false
  case (I_impL(), W_impR_R()) => false
  case (W_impR_R(), I_impL()) => false
  case (I_impL(), W_impR_L()) => false
  case (W_impR_L(), I_impL()) => false
  case (I_impL(), W_impL_R()) => false
  case (W_impL_R(), I_impL()) => false
  case (I_impL(), W_impL_L()) => false
  case (W_impL_L(), I_impL()) => false
  case (I_impL(), ImpR_I2()) => false
  case (ImpR_I2(), I_impL()) => false
  case (I_impL(), ImpR_I()) => false
  case (ImpR_I(), I_impL()) => false
  case (I_impL(), ImpL_I2()) => false
  case (ImpL_I2(), I_impL()) => false
  case (I_impL(), ImpL_I()) => false
  case (ImpL_I(), I_impL()) => false
  case (I_impL(), I_impR2()) => false
  case (I_impR2(), I_impL()) => false
  case (I_impL(), I_impR()) => false
  case (I_impR(), I_impL()) => false
  case (I_impL(), I_impL2()) => false
  case (I_impL2(), I_impL()) => false
  case (IW_R(), W_impR_R()) => false
  case (W_impR_R(), IW_R()) => false
  case (IW_R(), W_impR_L()) => false
  case (W_impR_L(), IW_R()) => false
  case (IW_R(), W_impL_R()) => false
  case (W_impL_R(), IW_R()) => false
  case (IW_R(), W_impL_L()) => false
  case (W_impL_L(), IW_R()) => false
  case (IW_R(), ImpR_I2()) => false
  case (ImpR_I2(), IW_R()) => false
  case (IW_R(), ImpR_I()) => false
  case (ImpR_I(), IW_R()) => false
  case (IW_R(), ImpL_I2()) => false
  case (ImpL_I2(), IW_R()) => false
  case (IW_R(), ImpL_I()) => false
  case (ImpL_I(), IW_R()) => false
  case (IW_R(), I_impR2()) => false
  case (I_impR2(), IW_R()) => false
  case (IW_R(), I_impR()) => false
  case (I_impR(), IW_R()) => false
  case (IW_R(), I_impL2()) => false
  case (I_impL2(), IW_R()) => false
  case (IW_R(), I_impL()) => false
  case (I_impL(), IW_R()) => false
  case (IW_L(), W_impR_R()) => false
  case (W_impR_R(), IW_L()) => false
  case (IW_L(), W_impR_L()) => false
  case (W_impR_L(), IW_L()) => false
  case (IW_L(), W_impL_R()) => false
  case (W_impL_R(), IW_L()) => false
  case (IW_L(), W_impL_L()) => false
  case (W_impL_L(), IW_L()) => false
  case (IW_L(), ImpR_I2()) => false
  case (ImpR_I2(), IW_L()) => false
  case (IW_L(), ImpR_I()) => false
  case (ImpR_I(), IW_L()) => false
  case (IW_L(), ImpL_I2()) => false
  case (ImpL_I2(), IW_L()) => false
  case (IW_L(), ImpL_I()) => false
  case (ImpL_I(), IW_L()) => false
  case (IW_L(), I_impR2()) => false
  case (I_impR2(), IW_L()) => false
  case (IW_L(), I_impR()) => false
  case (I_impR(), IW_L()) => false
  case (IW_L(), I_impL2()) => false
  case (I_impL2(), IW_L()) => false
  case (IW_L(), I_impL()) => false
  case (I_impL(), IW_L()) => false
  case (IW_L(), IW_R()) => false
  case (IW_R(), IW_L()) => false
  case (E_R(), W_impR_R()) => false
  case (W_impR_R(), E_R()) => false
  case (E_R(), W_impR_L()) => false
  case (W_impR_L(), E_R()) => false
  case (E_R(), W_impL_R()) => false
  case (W_impL_R(), E_R()) => false
  case (E_R(), W_impL_L()) => false
  case (W_impL_L(), E_R()) => false
  case (E_R(), ImpR_I2()) => false
  case (ImpR_I2(), E_R()) => false
  case (E_R(), ImpR_I()) => false
  case (ImpR_I(), E_R()) => false
  case (E_R(), ImpL_I2()) => false
  case (ImpL_I2(), E_R()) => false
  case (E_R(), ImpL_I()) => false
  case (ImpL_I(), E_R()) => false
  case (E_R(), I_impR2()) => false
  case (I_impR2(), E_R()) => false
  case (E_R(), I_impR()) => false
  case (I_impR(), E_R()) => false
  case (E_R(), I_impL2()) => false
  case (I_impL2(), E_R()) => false
  case (E_R(), I_impL()) => false
  case (I_impL(), E_R()) => false
  case (E_R(), IW_R()) => false
  case (IW_R(), E_R()) => false
  case (E_R(), IW_L()) => false
  case (IW_L(), E_R()) => false
  case (E_L(), W_impR_R()) => false
  case (W_impR_R(), E_L()) => false
  case (E_L(), W_impR_L()) => false
  case (W_impR_L(), E_L()) => false
  case (E_L(), W_impL_R()) => false
  case (W_impL_R(), E_L()) => false
  case (E_L(), W_impL_L()) => false
  case (W_impL_L(), E_L()) => false
  case (E_L(), ImpR_I2()) => false
  case (ImpR_I2(), E_L()) => false
  case (E_L(), ImpR_I()) => false
  case (ImpR_I(), E_L()) => false
  case (E_L(), ImpL_I2()) => false
  case (ImpL_I2(), E_L()) => false
  case (E_L(), ImpL_I()) => false
  case (ImpL_I(), E_L()) => false
  case (E_L(), I_impR2()) => false
  case (I_impR2(), E_L()) => false
  case (E_L(), I_impR()) => false
  case (I_impR(), E_L()) => false
  case (E_L(), I_impL2()) => false
  case (I_impL2(), E_L()) => false
  case (E_L(), I_impL()) => false
  case (I_impL(), E_L()) => false
  case (E_L(), IW_R()) => false
  case (IW_R(), E_L()) => false
  case (E_L(), IW_L()) => false
  case (IW_L(), E_L()) => false
  case (E_L(), E_R()) => false
  case (E_R(), E_L()) => false
  case (C_R(), W_impR_R()) => false
  case (W_impR_R(), C_R()) => false
  case (C_R(), W_impR_L()) => false
  case (W_impR_L(), C_R()) => false
  case (C_R(), W_impL_R()) => false
  case (W_impL_R(), C_R()) => false
  case (C_R(), W_impL_L()) => false
  case (W_impL_L(), C_R()) => false
  case (C_R(), ImpR_I2()) => false
  case (ImpR_I2(), C_R()) => false
  case (C_R(), ImpR_I()) => false
  case (ImpR_I(), C_R()) => false
  case (C_R(), ImpL_I2()) => false
  case (ImpL_I2(), C_R()) => false
  case (C_R(), ImpL_I()) => false
  case (ImpL_I(), C_R()) => false
  case (C_R(), I_impR2()) => false
  case (I_impR2(), C_R()) => false
  case (C_R(), I_impR()) => false
  case (I_impR(), C_R()) => false
  case (C_R(), I_impL2()) => false
  case (I_impL2(), C_R()) => false
  case (C_R(), I_impL()) => false
  case (I_impL(), C_R()) => false
  case (C_R(), IW_R()) => false
  case (IW_R(), C_R()) => false
  case (C_R(), IW_L()) => false
  case (IW_L(), C_R()) => false
  case (C_R(), E_R()) => false
  case (E_R(), C_R()) => false
  case (C_R(), E_L()) => false
  case (E_L(), C_R()) => false
  case (C_L(), W_impR_R()) => false
  case (W_impR_R(), C_L()) => false
  case (C_L(), W_impR_L()) => false
  case (W_impR_L(), C_L()) => false
  case (C_L(), W_impL_R()) => false
  case (W_impL_R(), C_L()) => false
  case (C_L(), W_impL_L()) => false
  case (W_impL_L(), C_L()) => false
  case (C_L(), ImpR_I2()) => false
  case (ImpR_I2(), C_L()) => false
  case (C_L(), ImpR_I()) => false
  case (ImpR_I(), C_L()) => false
  case (C_L(), ImpL_I2()) => false
  case (ImpL_I2(), C_L()) => false
  case (C_L(), ImpL_I()) => false
  case (ImpL_I(), C_L()) => false
  case (C_L(), I_impR2()) => false
  case (I_impR2(), C_L()) => false
  case (C_L(), I_impR()) => false
  case (I_impR(), C_L()) => false
  case (C_L(), I_impL2()) => false
  case (I_impL2(), C_L()) => false
  case (C_L(), I_impL()) => false
  case (I_impL(), C_L()) => false
  case (C_L(), IW_R()) => false
  case (IW_R(), C_L()) => false
  case (C_L(), IW_L()) => false
  case (IW_L(), C_L()) => false
  case (C_L(), E_R()) => false
  case (E_R(), C_L()) => false
  case (C_L(), E_L()) => false
  case (E_L(), C_L()) => false
  case (C_L(), C_R()) => false
  case (C_R(), C_L()) => false
  case (A_R2(), W_impR_R()) => false
  case (W_impR_R(), A_R2()) => false
  case (A_R2(), W_impR_L()) => false
  case (W_impR_L(), A_R2()) => false
  case (A_R2(), W_impL_R()) => false
  case (W_impL_R(), A_R2()) => false
  case (A_R2(), W_impL_L()) => false
  case (W_impL_L(), A_R2()) => false
  case (A_R2(), ImpR_I2()) => false
  case (ImpR_I2(), A_R2()) => false
  case (A_R2(), ImpR_I()) => false
  case (ImpR_I(), A_R2()) => false
  case (A_R2(), ImpL_I2()) => false
  case (ImpL_I2(), A_R2()) => false
  case (A_R2(), ImpL_I()) => false
  case (ImpL_I(), A_R2()) => false
  case (A_R2(), I_impR2()) => false
  case (I_impR2(), A_R2()) => false
  case (A_R2(), I_impR()) => false
  case (I_impR(), A_R2()) => false
  case (A_R2(), I_impL2()) => false
  case (I_impL2(), A_R2()) => false
  case (A_R2(), I_impL()) => false
  case (I_impL(), A_R2()) => false
  case (A_R2(), IW_R()) => false
  case (IW_R(), A_R2()) => false
  case (A_R2(), IW_L()) => false
  case (IW_L(), A_R2()) => false
  case (A_R2(), E_R()) => false
  case (E_R(), A_R2()) => false
  case (A_R2(), E_L()) => false
  case (E_L(), A_R2()) => false
  case (A_R2(), C_R()) => false
  case (C_R(), A_R2()) => false
  case (A_R2(), C_L()) => false
  case (C_L(), A_R2()) => false
  case (A_R(), W_impR_R()) => false
  case (W_impR_R(), A_R()) => false
  case (A_R(), W_impR_L()) => false
  case (W_impR_L(), A_R()) => false
  case (A_R(), W_impL_R()) => false
  case (W_impL_R(), A_R()) => false
  case (A_R(), W_impL_L()) => false
  case (W_impL_L(), A_R()) => false
  case (A_R(), ImpR_I2()) => false
  case (ImpR_I2(), A_R()) => false
  case (A_R(), ImpR_I()) => false
  case (ImpR_I(), A_R()) => false
  case (A_R(), ImpL_I2()) => false
  case (ImpL_I2(), A_R()) => false
  case (A_R(), ImpL_I()) => false
  case (ImpL_I(), A_R()) => false
  case (A_R(), I_impR2()) => false
  case (I_impR2(), A_R()) => false
  case (A_R(), I_impR()) => false
  case (I_impR(), A_R()) => false
  case (A_R(), I_impL2()) => false
  case (I_impL2(), A_R()) => false
  case (A_R(), I_impL()) => false
  case (I_impL(), A_R()) => false
  case (A_R(), IW_R()) => false
  case (IW_R(), A_R()) => false
  case (A_R(), IW_L()) => false
  case (IW_L(), A_R()) => false
  case (A_R(), E_R()) => false
  case (E_R(), A_R()) => false
  case (A_R(), E_L()) => false
  case (E_L(), A_R()) => false
  case (A_R(), C_R()) => false
  case (C_R(), A_R()) => false
  case (A_R(), C_L()) => false
  case (C_L(), A_R()) => false
  case (A_R(), A_R2()) => false
  case (A_R2(), A_R()) => false
  case (A_L2(), W_impR_R()) => false
  case (W_impR_R(), A_L2()) => false
  case (A_L2(), W_impR_L()) => false
  case (W_impR_L(), A_L2()) => false
  case (A_L2(), W_impL_R()) => false
  case (W_impL_R(), A_L2()) => false
  case (A_L2(), W_impL_L()) => false
  case (W_impL_L(), A_L2()) => false
  case (A_L2(), ImpR_I2()) => false
  case (ImpR_I2(), A_L2()) => false
  case (A_L2(), ImpR_I()) => false
  case (ImpR_I(), A_L2()) => false
  case (A_L2(), ImpL_I2()) => false
  case (ImpL_I2(), A_L2()) => false
  case (A_L2(), ImpL_I()) => false
  case (ImpL_I(), A_L2()) => false
  case (A_L2(), I_impR2()) => false
  case (I_impR2(), A_L2()) => false
  case (A_L2(), I_impR()) => false
  case (I_impR(), A_L2()) => false
  case (A_L2(), I_impL2()) => false
  case (I_impL2(), A_L2()) => false
  case (A_L2(), I_impL()) => false
  case (I_impL(), A_L2()) => false
  case (A_L2(), IW_R()) => false
  case (IW_R(), A_L2()) => false
  case (A_L2(), IW_L()) => false
  case (IW_L(), A_L2()) => false
  case (A_L2(), E_R()) => false
  case (E_R(), A_L2()) => false
  case (A_L2(), E_L()) => false
  case (E_L(), A_L2()) => false
  case (A_L2(), C_R()) => false
  case (C_R(), A_L2()) => false
  case (A_L2(), C_L()) => false
  case (C_L(), A_L2()) => false
  case (A_L2(), A_R2()) => false
  case (A_R2(), A_L2()) => false
  case (A_L2(), A_R()) => false
  case (A_R(), A_L2()) => false
  case (A_L(), W_impR_R()) => false
  case (W_impR_R(), A_L()) => false
  case (A_L(), W_impR_L()) => false
  case (W_impR_L(), A_L()) => false
  case (A_L(), W_impL_R()) => false
  case (W_impL_R(), A_L()) => false
  case (A_L(), W_impL_L()) => false
  case (W_impL_L(), A_L()) => false
  case (A_L(), ImpR_I2()) => false
  case (ImpR_I2(), A_L()) => false
  case (A_L(), ImpR_I()) => false
  case (ImpR_I(), A_L()) => false
  case (A_L(), ImpL_I2()) => false
  case (ImpL_I2(), A_L()) => false
  case (A_L(), ImpL_I()) => false
  case (ImpL_I(), A_L()) => false
  case (A_L(), I_impR2()) => false
  case (I_impR2(), A_L()) => false
  case (A_L(), I_impR()) => false
  case (I_impR(), A_L()) => false
  case (A_L(), I_impL2()) => false
  case (I_impL2(), A_L()) => false
  case (A_L(), I_impL()) => false
  case (I_impL(), A_L()) => false
  case (A_L(), IW_R()) => false
  case (IW_R(), A_L()) => false
  case (A_L(), IW_L()) => false
  case (IW_L(), A_L()) => false
  case (A_L(), E_R()) => false
  case (E_R(), A_L()) => false
  case (A_L(), E_L()) => false
  case (E_L(), A_L()) => false
  case (A_L(), C_R()) => false
  case (C_R(), A_L()) => false
  case (A_L(), C_L()) => false
  case (C_L(), A_L()) => false
  case (A_L(), A_R2()) => false
  case (A_R2(), A_L()) => false
  case (A_L(), A_R()) => false
  case (A_R(), A_L()) => false
  case (A_L(), A_L2()) => false
  case (A_L2(), A_L()) => false
  case (W_impR_R(), W_impR_R()) => true
  case (W_impR_L(), W_impR_L()) => true
  case (W_impL_R(), W_impL_R()) => true
  case (W_impL_L(), W_impL_L()) => true
  case (ImpR_I2(), ImpR_I2()) => true
  case (ImpR_I(), ImpR_I()) => true
  case (ImpL_I2(), ImpL_I2()) => true
  case (ImpL_I(), ImpL_I()) => true
  case (I_impR2(), I_impR2()) => true
  case (I_impR(), I_impR()) => true
  case (I_impL2(), I_impL2()) => true
  case (I_impL(), I_impL()) => true
  case (IW_R(), IW_R()) => true
  case (IW_L(), IW_L()) => true
  case (E_R(), E_R()) => true
  case (E_L(), E_L()) => true
  case (C_R(), C_R()) => true
  case (C_L(), C_L()) => true
  case (A_R2(), A_R2()) => true
  case (A_R(), A_R()) => true
  case (A_L2(), A_L2()) => true
  case (A_L(), A_L()) => true
}

abstract sealed class RuleOpAct
final case class BboxA_L() extends RuleOpAct
final case class BboxA_R() extends RuleOpAct
final case class BdiamA_L() extends RuleOpAct
final case class BdiamA_R() extends RuleOpAct
final case class FboxA_L() extends RuleOpAct
final case class FboxA_R() extends RuleOpAct
final case class FdiamA_L() extends RuleOpAct
final case class FdiamA_R() extends RuleOpAct
final case class One_L() extends RuleOpAct
final case class One_R() extends RuleOpAct
final case class Pre_L() extends RuleOpAct
final case class Pre_R() extends RuleOpAct

def equal_RuleOpAct(x0: RuleOpAct, x1: RuleOpAct): Boolean = (x0, x1) match {
  case (Pre_L(), Pre_R()) => false
  case (Pre_R(), Pre_L()) => false
  case (One_R(), Pre_R()) => false
  case (Pre_R(), One_R()) => false
  case (One_R(), Pre_L()) => false
  case (Pre_L(), One_R()) => false
  case (One_L(), Pre_R()) => false
  case (Pre_R(), One_L()) => false
  case (One_L(), Pre_L()) => false
  case (Pre_L(), One_L()) => false
  case (One_L(), One_R()) => false
  case (One_R(), One_L()) => false
  case (FdiamA_R(), Pre_R()) => false
  case (Pre_R(), FdiamA_R()) => false
  case (FdiamA_R(), Pre_L()) => false
  case (Pre_L(), FdiamA_R()) => false
  case (FdiamA_R(), One_R()) => false
  case (One_R(), FdiamA_R()) => false
  case (FdiamA_R(), One_L()) => false
  case (One_L(), FdiamA_R()) => false
  case (FdiamA_L(), Pre_R()) => false
  case (Pre_R(), FdiamA_L()) => false
  case (FdiamA_L(), Pre_L()) => false
  case (Pre_L(), FdiamA_L()) => false
  case (FdiamA_L(), One_R()) => false
  case (One_R(), FdiamA_L()) => false
  case (FdiamA_L(), One_L()) => false
  case (One_L(), FdiamA_L()) => false
  case (FdiamA_L(), FdiamA_R()) => false
  case (FdiamA_R(), FdiamA_L()) => false
  case (FboxA_R(), Pre_R()) => false
  case (Pre_R(), FboxA_R()) => false
  case (FboxA_R(), Pre_L()) => false
  case (Pre_L(), FboxA_R()) => false
  case (FboxA_R(), One_R()) => false
  case (One_R(), FboxA_R()) => false
  case (FboxA_R(), One_L()) => false
  case (One_L(), FboxA_R()) => false
  case (FboxA_R(), FdiamA_R()) => false
  case (FdiamA_R(), FboxA_R()) => false
  case (FboxA_R(), FdiamA_L()) => false
  case (FdiamA_L(), FboxA_R()) => false
  case (FboxA_L(), Pre_R()) => false
  case (Pre_R(), FboxA_L()) => false
  case (FboxA_L(), Pre_L()) => false
  case (Pre_L(), FboxA_L()) => false
  case (FboxA_L(), One_R()) => false
  case (One_R(), FboxA_L()) => false
  case (FboxA_L(), One_L()) => false
  case (One_L(), FboxA_L()) => false
  case (FboxA_L(), FdiamA_R()) => false
  case (FdiamA_R(), FboxA_L()) => false
  case (FboxA_L(), FdiamA_L()) => false
  case (FdiamA_L(), FboxA_L()) => false
  case (FboxA_L(), FboxA_R()) => false
  case (FboxA_R(), FboxA_L()) => false
  case (BdiamA_R(), Pre_R()) => false
  case (Pre_R(), BdiamA_R()) => false
  case (BdiamA_R(), Pre_L()) => false
  case (Pre_L(), BdiamA_R()) => false
  case (BdiamA_R(), One_R()) => false
  case (One_R(), BdiamA_R()) => false
  case (BdiamA_R(), One_L()) => false
  case (One_L(), BdiamA_R()) => false
  case (BdiamA_R(), FdiamA_R()) => false
  case (FdiamA_R(), BdiamA_R()) => false
  case (BdiamA_R(), FdiamA_L()) => false
  case (FdiamA_L(), BdiamA_R()) => false
  case (BdiamA_R(), FboxA_R()) => false
  case (FboxA_R(), BdiamA_R()) => false
  case (BdiamA_R(), FboxA_L()) => false
  case (FboxA_L(), BdiamA_R()) => false
  case (BdiamA_L(), Pre_R()) => false
  case (Pre_R(), BdiamA_L()) => false
  case (BdiamA_L(), Pre_L()) => false
  case (Pre_L(), BdiamA_L()) => false
  case (BdiamA_L(), One_R()) => false
  case (One_R(), BdiamA_L()) => false
  case (BdiamA_L(), One_L()) => false
  case (One_L(), BdiamA_L()) => false
  case (BdiamA_L(), FdiamA_R()) => false
  case (FdiamA_R(), BdiamA_L()) => false
  case (BdiamA_L(), FdiamA_L()) => false
  case (FdiamA_L(), BdiamA_L()) => false
  case (BdiamA_L(), FboxA_R()) => false
  case (FboxA_R(), BdiamA_L()) => false
  case (BdiamA_L(), FboxA_L()) => false
  case (FboxA_L(), BdiamA_L()) => false
  case (BdiamA_L(), BdiamA_R()) => false
  case (BdiamA_R(), BdiamA_L()) => false
  case (BboxA_R(), Pre_R()) => false
  case (Pre_R(), BboxA_R()) => false
  case (BboxA_R(), Pre_L()) => false
  case (Pre_L(), BboxA_R()) => false
  case (BboxA_R(), One_R()) => false
  case (One_R(), BboxA_R()) => false
  case (BboxA_R(), One_L()) => false
  case (One_L(), BboxA_R()) => false
  case (BboxA_R(), FdiamA_R()) => false
  case (FdiamA_R(), BboxA_R()) => false
  case (BboxA_R(), FdiamA_L()) => false
  case (FdiamA_L(), BboxA_R()) => false
  case (BboxA_R(), FboxA_R()) => false
  case (FboxA_R(), BboxA_R()) => false
  case (BboxA_R(), FboxA_L()) => false
  case (FboxA_L(), BboxA_R()) => false
  case (BboxA_R(), BdiamA_R()) => false
  case (BdiamA_R(), BboxA_R()) => false
  case (BboxA_R(), BdiamA_L()) => false
  case (BdiamA_L(), BboxA_R()) => false
  case (BboxA_L(), Pre_R()) => false
  case (Pre_R(), BboxA_L()) => false
  case (BboxA_L(), Pre_L()) => false
  case (Pre_L(), BboxA_L()) => false
  case (BboxA_L(), One_R()) => false
  case (One_R(), BboxA_L()) => false
  case (BboxA_L(), One_L()) => false
  case (One_L(), BboxA_L()) => false
  case (BboxA_L(), FdiamA_R()) => false
  case (FdiamA_R(), BboxA_L()) => false
  case (BboxA_L(), FdiamA_L()) => false
  case (FdiamA_L(), BboxA_L()) => false
  case (BboxA_L(), FboxA_R()) => false
  case (FboxA_R(), BboxA_L()) => false
  case (BboxA_L(), FboxA_L()) => false
  case (FboxA_L(), BboxA_L()) => false
  case (BboxA_L(), BdiamA_R()) => false
  case (BdiamA_R(), BboxA_L()) => false
  case (BboxA_L(), BdiamA_L()) => false
  case (BdiamA_L(), BboxA_L()) => false
  case (BboxA_L(), BboxA_R()) => false
  case (BboxA_R(), BboxA_L()) => false
  case (Pre_R(), Pre_R()) => true
  case (Pre_L(), Pre_L()) => true
  case (One_R(), One_R()) => true
  case (One_L(), One_L()) => true
  case (FdiamA_R(), FdiamA_R()) => true
  case (FdiamA_L(), FdiamA_L()) => true
  case (FboxA_R(), FboxA_R()) => true
  case (FboxA_L(), FboxA_L()) => true
  case (BdiamA_R(), BdiamA_R()) => true
  case (BdiamA_L(), BdiamA_L()) => true
  case (BboxA_R(), BboxA_R()) => true
  case (BboxA_L(), BboxA_L()) => true
}

abstract sealed class RuleGrish
final case class Grishin_L() extends RuleGrish
final case class Grishin_L2() extends RuleGrish
final case class Grishin_R() extends RuleGrish
final case class Grishin_R2() extends RuleGrish

def equal_RuleGrish(x0: RuleGrish, x1: RuleGrish): Boolean = (x0, x1) match {
  case (Grishin_R(), Grishin_R2()) => false
  case (Grishin_R2(), Grishin_R()) => false
  case (Grishin_L2(), Grishin_R2()) => false
  case (Grishin_R2(), Grishin_L2()) => false
  case (Grishin_L2(), Grishin_R()) => false
  case (Grishin_R(), Grishin_L2()) => false
  case (Grishin_L(), Grishin_R2()) => false
  case (Grishin_R2(), Grishin_L()) => false
  case (Grishin_L(), Grishin_R()) => false
  case (Grishin_R(), Grishin_L()) => false
  case (Grishin_L(), Grishin_L2()) => false
  case (Grishin_L2(), Grishin_L()) => false
  case (Grishin_R2(), Grishin_R2()) => true
  case (Grishin_R(), Grishin_R()) => true
  case (Grishin_L2(), Grishin_L2()) => true
  case (Grishin_L(), Grishin_L()) => true
}

abstract sealed class RuleDispK
final case class Back_forw_K() extends RuleDispK
final case class Back_forw_K2() extends RuleDispK
final case class Forw_back_K() extends RuleDispK
final case class Forw_back_K2() extends RuleDispK

def equal_RuleDispK(x0: RuleDispK, x1: RuleDispK): Boolean = (x0, x1) match {
  case (Forw_back_K(), Forw_back_K2()) => false
  case (Forw_back_K2(), Forw_back_K()) => false
  case (Back_forw_K2(), Forw_back_K2()) => false
  case (Forw_back_K2(), Back_forw_K2()) => false
  case (Back_forw_K2(), Forw_back_K()) => false
  case (Forw_back_K(), Back_forw_K2()) => false
  case (Back_forw_K(), Forw_back_K2()) => false
  case (Forw_back_K2(), Back_forw_K()) => false
  case (Back_forw_K(), Forw_back_K()) => false
  case (Forw_back_K(), Back_forw_K()) => false
  case (Back_forw_K(), Back_forw_K2()) => false
  case (Back_forw_K2(), Back_forw_K()) => false
  case (Forw_back_K2(), Forw_back_K2()) => true
  case (Forw_back_K(), Forw_back_K()) => true
  case (Back_forw_K2(), Back_forw_K2()) => true
  case (Back_forw_K(), Back_forw_K()) => true
}

abstract sealed class RuleDisp
final case class Comma_impL_disp() extends RuleDisp
final case class Comma_impL_disp2() extends RuleDisp
final case class Comma_impR_disp() extends RuleDisp
final case class Comma_impR_disp2() extends RuleDisp
final case class ImpL_comma_disp() extends RuleDisp
final case class ImpL_comma_disp2() extends RuleDisp
final case class ImpR_comma_disp() extends RuleDisp
final case class ImpR_comma_disp2() extends RuleDisp

def equal_RuleDisp(x0: RuleDisp, x1: RuleDisp): Boolean = (x0, x1) match {
  case (ImpR_comma_disp(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), ImpR_comma_disp()) => false
  case (ImpL_comma_disp2(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp2(), ImpR_comma_disp()) => false
  case (ImpR_comma_disp(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), ImpL_comma_disp()) => false
  case (ImpL_comma_disp(), ImpR_comma_disp()) => false
  case (ImpR_comma_disp(), ImpL_comma_disp()) => false
  case (ImpL_comma_disp(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp2(), ImpL_comma_disp()) => false
  case (Comma_impR_disp2(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), Comma_impR_disp2()) => false
  case (Comma_impR_disp2(), ImpR_comma_disp()) => false
  case (ImpR_comma_disp(), Comma_impR_disp2()) => false
  case (Comma_impR_disp2(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp2(), Comma_impR_disp2()) => false
  case (Comma_impR_disp2(), ImpL_comma_disp()) => false
  case (ImpL_comma_disp(), Comma_impR_disp2()) => false
  case (Comma_impR_disp(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), Comma_impR_disp()) => false
  case (Comma_impR_disp(), ImpR_comma_disp()) => false
  case (ImpR_comma_disp(), Comma_impR_disp()) => false
  case (Comma_impR_disp(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp2(), Comma_impR_disp()) => false
  case (Comma_impR_disp(), ImpL_comma_disp()) => false
  case (ImpL_comma_disp(), Comma_impR_disp()) => false
  case (Comma_impR_disp(), Comma_impR_disp2()) => false
  case (Comma_impR_disp2(), Comma_impR_disp()) => false
  case (Comma_impL_disp2(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), Comma_impL_disp2()) => false
  case (Comma_impL_disp2(), ImpR_comma_disp()) => false
  case (ImpR_comma_disp(), Comma_impL_disp2()) => false
  case (Comma_impL_disp2(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp2(), Comma_impL_disp2()) => false
  case (Comma_impL_disp2(), ImpL_comma_disp()) => false
  case (ImpL_comma_disp(), Comma_impL_disp2()) => false
  case (Comma_impL_disp2(), Comma_impR_disp2()) => false
  case (Comma_impR_disp2(), Comma_impL_disp2()) => false
  case (Comma_impL_disp2(), Comma_impR_disp()) => false
  case (Comma_impR_disp(), Comma_impL_disp2()) => false
  case (Comma_impL_disp(), ImpR_comma_disp2()) => false
  case (ImpR_comma_disp2(), Comma_impL_disp()) => false
  case (Comma_impL_disp(), ImpR_comma_disp()) => false
  case (ImpR_comma_disp(), Comma_impL_disp()) => false
  case (Comma_impL_disp(), ImpL_comma_disp2()) => false
  case (ImpL_comma_disp2(), Comma_impL_disp()) => false
  case (Comma_impL_disp(), ImpL_comma_disp()) => false
  case (ImpL_comma_disp(), Comma_impL_disp()) => false
  case (Comma_impL_disp(), Comma_impR_disp2()) => false
  case (Comma_impR_disp2(), Comma_impL_disp()) => false
  case (Comma_impL_disp(), Comma_impR_disp()) => false
  case (Comma_impR_disp(), Comma_impL_disp()) => false
  case (Comma_impL_disp(), Comma_impL_disp2()) => false
  case (Comma_impL_disp2(), Comma_impL_disp()) => false
  case (ImpR_comma_disp2(), ImpR_comma_disp2()) => true
  case (ImpR_comma_disp(), ImpR_comma_disp()) => true
  case (ImpL_comma_disp2(), ImpL_comma_disp2()) => true
  case (ImpL_comma_disp(), ImpL_comma_disp()) => true
  case (Comma_impR_disp2(), Comma_impR_disp2()) => true
  case (Comma_impR_disp(), Comma_impR_disp()) => true
  case (Comma_impL_disp2(), Comma_impL_disp2()) => true
  case (Comma_impL_disp(), Comma_impL_disp()) => true
}

abstract sealed class RuleZer
final case class Atom() extends RuleZer
final case class Id() extends RuleZer
final case class Partial() extends RuleZer
final case class Prem() extends RuleZer

def equal_RuleZer(x0: RuleZer, x1: RuleZer): Boolean = (x0, x1) match {
  case (Partial(), Prem()) => false
  case (Prem(), Partial()) => false
  case (Id(), Prem()) => false
  case (Prem(), Id()) => false
  case (Id(), Partial()) => false
  case (Partial(), Id()) => false
  case (Atom(), Prem()) => false
  case (Prem(), Atom()) => false
  case (Atom(), Partial()) => false
  case (Partial(), Atom()) => false
  case (Atom(), Id()) => false
  case (Id(), Atom()) => false
  case (Prem(), Prem()) => true
  case (Partial(), Partial()) => true
  case (Id(), Id()) => true
  case (Atom(), Atom()) => true
}

abstract sealed class RuleOpK
final case class BboxK_L() extends RuleOpK
final case class BboxK_R() extends RuleOpK
final case class BdiamK_L() extends RuleOpK
final case class BdiamK_R() extends RuleOpK
final case class FboxK_L() extends RuleOpK
final case class FboxK_R() extends RuleOpK
final case class FdiamK_L() extends RuleOpK
final case class FdiamK_R() extends RuleOpK

def equal_RuleOpK(x0: RuleOpK, x1: RuleOpK): Boolean = (x0, x1) match {
  case (FdiamK_L(), FdiamK_R()) => false
  case (FdiamK_R(), FdiamK_L()) => false
  case (FboxK_R(), FdiamK_R()) => false
  case (FdiamK_R(), FboxK_R()) => false
  case (FboxK_R(), FdiamK_L()) => false
  case (FdiamK_L(), FboxK_R()) => false
  case (FboxK_L(), FdiamK_R()) => false
  case (FdiamK_R(), FboxK_L()) => false
  case (FboxK_L(), FdiamK_L()) => false
  case (FdiamK_L(), FboxK_L()) => false
  case (FboxK_L(), FboxK_R()) => false
  case (FboxK_R(), FboxK_L()) => false
  case (BdiamK_R(), FdiamK_R()) => false
  case (FdiamK_R(), BdiamK_R()) => false
  case (BdiamK_R(), FdiamK_L()) => false
  case (FdiamK_L(), BdiamK_R()) => false
  case (BdiamK_R(), FboxK_R()) => false
  case (FboxK_R(), BdiamK_R()) => false
  case (BdiamK_R(), FboxK_L()) => false
  case (FboxK_L(), BdiamK_R()) => false
  case (BdiamK_L(), FdiamK_R()) => false
  case (FdiamK_R(), BdiamK_L()) => false
  case (BdiamK_L(), FdiamK_L()) => false
  case (FdiamK_L(), BdiamK_L()) => false
  case (BdiamK_L(), FboxK_R()) => false
  case (FboxK_R(), BdiamK_L()) => false
  case (BdiamK_L(), FboxK_L()) => false
  case (FboxK_L(), BdiamK_L()) => false
  case (BdiamK_L(), BdiamK_R()) => false
  case (BdiamK_R(), BdiamK_L()) => false
  case (BboxK_R(), FdiamK_R()) => false
  case (FdiamK_R(), BboxK_R()) => false
  case (BboxK_R(), FdiamK_L()) => false
  case (FdiamK_L(), BboxK_R()) => false
  case (BboxK_R(), FboxK_R()) => false
  case (FboxK_R(), BboxK_R()) => false
  case (BboxK_R(), FboxK_L()) => false
  case (FboxK_L(), BboxK_R()) => false
  case (BboxK_R(), BdiamK_R()) => false
  case (BdiamK_R(), BboxK_R()) => false
  case (BboxK_R(), BdiamK_L()) => false
  case (BdiamK_L(), BboxK_R()) => false
  case (BboxK_L(), FdiamK_R()) => false
  case (FdiamK_R(), BboxK_L()) => false
  case (BboxK_L(), FdiamK_L()) => false
  case (FdiamK_L(), BboxK_L()) => false
  case (BboxK_L(), FboxK_R()) => false
  case (FboxK_R(), BboxK_L()) => false
  case (BboxK_L(), FboxK_L()) => false
  case (FboxK_L(), BboxK_L()) => false
  case (BboxK_L(), BdiamK_R()) => false
  case (BdiamK_R(), BboxK_L()) => false
  case (BboxK_L(), BdiamK_L()) => false
  case (BdiamK_L(), BboxK_L()) => false
  case (BboxK_L(), BboxK_R()) => false
  case (BboxK_R(), BboxK_L()) => false
  case (FdiamK_R(), FdiamK_R()) => true
  case (FdiamK_L(), FdiamK_L()) => true
  case (FboxK_R(), FboxK_R()) => true
  case (FboxK_L(), FboxK_L()) => true
  case (BdiamK_R(), BdiamK_R()) => true
  case (BdiamK_L(), BdiamK_L()) => true
  case (BboxK_R(), BboxK_R()) => true
  case (BboxK_L(), BboxK_L()) => true
}

abstract sealed class RuleCut
final case class SingleCut() extends RuleCut

def equal_RuleCut(x0: RuleCut, x1: RuleCut): Boolean = (x0, x1) match {
  case (SingleCut(), SingleCut()) => true
}

abstract sealed class RuleOp
final case class And_L() extends RuleOp
final case class And_R() extends RuleOp
final case class Bot_L() extends RuleOp
final case class Bot_R() extends RuleOp
final case class DImpL_L() extends RuleOp
final case class DImpL_R() extends RuleOp
final case class DImpR_L() extends RuleOp
final case class DImpR_R() extends RuleOp
final case class ImpL_L() extends RuleOp
final case class ImpL_R() extends RuleOp
final case class ImpR_L() extends RuleOp
final case class ImpR_R() extends RuleOp
final case class Or_L() extends RuleOp
final case class Or_R() extends RuleOp
final case class Top_L() extends RuleOp
final case class Top_R() extends RuleOp

def equal_RuleOp(x0: RuleOp, x1: RuleOp): Boolean = (x0, x1) match {
  case (Top_L(), Top_R()) => false
  case (Top_R(), Top_L()) => false
  case (Or_R(), Top_R()) => false
  case (Top_R(), Or_R()) => false
  case (Or_R(), Top_L()) => false
  case (Top_L(), Or_R()) => false
  case (Or_L(), Top_R()) => false
  case (Top_R(), Or_L()) => false
  case (Or_L(), Top_L()) => false
  case (Top_L(), Or_L()) => false
  case (Or_L(), Or_R()) => false
  case (Or_R(), Or_L()) => false
  case (ImpR_R(), Top_R()) => false
  case (Top_R(), ImpR_R()) => false
  case (ImpR_R(), Top_L()) => false
  case (Top_L(), ImpR_R()) => false
  case (ImpR_R(), Or_R()) => false
  case (Or_R(), ImpR_R()) => false
  case (ImpR_R(), Or_L()) => false
  case (Or_L(), ImpR_R()) => false
  case (ImpR_L(), Top_R()) => false
  case (Top_R(), ImpR_L()) => false
  case (ImpR_L(), Top_L()) => false
  case (Top_L(), ImpR_L()) => false
  case (ImpR_L(), Or_R()) => false
  case (Or_R(), ImpR_L()) => false
  case (ImpR_L(), Or_L()) => false
  case (Or_L(), ImpR_L()) => false
  case (ImpR_L(), ImpR_R()) => false
  case (ImpR_R(), ImpR_L()) => false
  case (ImpL_R(), Top_R()) => false
  case (Top_R(), ImpL_R()) => false
  case (ImpL_R(), Top_L()) => false
  case (Top_L(), ImpL_R()) => false
  case (ImpL_R(), Or_R()) => false
  case (Or_R(), ImpL_R()) => false
  case (ImpL_R(), Or_L()) => false
  case (Or_L(), ImpL_R()) => false
  case (ImpL_R(), ImpR_R()) => false
  case (ImpR_R(), ImpL_R()) => false
  case (ImpL_R(), ImpR_L()) => false
  case (ImpR_L(), ImpL_R()) => false
  case (ImpL_L(), Top_R()) => false
  case (Top_R(), ImpL_L()) => false
  case (ImpL_L(), Top_L()) => false
  case (Top_L(), ImpL_L()) => false
  case (ImpL_L(), Or_R()) => false
  case (Or_R(), ImpL_L()) => false
  case (ImpL_L(), Or_L()) => false
  case (Or_L(), ImpL_L()) => false
  case (ImpL_L(), ImpR_R()) => false
  case (ImpR_R(), ImpL_L()) => false
  case (ImpL_L(), ImpR_L()) => false
  case (ImpR_L(), ImpL_L()) => false
  case (ImpL_L(), ImpL_R()) => false
  case (ImpL_R(), ImpL_L()) => false
  case (DImpR_R(), Top_R()) => false
  case (Top_R(), DImpR_R()) => false
  case (DImpR_R(), Top_L()) => false
  case (Top_L(), DImpR_R()) => false
  case (DImpR_R(), Or_R()) => false
  case (Or_R(), DImpR_R()) => false
  case (DImpR_R(), Or_L()) => false
  case (Or_L(), DImpR_R()) => false
  case (DImpR_R(), ImpR_R()) => false
  case (ImpR_R(), DImpR_R()) => false
  case (DImpR_R(), ImpR_L()) => false
  case (ImpR_L(), DImpR_R()) => false
  case (DImpR_R(), ImpL_R()) => false
  case (ImpL_R(), DImpR_R()) => false
  case (DImpR_R(), ImpL_L()) => false
  case (ImpL_L(), DImpR_R()) => false
  case (DImpR_L(), Top_R()) => false
  case (Top_R(), DImpR_L()) => false
  case (DImpR_L(), Top_L()) => false
  case (Top_L(), DImpR_L()) => false
  case (DImpR_L(), Or_R()) => false
  case (Or_R(), DImpR_L()) => false
  case (DImpR_L(), Or_L()) => false
  case (Or_L(), DImpR_L()) => false
  case (DImpR_L(), ImpR_R()) => false
  case (ImpR_R(), DImpR_L()) => false
  case (DImpR_L(), ImpR_L()) => false
  case (ImpR_L(), DImpR_L()) => false
  case (DImpR_L(), ImpL_R()) => false
  case (ImpL_R(), DImpR_L()) => false
  case (DImpR_L(), ImpL_L()) => false
  case (ImpL_L(), DImpR_L()) => false
  case (DImpR_L(), DImpR_R()) => false
  case (DImpR_R(), DImpR_L()) => false
  case (DImpL_R(), Top_R()) => false
  case (Top_R(), DImpL_R()) => false
  case (DImpL_R(), Top_L()) => false
  case (Top_L(), DImpL_R()) => false
  case (DImpL_R(), Or_R()) => false
  case (Or_R(), DImpL_R()) => false
  case (DImpL_R(), Or_L()) => false
  case (Or_L(), DImpL_R()) => false
  case (DImpL_R(), ImpR_R()) => false
  case (ImpR_R(), DImpL_R()) => false
  case (DImpL_R(), ImpR_L()) => false
  case (ImpR_L(), DImpL_R()) => false
  case (DImpL_R(), ImpL_R()) => false
  case (ImpL_R(), DImpL_R()) => false
  case (DImpL_R(), ImpL_L()) => false
  case (ImpL_L(), DImpL_R()) => false
  case (DImpL_R(), DImpR_R()) => false
  case (DImpR_R(), DImpL_R()) => false
  case (DImpL_R(), DImpR_L()) => false
  case (DImpR_L(), DImpL_R()) => false
  case (DImpL_L(), Top_R()) => false
  case (Top_R(), DImpL_L()) => false
  case (DImpL_L(), Top_L()) => false
  case (Top_L(), DImpL_L()) => false
  case (DImpL_L(), Or_R()) => false
  case (Or_R(), DImpL_L()) => false
  case (DImpL_L(), Or_L()) => false
  case (Or_L(), DImpL_L()) => false
  case (DImpL_L(), ImpR_R()) => false
  case (ImpR_R(), DImpL_L()) => false
  case (DImpL_L(), ImpR_L()) => false
  case (ImpR_L(), DImpL_L()) => false
  case (DImpL_L(), ImpL_R()) => false
  case (ImpL_R(), DImpL_L()) => false
  case (DImpL_L(), ImpL_L()) => false
  case (ImpL_L(), DImpL_L()) => false
  case (DImpL_L(), DImpR_R()) => false
  case (DImpR_R(), DImpL_L()) => false
  case (DImpL_L(), DImpR_L()) => false
  case (DImpR_L(), DImpL_L()) => false
  case (DImpL_L(), DImpL_R()) => false
  case (DImpL_R(), DImpL_L()) => false
  case (Bot_R(), Top_R()) => false
  case (Top_R(), Bot_R()) => false
  case (Bot_R(), Top_L()) => false
  case (Top_L(), Bot_R()) => false
  case (Bot_R(), Or_R()) => false
  case (Or_R(), Bot_R()) => false
  case (Bot_R(), Or_L()) => false
  case (Or_L(), Bot_R()) => false
  case (Bot_R(), ImpR_R()) => false
  case (ImpR_R(), Bot_R()) => false
  case (Bot_R(), ImpR_L()) => false
  case (ImpR_L(), Bot_R()) => false
  case (Bot_R(), ImpL_R()) => false
  case (ImpL_R(), Bot_R()) => false
  case (Bot_R(), ImpL_L()) => false
  case (ImpL_L(), Bot_R()) => false
  case (Bot_R(), DImpR_R()) => false
  case (DImpR_R(), Bot_R()) => false
  case (Bot_R(), DImpR_L()) => false
  case (DImpR_L(), Bot_R()) => false
  case (Bot_R(), DImpL_R()) => false
  case (DImpL_R(), Bot_R()) => false
  case (Bot_R(), DImpL_L()) => false
  case (DImpL_L(), Bot_R()) => false
  case (Bot_L(), Top_R()) => false
  case (Top_R(), Bot_L()) => false
  case (Bot_L(), Top_L()) => false
  case (Top_L(), Bot_L()) => false
  case (Bot_L(), Or_R()) => false
  case (Or_R(), Bot_L()) => false
  case (Bot_L(), Or_L()) => false
  case (Or_L(), Bot_L()) => false
  case (Bot_L(), ImpR_R()) => false
  case (ImpR_R(), Bot_L()) => false
  case (Bot_L(), ImpR_L()) => false
  case (ImpR_L(), Bot_L()) => false
  case (Bot_L(), ImpL_R()) => false
  case (ImpL_R(), Bot_L()) => false
  case (Bot_L(), ImpL_L()) => false
  case (ImpL_L(), Bot_L()) => false
  case (Bot_L(), DImpR_R()) => false
  case (DImpR_R(), Bot_L()) => false
  case (Bot_L(), DImpR_L()) => false
  case (DImpR_L(), Bot_L()) => false
  case (Bot_L(), DImpL_R()) => false
  case (DImpL_R(), Bot_L()) => false
  case (Bot_L(), DImpL_L()) => false
  case (DImpL_L(), Bot_L()) => false
  case (Bot_L(), Bot_R()) => false
  case (Bot_R(), Bot_L()) => false
  case (And_R(), Top_R()) => false
  case (Top_R(), And_R()) => false
  case (And_R(), Top_L()) => false
  case (Top_L(), And_R()) => false
  case (And_R(), Or_R()) => false
  case (Or_R(), And_R()) => false
  case (And_R(), Or_L()) => false
  case (Or_L(), And_R()) => false
  case (And_R(), ImpR_R()) => false
  case (ImpR_R(), And_R()) => false
  case (And_R(), ImpR_L()) => false
  case (ImpR_L(), And_R()) => false
  case (And_R(), ImpL_R()) => false
  case (ImpL_R(), And_R()) => false
  case (And_R(), ImpL_L()) => false
  case (ImpL_L(), And_R()) => false
  case (And_R(), DImpR_R()) => false
  case (DImpR_R(), And_R()) => false
  case (And_R(), DImpR_L()) => false
  case (DImpR_L(), And_R()) => false
  case (And_R(), DImpL_R()) => false
  case (DImpL_R(), And_R()) => false
  case (And_R(), DImpL_L()) => false
  case (DImpL_L(), And_R()) => false
  case (And_R(), Bot_R()) => false
  case (Bot_R(), And_R()) => false
  case (And_R(), Bot_L()) => false
  case (Bot_L(), And_R()) => false
  case (And_L(), Top_R()) => false
  case (Top_R(), And_L()) => false
  case (And_L(), Top_L()) => false
  case (Top_L(), And_L()) => false
  case (And_L(), Or_R()) => false
  case (Or_R(), And_L()) => false
  case (And_L(), Or_L()) => false
  case (Or_L(), And_L()) => false
  case (And_L(), ImpR_R()) => false
  case (ImpR_R(), And_L()) => false
  case (And_L(), ImpR_L()) => false
  case (ImpR_L(), And_L()) => false
  case (And_L(), ImpL_R()) => false
  case (ImpL_R(), And_L()) => false
  case (And_L(), ImpL_L()) => false
  case (ImpL_L(), And_L()) => false
  case (And_L(), DImpR_R()) => false
  case (DImpR_R(), And_L()) => false
  case (And_L(), DImpR_L()) => false
  case (DImpR_L(), And_L()) => false
  case (And_L(), DImpL_R()) => false
  case (DImpL_R(), And_L()) => false
  case (And_L(), DImpL_L()) => false
  case (DImpL_L(), And_L()) => false
  case (And_L(), Bot_R()) => false
  case (Bot_R(), And_L()) => false
  case (And_L(), Bot_L()) => false
  case (Bot_L(), And_L()) => false
  case (And_L(), And_R()) => false
  case (And_R(), And_L()) => false
  case (Top_R(), Top_R()) => true
  case (Top_L(), Top_L()) => true
  case (Or_R(), Or_R()) => true
  case (Or_L(), Or_L()) => true
  case (ImpR_R(), ImpR_R()) => true
  case (ImpR_L(), ImpR_L()) => true
  case (ImpL_R(), ImpL_R()) => true
  case (ImpL_L(), ImpL_L()) => true
  case (DImpR_R(), DImpR_R()) => true
  case (DImpR_L(), DImpR_L()) => true
  case (DImpL_R(), DImpL_R()) => true
  case (DImpL_L(), DImpL_L()) => true
  case (Bot_R(), Bot_R()) => true
  case (Bot_L(), Bot_L()) => true
  case (And_R(), And_R()) => true
  case (And_L(), And_L()) => true
}

abstract sealed class Prooftree
final case class Prooftreea(a: Sequent, b: Rule, c: List[Prooftree]) extends
  Prooftree

abstract sealed class Rule
final case class RuleBigcommaa(a: RuleBigcomma) extends Rule
final case class RuleCuta(a: RuleCut) extends Rule
final case class RuleDispa(a: RuleDisp) extends Rule
final case class RuleDispActa(a: RuleDispAct) extends Rule
final case class RuleDispKa(a: RuleDispK) extends Rule
final case class RuleGrisha(a: RuleGrish) extends Rule
final case class RuleKnowledgea(a: RuleKnowledge) extends Rule
final case class RuleOpa(a: RuleOp) extends Rule
final case class RuleOpActa(a: RuleOpAct) extends Rule
final case class RuleOpKa(a: RuleOpK) extends Rule
final case class RuleStructa(a: RuleStruct) extends Rule
final case class RuleStructActa(a: RuleStructAct) extends Rule
final case class RuleStructEAa(a: RuleStructEA) extends Rule
final case class RuleStructKa(a: RuleStructK) extends Rule
final case class RuleSwapina(a: RuleSwapin) extends Rule
final case class RuleSwapouta(a: RuleSwapout) extends Rule
final case class RuleZera(a: RuleZer) extends Rule
final case class RuleMacro(a: List[Char], b: Prooftree) extends Rule
final case class Fail() extends Rule

def equal_Rule(x0: Rule, x1: Rule): Boolean = (x0, x1) match {
  case (RuleMacro(x181, x182), Fail()) => false
  case (Fail(), RuleMacro(x181, x182)) => false
  case (RuleZera(x17), Fail()) => false
  case (Fail(), RuleZera(x17)) => false
  case (RuleZera(x17), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleZera(x17)) => false
  case (RuleSwapouta(x16), Fail()) => false
  case (Fail(), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleZera(x17)) => false
  case (RuleZera(x17), RuleSwapouta(x16)) => false
  case (RuleSwapina(x15), Fail()) => false
  case (Fail(), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleZera(x17)) => false
  case (RuleZera(x17), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleSwapina(x15)) => false
  case (RuleStructKa(x14), Fail()) => false
  case (Fail(), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleZera(x17)) => false
  case (RuleZera(x17), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleStructKa(x14)) => false
  case (RuleStructEAa(x13), Fail()) => false
  case (Fail(), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleZera(x17)) => false
  case (RuleZera(x17), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleStructEAa(x13)) => false
  case (RuleStructActa(x12), Fail()) => false
  case (Fail(), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleZera(x17)) => false
  case (RuleZera(x17), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleStructActa(x12)) => false
  case (RuleStructa(x11), Fail()) => false
  case (Fail(), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleZera(x17)) => false
  case (RuleZera(x17), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleStructa(x11)) => false
  case (RuleOpKa(x10), Fail()) => false
  case (Fail(), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleZera(x17)) => false
  case (RuleZera(x17), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleOpKa(x10)) => false
  case (RuleOpActa(x9), Fail()) => false
  case (Fail(), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleZera(x17)) => false
  case (RuleZera(x17), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleOpActa(x9)) => false
  case (RuleOpa(x8), Fail()) => false
  case (Fail(), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleZera(x17)) => false
  case (RuleZera(x17), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleOpa(x8)) => false
  case (RuleKnowledgea(x7), Fail()) => false
  case (Fail(), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleZera(x17)) => false
  case (RuleZera(x17), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleKnowledgea(x7)) => false
  case (RuleGrisha(x6), Fail()) => false
  case (Fail(), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleZera(x17)) => false
  case (RuleZera(x17), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleGrisha(x6)) => false
  case (RuleDispKa(x5), Fail()) => false
  case (Fail(), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleZera(x17)) => false
  case (RuleZera(x17), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleDispKa(x5)) => false
  case (RuleDispActa(x4), Fail()) => false
  case (Fail(), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleZera(x17)) => false
  case (RuleZera(x17), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleDispActa(x4)) => false
  case (RuleDispa(x3), Fail()) => false
  case (Fail(), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleZera(x17)) => false
  case (RuleZera(x17), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleDispa(x3)) => false
  case (RuleCuta(x2), Fail()) => false
  case (Fail(), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleZera(x17)) => false
  case (RuleZera(x17), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleCuta(x2)) => false
  case (RuleBigcommaa(x1), Fail()) => false
  case (Fail(), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleMacro(x181, x182)) => false
  case (RuleMacro(x181, x182), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleZera(x17)) => false
  case (RuleZera(x17), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleSwapouta(x16)) => false
  case (RuleSwapouta(x16), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleSwapina(x15)) => false
  case (RuleSwapina(x15), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleStructKa(x14)) => false
  case (RuleStructKa(x14), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleStructEAa(x13)) => false
  case (RuleStructEAa(x13), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleStructActa(x12)) => false
  case (RuleStructActa(x12), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleStructa(x11)) => false
  case (RuleStructa(x11), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleOpKa(x10)) => false
  case (RuleOpKa(x10), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleOpActa(x9)) => false
  case (RuleOpActa(x9), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleOpa(x8)) => false
  case (RuleOpa(x8), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleKnowledgea(x7)) => false
  case (RuleKnowledgea(x7), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleGrisha(x6)) => false
  case (RuleGrisha(x6), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleDispKa(x5)) => false
  case (RuleDispKa(x5), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleDispActa(x4)) => false
  case (RuleDispActa(x4), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleDispa(x3)) => false
  case (RuleDispa(x3), RuleBigcommaa(x1)) => false
  case (RuleBigcommaa(x1), RuleCuta(x2)) => false
  case (RuleCuta(x2), RuleBigcommaa(x1)) => false
  case (RuleMacro(x181, x182), RuleMacro(y181, y182)) =>
    equal_lista[Char](x181, y181) && equal_Prooftreea(x182, y182)
  case (RuleZera(x17), RuleZera(y17)) => equal_RuleZer(x17, y17)
  case (RuleSwapouta(x16), RuleSwapouta(y16)) => equal_RuleSwapout(x16, y16)
  case (RuleSwapina(x15), RuleSwapina(y15)) => equal_RuleSwapin(x15, y15)
  case (RuleStructKa(x14), RuleStructKa(y14)) => equal_RuleStructK(x14, y14)
  case (RuleStructEAa(x13), RuleStructEAa(y13)) => equal_RuleStructEA(x13, y13)
  case (RuleStructActa(x12), RuleStructActa(y12)) =>
    equal_RuleStructAct(x12, y12)
  case (RuleStructa(x11), RuleStructa(y11)) => equal_RuleStruct(x11, y11)
  case (RuleOpKa(x10), RuleOpKa(y10)) => equal_RuleOpK(x10, y10)
  case (RuleOpActa(x9), RuleOpActa(y9)) => equal_RuleOpAct(x9, y9)
  case (RuleOpa(x8), RuleOpa(y8)) => equal_RuleOp(x8, y8)
  case (RuleKnowledgea(x7), RuleKnowledgea(y7)) => equal_RuleKnowledge(x7, y7)
  case (RuleGrisha(x6), RuleGrisha(y6)) => equal_RuleGrish(x6, y6)
  case (RuleDispKa(x5), RuleDispKa(y5)) => equal_RuleDispK(x5, y5)
  case (RuleDispActa(x4), RuleDispActa(y4)) => equal_RuleDispAct(x4, y4)
  case (RuleDispa(x3), RuleDispa(y3)) => equal_RuleDisp(x3, y3)
  case (RuleCuta(x2), RuleCuta(y2)) => equal_RuleCut(x2, y2)
  case (RuleBigcommaa(x1), RuleBigcommaa(y1)) => equal_RuleBigcomma(x1, y1)
  case (Fail(), Fail()) => true
}

def equal_Prooftreea(x0: Prooftree, x1: Prooftree): Boolean = (x0, x1) match {
  case (Prooftreea(x1, x2, x3), Prooftreea(y1, y2, y3)) =>
    equal_Sequenta(x1, y1) &&
      (equal_Rule(x2, y2) && equal_lista[Prooftree](x3, y3))
}

implicit def equal_Prooftree: equal[Prooftree] = new equal[Prooftree] {
  val `DEAK.equal` = (a: Prooftree, b: Prooftree) => equal_Prooftreea(a, b)
}

implicit def equal_Agent: equal[Agent] = new equal[Agent] {
  val `DEAK.equal` = (a: Agent, b: Agent) => equal_Agenta(a, b)
}

implicit def equal_Action: equal[Action] = new equal[Action] {
  val `DEAK.equal` = (a: Action, b: Action) => equal_Actiona(a, b)
}

implicit def equal_Atprop: equal[Atprop] = new equal[Atprop] {
  val `DEAK.equal` = (a: Atprop, b: Atprop) => equal_Atpropa(a, b)
}

implicit def equal_Formula: equal[Formula] = new equal[Formula] {
  val `DEAK.equal` = (a: Formula, b: Formula) => equal_Formulaa(a, b)
}

implicit def equal_Sequent: equal[Sequent] = new equal[Sequent] {
  val `DEAK.equal` = (a: Sequent, b: Sequent) => equal_Sequenta(a, b)
}

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

def bot_set[A]: set[A] = seta[A](Nil)

def removeAll[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def inserta[A : equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def freevars_Atprop(x0: Atprop): set[Atprop] = x0 match {
  case Atprop_Freevar(vara) =>
    insert[Atprop](Atprop_Freevar(vara), bot_set[Atprop])
  case Atpropa(uu) => bot_set[Atprop]
}

def freevars_Action(x0: Action): set[Action] = x0 match {
  case Action_Freevar(vara) =>
    insert[Action](Action_Freevar(vara), bot_set[Action])
  case Actiona(v) => bot_set[Action]
}

def freevars_Agent(x0: Agent): set[Agent] = x0 match {
  case Agent_Freevar(vara) => insert[Agent](Agent_Freevar(vara), bot_set[Agent])
  case Agenta(v) => bot_set[Agent]
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def sup_set[A : equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) => coset[A](filter[A]((x: A) => ! (member[A](x, a)), xs))
  case (seta(xs), a) =>
    fold[A, set[A]]((aa: A) => (b: set[A]) => insert[A](aa, b), xs, a)
}

abstract sealed class nibble
final case class Nibble0() extends nibble
final case class Nibble1() extends nibble
final case class Nibble2() extends nibble
final case class Nibble3() extends nibble
final case class Nibble4() extends nibble
final case class Nibble5() extends nibble
final case class Nibble6() extends nibble
final case class Nibble7() extends nibble
final case class Nibble8() extends nibble
final case class Nibble9() extends nibble
final case class NibbleA() extends nibble
final case class NibbleB() extends nibble
final case class NibbleC() extends nibble
final case class NibbleD() extends nibble
final case class NibbleE() extends nibble
final case class NibbleF() extends nibble

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def freevars_Formula(x0: Formula): set[Formula] = x0 match {
  case Formula_Atprop(vara) =>
    image[Atprop,
           Formula]((a: Atprop) => Formula_Atprop(a), freevars_Atprop(vara))
  case Formula_Bin(var1, uu, var2) =>
    sup_set[Formula](freevars_Formula(var1), freevars_Formula(var2))
  case Formula_Freevar(vara) =>
    insert[Formula](Formula_Freevar(vara), bot_set[Formula])
  case Formula_Action_Formula(uv, act1, form1) =>
    sup_set[Formula](image[Action,
                            Formula]((a: Action) => Formula_Action(a),
                                      freevars_Action(act1)),
                      freevars_Formula(form1))
  case Formula_Agent_Formula(uw, ag1, form1) =>
    sup_set[Formula](image[Agent,
                            Formula]((a: Agent) => Formula_Agent(a),
                                      freevars_Agent(ag1)),
                      freevars_Formula(form1))
  case Formula_Precondition(act1) =>
    image[Action,
           Formula]((a: Action) => Formula_Action(a), freevars_Action(act1))
  case Formula_Zer(act1) => bot_set[Formula]
  case Formula_Agent(ag1) =>
    insert[Formula](Formula_Freevar(List('a', 'g')), bot_set[Formula])
  case Formula_Action(act1) =>
    insert[Formula](Formula_Freevar(List('a', 'c', 't')), bot_set[Formula])
}

def comp[A, B, C](f: A => B, g: C => A): C => B = (x: C) => f(g(x))

def id[A]: A => A = (x: A) => x

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def freevars_Structure(x0: Structure): set[Structure] = x0 match {
  case Structure_Formula(vara) =>
    image[Formula,
           Structure]((a: Formula) => Structure_Formula(a),
                       freevars_Formula(vara))
  case Structure_Bin(var1, uu, var2) =>
    sup_set[Structure](freevars_Structure(var1), freevars_Structure(var2))
  case Structure_Freevar(vara) =>
    insert[Structure](Structure_Freevar(vara), bot_set[Structure])
  case Structure_Action_Structure(uv, act1, struct) =>
    sup_set[Structure](image[Action,
                              Structure]((x: Action) =>
   Structure_Formula(Formula_Action(x)),
  freevars_Action(act1)),
                        freevars_Structure(struct))
  case Structure_Agent_Structure(uw, ag1, struct) =>
    sup_set[Structure](image[Agent,
                              Structure]((x: Agent) =>
   Structure_Formula(Formula_Agent(x)),
  freevars_Agent(ag1)),
                        freevars_Structure(struct))
  case Structure_Phi(act1) =>
    image[Action,
           Structure]((x: Action) => Structure_Formula(Formula_Action(x)),
                       freevars_Action(act1))
  case Structure_Bigcomma(list) =>
    (foldr[Structure,
            set[Structure]](comp[set[Structure],
                                  (set[Structure]) => set[Structure],
                                  Structure]((a: set[Structure]) =>
       (b: set[Structure]) => sup_set[Structure](a, b),
      (a: Structure) => freevars_Structure(a)),
                             list)).apply(bot_set[Structure])
  case Structure_Zer(v) => bot_set[Structure]
}

def freevars_Sequent(x0: Sequent): set[Sequent] = x0 match {
  case Sequenta(var1, var2) =>
    image[Structure,
           Sequent]((a: Structure) => Sequent_Structure(a),
                     sup_set[Structure](freevars_Structure(var1),
 freevars_Structure(var2)))
  case Sequent_Structure(v) => bot_set[Sequent]
}

def replace_Atprop_aux(xa0: Atprop, mtch: Atprop, x: Atprop): Atprop =
  (xa0, mtch, x) match {
  case (Atprop_Freevar(a), mtch, x) =>
    (x match {
       case Atpropa(_) => x
       case Atprop_Freevar(free) =>
         (if (equal_lista[Char](a, free)) mtch else Atprop_Freevar(free))
     })
  case (Atpropa(a), mtch, x) => x
}

def replace_Atprop(x0: (Atprop, Atprop), c: Atprop): Atprop = (x0, c) match {
  case ((a, b), c) => replace_Atprop_aux(a, b, c)
}

def replace_Action(uu: (Action, Action), pttrn: Action): Action = (uu, pttrn)
  match {
  case ((Action_Freevar(x), mtch), Action_Freevar(free)) =>
    (if (equal_lista[Char](x, free)) mtch else Action_Freevar(free))
  case ((Actiona(vb), va), pttrn) => pttrn
  case (uu, Actiona(v)) => Actiona(v)
}

def replace_Agent(uu: (Agent, Agent), pttrn: Agent): Agent = (uu, pttrn) match {
  case ((Agent_Freevar(x), mtch), Agent_Freevar(free)) =>
    (if (equal_lista[Char](x, free)) mtch else Agent_Freevar(free))
  case ((Agenta(vb), va), pttrn) => pttrn
  case (uu, Agenta(v)) => Agenta(v)
}

def replace_Formula_aux(x: Formula, mtch: Formula, xa2: Formula): Formula =
  (x, mtch, xa2) match {
  case (x, mtch, Formula_Atprop(a)) =>
    (x match {
       case Formula_Action(_) => Formula_Atprop(a)
       case Formula_Action_Formula(_, _, _) => Formula_Atprop(a)
       case Formula_Agent(_) => Formula_Atprop(a)
       case Formula_Agent_Formula(_, _, _) => Formula_Atprop(a)
       case Formula_Atprop(xa) =>
         (mtch match {
            case Formula_Action(_) => Formula_Atprop(a)
            case Formula_Action_Formula(_, _, _) => Formula_Atprop(a)
            case Formula_Agent(_) => Formula_Atprop(a)
            case Formula_Agent_Formula(_, _, _) => Formula_Atprop(a)
            case Formula_Atprop(mtcha) =>
              Formula_Atprop(replace_Atprop((xa, mtcha), a))
            case Formula_Bin(_, _, _) => Formula_Atprop(a)
            case Formula_Freevar(_) => Formula_Atprop(a)
            case Formula_Precondition(_) => Formula_Atprop(a)
            case Formula_Zer(_) => Formula_Atprop(a)
          })
       case Formula_Bin(_, _, _) => Formula_Atprop(a)
       case Formula_Freevar(_) => Formula_Atprop(a)
       case Formula_Precondition(_) => Formula_Atprop(a)
       case Formula_Zer(_) => Formula_Atprop(a)
     })
  case (x, mtch, Formula_Bin(var1, op1, var2)) =>
    Formula_Bin(replace_Formula_aux(x, mtch, var1), op1,
                 replace_Formula_aux(x, mtch, var2))
  case (x, mtch, Formula_Freevar(free)) =>
    (if (equal_Formulaa(x, Formula_Freevar(free))) mtch
      else Formula_Freevar(free))
  case (x, mtch, Formula_Action_Formula(op1, act1, form1)) =>
    (x match {
       case Formula_Action(xa) =>
         (mtch match {
            case Formula_Action(mtcha) =>
              Formula_Action_Formula(op1, replace_Action((xa, mtcha), act1),
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Action_Formula(_, _, _) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Agent(_) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Agent_Formula(_, _, _) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Atprop(_) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Bin(_, _, _) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Freevar(_) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Precondition(_) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
            case Formula_Zer(_) =>
              Formula_Action_Formula(op1, act1,
                                      replace_Formula_aux(x, mtch, form1))
          })
       case Formula_Action_Formula(_, _, _) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Agent(_) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Agent_Formula(_, _, _) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Atprop(_) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Bin(_, _, _) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Freevar(_) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Precondition(_) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Zer(_) =>
         Formula_Action_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
     })
  case (x, mtch, Formula_Agent_Formula(op1, act1, form1)) =>
    (x match {
       case Formula_Action(_) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Action_Formula(_, _, _) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Agent(xa) =>
         (mtch match {
            case Formula_Action(_) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Action_Formula(_, _, _) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Agent(mtcha) =>
              Formula_Agent_Formula(op1, replace_Agent((xa, mtcha), act1),
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Agent_Formula(_, _, _) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Atprop(_) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Bin(_, _, _) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Freevar(_) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Precondition(_) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
            case Formula_Zer(_) =>
              Formula_Agent_Formula(op1, act1,
                                     replace_Formula_aux(x, mtch, form1))
          })
       case Formula_Agent_Formula(_, _, _) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Atprop(_) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Bin(_, _, _) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Freevar(_) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Precondition(_) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
       case Formula_Zer(_) =>
         Formula_Agent_Formula(op1, act1, replace_Formula_aux(x, mtch, form1))
     })
  case (x, mtch, Formula_Precondition(act1)) =>
    (x match {
       case Formula_Action(xa) =>
         (mtch match {
            case Formula_Action(mtcha) =>
              Formula_Precondition(replace_Action((xa, mtcha), act1))
            case Formula_Action_Formula(_, _, _) => Formula_Precondition(act1)
            case Formula_Agent(_) => Formula_Precondition(act1)
            case Formula_Agent_Formula(_, _, _) => Formula_Precondition(act1)
            case Formula_Atprop(_) => Formula_Precondition(act1)
            case Formula_Bin(_, _, _) => Formula_Precondition(act1)
            case Formula_Freevar(_) => Formula_Precondition(act1)
            case Formula_Precondition(_) => Formula_Precondition(act1)
            case Formula_Zer(_) => Formula_Precondition(act1)
          })
       case Formula_Action_Formula(_, _, _) => Formula_Precondition(act1)
       case Formula_Agent(_) => Formula_Precondition(act1)
       case Formula_Agent_Formula(_, _, _) => Formula_Precondition(act1)
       case Formula_Atprop(_) => Formula_Precondition(act1)
       case Formula_Bin(_, _, _) => Formula_Precondition(act1)
       case Formula_Freevar(_) => Formula_Precondition(act1)
       case Formula_Precondition(_) => Formula_Precondition(act1)
       case Formula_Zer(_) => Formula_Precondition(act1)
     })
  case (x, mtch, Formula_Zer(z)) => Formula_Zer(z)
  case (x, mtch, Formula_Agent(z)) => Formula_Agent(z)
  case (x, mtch, Formula_Action(z)) => Formula_Action(z)
}

def replace_Formula(x0: (Formula, Formula), c: Formula): Formula = (x0, c) match
  {
  case ((a, b), c) => replace_Formula_aux(a, b, c)
}

def replace_Structure_list_aux(x: Structure, mtch: Structure,
                                xa2: List[Structure]):
      List[Structure]
  =
  (x, mtch, xa2) match {
  case (x, mtch, Nil) => Nil
  case (x, mtch, l :: ist) =>
    replace_Structure_aux(x, mtch, l) ::
      replace_Structure_list_aux(x, mtch, ist)
}

def replace_Structure_aux(x: Structure, mtch: Structure, xa2: Structure):
      Structure
  =
  (x, mtch, xa2) match {
  case (x, mtch, Structure_Formula(f)) =>
    (x match {
       case Structure_Action_Structure(_, _, _) => Structure_Formula(f)
       case Structure_Agent_Structure(_, _, _) => Structure_Formula(f)
       case Structure_Bigcomma(_) => Structure_Formula(f)
       case Structure_Bin(_, _, _) => Structure_Formula(f)
       case Structure_Formula(xf) =>
         (mtch match {
            case Structure_Action_Structure(_, _, _) => Structure_Formula(f)
            case Structure_Agent_Structure(_, _, _) => Structure_Formula(f)
            case Structure_Bigcomma(_) => Structure_Formula(f)
            case Structure_Bin(_, _, _) => Structure_Formula(f)
            case Structure_Formula(mtchf) =>
              Structure_Formula(replace_Formula((xf, mtchf), f))
            case Structure_Freevar(_) => Structure_Formula(f)
            case Structure_Phi(_) => Structure_Formula(f)
            case Structure_Zer(_) => Structure_Formula(f)
          })
       case Structure_Freevar(_) => Structure_Formula(f)
       case Structure_Phi(_) => Structure_Formula(f)
       case Structure_Zer(_) => Structure_Formula(f)
     })
  case (x, mtch, Structure_Bin(var1, op1, var2)) =>
    Structure_Bin(replace_Structure_aux(x, mtch, var1), op1,
                   replace_Structure_aux(x, mtch, var2))
  case (x, mtch, Structure_Freevar(free)) =>
    (if (equal_Structurea(x, Structure_Freevar(free))) mtch
      else Structure_Freevar(free))
  case (x, mtch, Structure_Action_Structure(op1, act1, form1)) =>
    (x match {
       case Structure_Action_Structure(_, _, _) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Agent_Structure(_, _, _) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Bigcomma(_) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Bin(_, _, _) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Action(xa)) =>
         (mtch match {
            case Structure_Action_Structure(_, _, _) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Agent_Structure(_, _, _) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Bigcomma(_) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Bin(_, _, _) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Action(mtcha)) =>
              Structure_Action_Structure(op1, replace_Action((xa, mtcha), act1),
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Action_Formula(_, _, _)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Agent(_)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Agent_Formula(_, _, _)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Atprop(_)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Bin(_, _, _)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Freevar(_)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Precondition(_)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Zer(_)) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Freevar(_) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Phi(_) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
            case Structure_Zer(_) =>
              Structure_Action_Structure(op1, act1,
  replace_Structure_aux(x, mtch, form1))
          })
       case Structure_Formula(Formula_Action_Formula(_, _, _)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Agent(_)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Agent_Formula(_, _, _)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Atprop(_)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Bin(_, _, _)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Freevar(_)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Precondition(_)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Zer(_)) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Freevar(_) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Phi(_) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
       case Structure_Zer(_) =>
         Structure_Action_Structure(op1, act1,
                                     replace_Structure_aux(x, mtch, form1))
     })
  case (x, mtch, Structure_Agent_Structure(op1, act1, form1)) =>
    (x match {
       case Structure_Action_Structure(_, _, _) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Agent_Structure(_, _, _) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Bigcomma(_) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Bin(_, _, _) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Action(_)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Action_Formula(_, _, _)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Agent(xa)) =>
         (mtch match {
            case Structure_Action_Structure(_, _, _) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Agent_Structure(_, _, _) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Bigcomma(_) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Bin(_, _, _) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Action(_)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Action_Formula(_, _, _)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Agent(mtcha)) =>
              Structure_Agent_Structure(op1, replace_Agent((xa, mtcha), act1),
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Agent_Formula(_, _, _)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Atprop(_)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Bin(_, _, _)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Freevar(_)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Precondition(_)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Formula(Formula_Zer(_)) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Freevar(_) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Phi(_) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
            case Structure_Zer(_) =>
              Structure_Agent_Structure(op1, act1,
 replace_Structure_aux(x, mtch, form1))
          })
       case Structure_Formula(Formula_Agent_Formula(_, _, _)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Atprop(_)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Bin(_, _, _)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Freevar(_)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Precondition(_)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Formula(Formula_Zer(_)) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Freevar(_) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Phi(_) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
       case Structure_Zer(_) =>
         Structure_Agent_Structure(op1, act1,
                                    replace_Structure_aux(x, mtch, form1))
     })
  case (x, mtch, Structure_Phi(act1)) =>
    (x match {
       case Structure_Action_Structure(_, _, _) => Structure_Phi(act1)
       case Structure_Agent_Structure(_, _, _) => Structure_Phi(act1)
       case Structure_Bigcomma(_) => Structure_Phi(act1)
       case Structure_Bin(_, _, _) => Structure_Phi(act1)
       case Structure_Formula(Formula_Action(xa)) =>
         (mtch match {
            case Structure_Action_Structure(_, _, _) => Structure_Phi(act1)
            case Structure_Agent_Structure(_, _, _) => Structure_Phi(act1)
            case Structure_Bigcomma(_) => Structure_Phi(act1)
            case Structure_Bin(_, _, _) => Structure_Phi(act1)
            case Structure_Formula(Formula_Action(mtcha)) =>
              Structure_Phi(replace_Action((xa, mtcha), act1))
            case Structure_Formula(Formula_Action_Formula(_, _, _)) =>
              Structure_Phi(act1)
            case Structure_Formula(Formula_Agent(_)) => Structure_Phi(act1)
            case Structure_Formula(Formula_Agent_Formula(_, _, _)) =>
              Structure_Phi(act1)
            case Structure_Formula(Formula_Atprop(_)) => Structure_Phi(act1)
            case Structure_Formula(Formula_Bin(_, _, _)) => Structure_Phi(act1)
            case Structure_Formula(Formula_Freevar(_)) => Structure_Phi(act1)
            case Structure_Formula(Formula_Precondition(_)) =>
              Structure_Phi(act1)
            case Structure_Formula(Formula_Zer(_)) => Structure_Phi(act1)
            case Structure_Freevar(_) => Structure_Phi(act1)
            case Structure_Phi(_) => Structure_Phi(act1)
            case Structure_Zer(_) => Structure_Phi(act1)
          })
       case Structure_Formula(Formula_Action_Formula(_, _, _)) =>
         Structure_Phi(act1)
       case Structure_Formula(Formula_Agent(_)) => Structure_Phi(act1)
       case Structure_Formula(Formula_Agent_Formula(_, _, _)) =>
         Structure_Phi(act1)
       case Structure_Formula(Formula_Atprop(_)) => Structure_Phi(act1)
       case Structure_Formula(Formula_Bin(_, _, _)) => Structure_Phi(act1)
       case Structure_Formula(Formula_Freevar(_)) => Structure_Phi(act1)
       case Structure_Formula(Formula_Precondition(_)) => Structure_Phi(act1)
       case Structure_Formula(Formula_Zer(_)) => Structure_Phi(act1)
       case Structure_Freevar(_) => Structure_Phi(act1)
       case Structure_Phi(_) => Structure_Phi(act1)
       case Structure_Zer(_) => Structure_Phi(act1)
     })
  case (x, mtch, Structure_Zer(z)) => Structure_Zer(z)
  case (x, mtch, Structure_Bigcomma(list)) =>
    Structure_Bigcomma(replace_Structure_list_aux(x, mtch, list))
}

def replace_Structure(x0: (Structure, Structure), c: Structure): Structure =
  (x0, c) match {
  case ((a, b), c) => replace_Structure_aux(a, b, c)
}

def replace_Sequent(x0: (Sequent, Sequent), y: Sequent): Sequent = (x0, y) match
  {
  case ((Sequent_Structure(x), Sequent_Structure(rep)), Sequenta(var1, var2)) =>
    Sequenta(replace_Structure((x, rep), var1),
              replace_Structure((x, rep), var2))
  case ((Sequenta(v, va), uv), y) => y
  case ((uu, Sequenta(v, va)), y) => y
  case ((uu, uv), Sequent_Structure(v)) => Sequent_Structure(v)
}

def match_Atprop(xa0: Atprop, x: Atprop): List[(Atprop, Atprop)] = (xa0, x)
  match {
  case (Atprop_Freevar(free), x) => List((Atprop_Freevar(free), x))
  case (Atpropa(uu), uv) => Nil
}

def match_Action(x0: Action, mtch: Action): List[(Action, Action)] = (x0, mtch)
  match {
  case (Action_Freevar(free), mtch) => List((Action_Freevar(free), mtch))
  case (Actiona(v), uv) => Nil
}

def match_Agent(x0: Agent, mtch: Agent): List[(Agent, Agent)] = (x0, mtch) match
  {
  case (Agent_Freevar(free), mtch) => List((Agent_Freevar(free), mtch))
  case (Agenta(v), uv) => Nil
}

def fsta[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def snda[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def list_ex[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def m_clash[A : equal, B : equal](x: (A, B), y: List[(A, B)]): Boolean =
  list_ex[(A, B)]((a: (A, B)) =>
                    eq[A](fsta[A, B](a), fsta[A, B](x)) &&
                      ! (eq[B](snda[A, B](a), snda[A, B](x))),
                   y)

def merge[A : equal, B : equal](x0: List[(A, B)], y: List[(A, B)]): List[(A, B)]
  =
  (x0, y) match {
  case (Nil, y) => y
  case (x :: xs, y) =>
    (if (m_clash[A, B](x, y))
      merge[A, B](filter[(A, B)]((a: (A, B)) =>
                                   ! (eq[A](fsta[A, B](a), fsta[A, B](x))),
                                  xs),
                   filter[(A, B)]((a: (A, B)) =>
                                    ! (eq[A](fsta[A, B](a), fsta[A, B](x))),
                                   y))
      else x :: merge[A, B](xs, y))
}

def match_Formula(xa0: Formula, x: Formula): List[(Formula, Formula)] = (xa0, x)
  match {
  case (Formula_Atprop(rule), x) =>
    (x match {
       case Formula_Action(_) => Nil
       case Formula_Action_Formula(_, _, _) => Nil
       case Formula_Agent(_) => Nil
       case Formula_Agent_Formula(_, _, _) => Nil
       case Formula_Atprop(m) =>
         map[(Atprop, Atprop),
              (Formula,
                Formula)]((a: (Atprop, Atprop)) =>
                            {
                              val (xa, y): (Atprop, Atprop) = a;
                              (Formula_Atprop(xa), Formula_Atprop(y))
                            },
                           match_Atprop(rule, m))
       case Formula_Bin(_, _, _) => Nil
       case Formula_Freevar(_) => Nil
       case Formula_Precondition(_) => Nil
       case Formula_Zer(_) => Nil
     })
  case (Formula_Bin(var11, op1, var12), x) =>
    (x match {
       case Formula_Action(_) => Nil
       case Formula_Action_Formula(_, _, _) => Nil
       case Formula_Agent(_) => Nil
       case Formula_Agent_Formula(_, _, _) => Nil
       case Formula_Atprop(_) => Nil
       case Formula_Bin(var21, op2, var22) =>
         (if (equal_Formula_Bin_Op(op1, op2))
           merge[Formula,
                  Formula](match_Formula(var11, var21),
                            match_Formula(var12, var22))
           else Nil)
       case Formula_Freevar(_) => Nil
       case Formula_Precondition(_) => Nil
       case Formula_Zer(_) => Nil
     })
  case (Formula_Freevar(free), x) => List((Formula_Freevar(free), x))
  case (Formula_Action_Formula(op1, act1, form1), x) =>
    (x match {
       case Formula_Action(_) => Nil
       case Formula_Action_Formula(op2, act2, form2) =>
         (if (equal_Formula_Action_Formula_Op(op1, op2))
           merge[Formula,
                  Formula](map[(Action, Action),
                                (Formula,
                                  Formula)]((a: (Action, Action)) =>
      {
        val (xa, y): (Action, Action) = a;
        (Formula_Action(xa), Formula_Action(y))
      },
     match_Action(act1, act2)),
                            match_Formula(form1, form2))
           else Nil)
       case Formula_Agent(_) => Nil
       case Formula_Agent_Formula(_, _, _) => Nil
       case Formula_Atprop(_) => Nil
       case Formula_Bin(_, _, _) => Nil
       case Formula_Freevar(_) => Nil
       case Formula_Precondition(_) => Nil
       case Formula_Zer(_) => Nil
     })
  case (Formula_Agent_Formula(op1, act1, form1), x) =>
    (x match {
       case Formula_Action(_) => Nil
       case Formula_Action_Formula(_, _, _) => Nil
       case Formula_Agent(_) => Nil
       case Formula_Agent_Formula(op2, act2, form2) =>
         (if (equal_Formula_Agent_Formula_Op(op1, op2))
           merge[Formula,
                  Formula](map[(Agent, Agent),
                                (Formula,
                                  Formula)]((a: (Agent, Agent)) =>
      {
        val (xa, y): (Agent, Agent) = a;
        (Formula_Agent(xa), Formula_Agent(y))
      },
     match_Agent(act1, act2)),
                            match_Formula(form1, form2))
           else Nil)
       case Formula_Atprop(_) => Nil
       case Formula_Bin(_, _, _) => Nil
       case Formula_Freevar(_) => Nil
       case Formula_Precondition(_) => Nil
       case Formula_Zer(_) => Nil
     })
  case (Formula_Precondition(act1), x) =>
    (x match {
       case Formula_Action(_) => Nil
       case Formula_Action_Formula(_, _, _) => Nil
       case Formula_Agent(_) => Nil
       case Formula_Agent_Formula(_, _, _) => Nil
       case Formula_Atprop(_) => Nil
       case Formula_Bin(_, _, _) => Nil
       case Formula_Freevar(_) => Nil
       case Formula_Precondition(act2) =>
         map[(Action, Action),
              (Formula,
                Formula)]((a: (Action, Action)) =>
                            {
                              val (xa, y): (Action, Action) = a;
                              (Formula_Action(xa), Formula_Action(y))
                            },
                           match_Action(act1, act2))
       case Formula_Zer(_) => Nil
     })
  case (Formula_Zer(z), x) => Nil
  case (Formula_Agent(z), x) => Nil
  case (Formula_Action(z), x) => Nil
}

def match_Structure(xa0: Structure, x: Structure): List[(Structure, Structure)]
  =
  (xa0, x) match {
  case (Structure_Formula(rule), x) =>
    (x match {
       case Structure_Action_Structure(_, _, _) => Nil
       case Structure_Agent_Structure(_, _, _) => Nil
       case Structure_Bigcomma(_) => Nil
       case Structure_Bin(_, _, _) => Nil
       case Structure_Formula(form) =>
         map[(Formula, Formula),
              (Structure,
                Structure)]((a: (Formula, Formula)) =>
                              {
                                val (xa, y): (Formula, Formula) = a;
                                (Structure_Formula(xa), Structure_Formula(y))
                              },
                             match_Formula(rule, form))
       case Structure_Freevar(_) => Nil
       case Structure_Phi(_) => Nil
       case Structure_Zer(_) => Nil
     })
  case (Structure_Bin(var11, op1, var12), x) =>
    (x match {
       case Structure_Action_Structure(_, _, _) => Nil
       case Structure_Agent_Structure(_, _, _) => Nil
       case Structure_Bigcomma(_) => Nil
       case Structure_Bin(var21, op2, var22) =>
         (if (equal_Structure_Bin_Op(op1, op2))
           merge[Structure,
                  Structure](match_Structure(var11, var21),
                              match_Structure(var12, var22))
           else Nil)
       case Structure_Formula(_) => Nil
       case Structure_Freevar(_) => Nil
       case Structure_Phi(_) => Nil
       case Structure_Zer(_) => Nil
     })
  case (Structure_Freevar(free), x) => List((Structure_Freevar(free), x))
  case (Structure_Action_Structure(op1, act1, struct1), x) =>
    (x match {
       case Structure_Action_Structure(op2, act2, struct2) =>
         (if (equal_Structure_Action_Structure_Op(op1, op2))
           merge[Structure,
                  Structure](map[(Action, Action),
                                  (Structure,
                                    Structure)]((a: (Action, Action)) =>
          {
            val (xa, y): (Action, Action) = a;
            (Structure_Formula(Formula_Action(xa)),
              Structure_Formula(Formula_Action(y)))
          },
         match_Action(act1, act2)),
                              match_Structure(struct1, struct2))
           else Nil)
       case Structure_Agent_Structure(_, _, _) => Nil
       case Structure_Bigcomma(_) => Nil
       case Structure_Bin(_, _, _) => Nil
       case Structure_Formula(_) => Nil
       case Structure_Freevar(_) => Nil
       case Structure_Phi(_) => Nil
       case Structure_Zer(_) => Nil
     })
  case (Structure_Agent_Structure(op1, act1, struct1), x) =>
    (x match {
       case Structure_Action_Structure(_, _, _) => Nil
       case Structure_Agent_Structure(op2, act2, struct2) =>
         (if (equal_Structure_Agent_Structure_Op(op1, op2))
           merge[Structure,
                  Structure](map[(Agent, Agent),
                                  (Structure,
                                    Structure)]((a: (Agent, Agent)) =>
          {
            val (xa, y): (Agent, Agent) = a;
            (Structure_Formula(Formula_Agent(xa)),
              Structure_Formula(Formula_Agent(y)))
          },
         match_Agent(act1, act2)),
                              match_Structure(struct1, struct2))
           else Nil)
       case Structure_Bigcomma(_) => Nil
       case Structure_Bin(_, _, _) => Nil
       case Structure_Formula(_) => Nil
       case Structure_Freevar(_) => Nil
       case Structure_Phi(_) => Nil
       case Structure_Zer(_) => Nil
     })
  case (Structure_Phi(act1), x) =>
    (x match {
       case Structure_Action_Structure(_, _, _) => Nil
       case Structure_Agent_Structure(_, _, _) => Nil
       case Structure_Bigcomma(_) => Nil
       case Structure_Bin(_, _, _) => Nil
       case Structure_Formula(_) => Nil
       case Structure_Freevar(_) => Nil
       case Structure_Phi(act2) =>
         map[(Action, Action),
              (Structure,
                Structure)]((a: (Action, Action)) =>
                              {
                                val (xa, y): (Action, Action) = a;
                                (Structure_Formula(Formula_Action(xa)),
                                  Structure_Formula(Formula_Action(y)))
                              },
                             match_Action(act1, act2))
       case Structure_Zer(_) => Nil
     })
  case (Structure_Zer(uu), x) => Nil
  case (Structure_Bigcomma(list), x) => Nil
}

def match_Sequent(uu: Sequent, uv: Sequent): List[(Sequent, Sequent)] = (uu, uv)
  match {
  case (Sequenta(var11, var12), Sequenta(var21, var22)) =>
    map[(Structure, Structure),
         (Sequent,
           Sequent)]((a: (Structure, Structure)) =>
                       {
                         val (x, y): (Structure, Structure) = a;
                         (Sequent_Structure(x), Sequent_Structure(y))
                       },
                      merge[Structure,
                             Structure](match_Structure(var11, var21),
 match_Structure(var12, var22)))
  case (Sequent_Structure(v), uv) => Nil
  case (uu, Sequent_Structure(v)) => Nil
}

trait Varmatch[A] {
  val `DEAK.matcha`: (A, A) => List[(A, A)]
  val `DEAK.freevars`: A => set[A]
  val `DEAK.replace`: ((A, A), A) => A
}
def matcha[A](a: A, b: A)(implicit A: Varmatch[A]): List[(A, A)] =
  A.`DEAK.matcha`(a, b)
def freevars[A](a: A)(implicit A: Varmatch[A]): set[A] = A.`DEAK.freevars`(a)
def replace[A](a: (A, A), b: A)(implicit A: Varmatch[A]): A =
  A.`DEAK.replace`(a, b)

implicit def Varmatch_Sequent: Varmatch[Sequent] = new Varmatch[Sequent] {
  val `DEAK.matcha` = (a: Sequent, b: Sequent) => match_Sequent(a, b)
  val `DEAK.freevars` = (a: Sequent) => freevars_Sequent(a)
  val `DEAK.replace` = (a: (Sequent, Sequent), b: Sequent) =>
    replace_Sequent(a, b)
}

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

implicit def equal_prod[A : equal, B : equal]: equal[(A, B)] = new equal[(A, B)]
  {
  val `DEAK.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

abstract sealed class Locale
final case class CutFormula(a: Formula) extends Locale
final case class Premise(a: Sequent) extends Locale
final case class Part(a: Structure) extends Locale
final case class RelAKA(a: Action => Agent => List[Action]) extends Locale
final case class PreFormula(a: Action, b: Formula) extends Locale
final case class LAgent(a: Agent) extends Locale
final case class Empty() extends Locale

abstract sealed class ruleder
final case class ruledera(a: Sequent, b: Sequent => Option[List[Sequent]])
  extends ruleder
final case class
  ruleder_cond(a: Sequent => Boolean, b: Sequent,
                c: Sequent => Option[List[Sequent]])
  extends ruleder

abstract sealed class polarity
final case class Plus() extends polarity
final case class Minus() extends polarity
final case class N() extends polarity

abstract sealed class multiset[A]
final case class multiset_of[A](a: List[A]) extends multiset[A]

def ant(x0: Sequent): Structure = x0 match {
  case Sequenta(x, y) => x
  case Sequent_Structure(x) => x
}

def replaceAll[A : Varmatch](x0: List[(A, A)], mtch: A): A = (x0, mtch) match {
  case (Nil, mtch) => mtch
  case (x :: xs, mtch) => replaceAll[A](xs, replace[A](x, mtch))
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def is_empty[A](x0: set[A]): Boolean = x0 match {
  case seta(xs) => nulla[A](xs)
}

def ruleMatch[A : Varmatch : equal](r: A, m: A): Boolean =
  (if (is_empty[A](freevars[A](m))) eq[A](replaceAll[A](matcha[A](r, m), r), m)
    else false)

def ruleRuleStructAct(x: Locale, xa1: RuleStructAct): ruleder = (x, xa1) match {
  case (x, A_nec_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_BackA(),
          Action_Freevar(List('a')), Structure_Zer(Structure_Neutral())),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('X'))))))
  case (x, A_mon_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_BackA(),
          Action_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                         Structure_Freevar(List('Y')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Action_Structure(Structure_BackA(),
            Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                         Structure_Comma(),
                         Structure_Action_Structure(Structure_BackA(),
             Action_Freevar(List('a')), Structure_Freevar(List('Y')))),
           Structure_Freevar(List('Z'))))))
  case (x, Mon_A_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                          Structure_Freevar(List('Y'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Action_Structure(Structure_ForwA(),
             Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                          Structure_Comma(),
                          Structure_Action_Structure(Structure_ForwA(),
              Action_Freevar(List('a')), Structure_Freevar(List('Y'))))))))
  case (x, Nec_A_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a')), Structure_Zer(Structure_Neutral())),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('X'))))))
  case (x, FS_A_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                         Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Action_Structure(Structure_ForwA(),
            Action_Freevar(List('a')), Structure_Freevar(List('Y'))),
                         Structure_ImpR(),
                         Structure_Action_Structure(Structure_ForwA(),
             Action_Freevar(List('a')), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('X'))))))
  case (x, FS_A_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a')),
           Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                          Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Action_Structure(Structure_ForwA(),
             Action_Freevar(List('a')), Structure_Freevar(List('Y'))),
                          Structure_ImpR(),
                          Structure_Action_Structure(Structure_ForwA(),
              Action_Freevar(List('a')), Structure_Freevar(List('Z'))))))))
  case (x, A_mon_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Action_Structure(Structure_BackA(),
           Action_Freevar(List('a')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                          Structure_Freevar(List('Y'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Action_Structure(Structure_BackA(),
             Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                          Structure_Comma(),
                          Structure_Action_Structure(Structure_BackA(),
              Action_Freevar(List('a')), Structure_Freevar(List('Y'))))))))
  case (x, A_FS_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Action_Structure(Structure_BackA(),
           Action_Freevar(List('a')),
           Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                          Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Action_Structure(Structure_BackA(),
             Action_Freevar(List('a')), Structure_Freevar(List('Y'))),
                          Structure_ImpR(),
                          Structure_Action_Structure(Structure_BackA(),
              Action_Freevar(List('a')), Structure_Freevar(List('Z'))))))))
  case (x, Nec_A_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a')), Structure_Zer(Structure_Neutral()))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Zer(Structure_Neutral())))))
  case (x, Mon_A_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                         Structure_Freevar(List('Y')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Action_Structure(Structure_ForwA(),
            Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                         Structure_Comma(),
                         Structure_Action_Structure(Structure_ForwA(),
             Action_Freevar(List('a')), Structure_Freevar(List('Y')))),
           Structure_Freevar(List('Z'))))))
  case (x, A_FS_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_BackA(),
          Action_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                         Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Action_Structure(Structure_BackA(),
            Action_Freevar(List('a')), Structure_Freevar(List('Y'))),
                         Structure_ImpR(),
                         Structure_Action_Structure(Structure_BackA(),
             Action_Freevar(List('a')), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('X'))))))
  case (x, A_nec_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Action_Structure(Structure_BackA(),
           Action_Freevar(List('a')), Structure_Zer(Structure_Neutral()))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Zer(Structure_Neutral())))))
}

def ruleRuleKnowledge(x: Locale, xa1: RuleKnowledge): ruleder = (x, xa1) match {
  case (x, Refl_ForwK()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(a) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) =>
                     Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
                Structure_Agent_Structure(Structure_ForwK(), a,
   Structure_Freevar(List('Y')))))))
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
}

def ruleRuleStructEA(x: Locale, xa1: RuleStructEA): ruleder = (x, xa1) match {
  case (x, Reduce_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a')), Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
           Structure_Bin(Structure_Phi(Action_Freevar(List('a'))),
                          Structure_ImpR(),
                          Structure_Action_Structure(Structure_ForwA(),
              Action_Freevar(List('a')), Structure_Freevar(List('X'))))))))
  case (x, CompA_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')),
                       Structure_Bin(Structure_Phi(Action_Freevar(List('a'))),
                                      Structure_ImpR(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
           Structure_Action_Structure(Structure_ForwA(),
                                       Action_Freevar(List('a')),
                                       Structure_Action_Structure(Structure_BackA(),
                           Action_Freevar(List('a')),
                           Structure_Freevar(List('X'))))))))
  case (x, Balance()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a')), Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, CompA_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Phi(Action_Freevar(List('a'))),
                                     Structure_Comma(),
                                     Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Action_Structure(Structure_ForwA(),
                                      Action_Freevar(List('a')),
                                      Structure_Action_Structure(Structure_BackA(),
                          Action_Freevar(List('a')),
                          Structure_Freevar(List('X')))),
           Structure_Freevar(List('Y'))))))
  case (x, Reduce_L()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Phi(Action_Freevar(List('a'))),
                         Structure_Comma(),
                         Structure_Action_Structure(Structure_ForwA(),
             Action_Freevar(List('a')), Structure_Freevar(List('X')))),
           Structure_Freevar(List('Y'))))))
}

def bigcomma_cons_R2(x0: Sequent): Option[List[Sequent]] = x0 match {
  case Sequenta(y, Structure_Bigcomma(x :: xs)) =>
    Some[List[Sequent]](List(Sequenta(y, Structure_Bin(x, Structure_Comma(),
                Structure_Bigcomma(xs)))))
  case Sequenta(v, Structure_Action_Structure(vb, vc, vd)) => None
  case Sequenta(v, Structure_Agent_Structure(vb, vc, vd)) => None
  case Sequenta(v, Structure_Bigcomma(Nil)) => None
  case Sequenta(v, Structure_Bin(vb, vc, vd)) => None
  case Sequenta(v, Structure_Formula(vb)) => None
  case Sequenta(v, Structure_Freevar(vb)) => None
  case Sequenta(v, Structure_Phi(vb)) => None
  case Sequenta(v, Structure_Zer(vb)) => None
  case Sequent_Structure(v) => None
}

def bigcomma_cons_L2(x0: Sequent): Option[List[Sequent]] = x0 match {
  case Sequenta(Structure_Bigcomma(x :: xs), y) =>
    Some[List[Sequent]](List(Sequenta(Structure_Bin(x, Structure_Comma(),
             Structure_Bigcomma(xs)),
                                       y)))
  case Sequenta(Structure_Action_Structure(vb, vc, vd), va) => None
  case Sequenta(Structure_Agent_Structure(vb, vc, vd), va) => None
  case Sequenta(Structure_Bigcomma(Nil), va) => None
  case Sequenta(Structure_Bin(vb, vc, vd), va) => None
  case Sequenta(Structure_Formula(vb), va) => None
  case Sequenta(Structure_Freevar(vb), va) => None
  case Sequenta(Structure_Phi(vb), va) => None
  case Sequenta(Structure_Zer(vb), va) => None
  case Sequent_Structure(v) => None
}

def bigcomma_cons_R(x0: Sequent): Option[List[Sequent]] = x0 match {
  case Sequenta(y, Structure_Bin(x, Structure_Comma(), Structure_Bigcomma(xs)))
    => Some[List[Sequent]](List(Sequenta(y, Structure_Bigcomma(x :: xs))))
  case Sequenta(v, Structure_Action_Structure(vb, vc, vd)) => None
  case Sequenta(v, Structure_Agent_Structure(vb, vc, vd)) => None
  case Sequenta(v, Structure_Bigcomma(vb)) => None
  case Sequenta(v, Structure_Bin(vb, Structure_ImpL(), vd)) => None
  case Sequenta(v, Structure_Bin(vb, Structure_ImpR(), vd)) => None
  case Sequenta(v, Structure_Bin(vb, vc,
                                  Structure_Action_Structure(ve, vf, vg)))
    => None
  case Sequenta(v, Structure_Bin(vb, vc, Structure_Agent_Structure(ve, vf, vg)))
    => None
  case Sequenta(v, Structure_Bin(vb, vc, Structure_Bin(ve, vf, vg))) => None
  case Sequenta(v, Structure_Bin(vb, vc, Structure_Formula(ve))) => None
  case Sequenta(v, Structure_Bin(vb, vc, Structure_Freevar(ve))) => None
  case Sequenta(v, Structure_Bin(vb, vc, Structure_Phi(ve))) => None
  case Sequenta(v, Structure_Bin(vb, vc, Structure_Zer(ve))) => None
  case Sequenta(v, Structure_Formula(vb)) => None
  case Sequenta(v, Structure_Freevar(vb)) => None
  case Sequenta(v, Structure_Phi(vb)) => None
  case Sequenta(v, Structure_Zer(vb)) => None
  case Sequent_Structure(v) => None
}

def bigcomma_cons_L(x0: Sequent): Option[List[Sequent]] = x0 match {
  case Sequenta(Structure_Bin(x, Structure_Comma(), Structure_Bigcomma(xs)), y)
    => Some[List[Sequent]](List(Sequenta(Structure_Bigcomma(x :: xs), y)))
  case Sequenta(Structure_Action_Structure(vb, vc, vd), va) => None
  case Sequenta(Structure_Agent_Structure(vb, vc, vd), va) => None
  case Sequenta(Structure_Bigcomma(vb), va) => None
  case Sequenta(Structure_Bin(vb, Structure_ImpL(), vd), va) => None
  case Sequenta(Structure_Bin(vb, Structure_ImpR(), vd), va) => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Action_Structure(ve, vf, vg)),
                 va)
    => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Agent_Structure(ve, vf, vg)),
                 va)
    => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Bin(ve, vf, vg)), va) => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Formula(ve)), va) => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Freevar(ve)), va) => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Phi(ve)), va) => None
  case Sequenta(Structure_Bin(vb, vc, Structure_Zer(ve)), va) => None
  case Sequenta(Structure_Formula(vb), va) => None
  case Sequenta(Structure_Freevar(vb), va) => None
  case Sequenta(Structure_Phi(vb), va) => None
  case Sequenta(Structure_Zer(vb), va) => None
  case Sequent_Structure(v) => None
}

def ruleRuleBigcomma(x: Locale, xa1: RuleBigcomma): ruleder = (x, xa1) match {
  case (x, Bigcomma_Nil_R2()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')), Structure_Bigcomma(Nil)),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
           Structure_Zer(Structure_Neutral())))))
  case (x, Bigcomma_Nil_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')),
                       Structure_Zer(Structure_Neutral())),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
           Structure_Bigcomma(Nil)))))
  case (x, Bigcomma_Nil_L2()) =>
    ruledera(Sequenta(Structure_Bigcomma(Nil), Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('Y'))))))
  case (x, Bigcomma_Nil_L()) =>
    ruledera(Sequenta(Structure_Zer(Structure_Neutral()),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bigcomma(Nil),
           Structure_Freevar(List('Y'))))))
  case (x, Bigcomma_Cons_R2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (a: Sequent) => bigcomma_cons_R2(a))
  case (x, Bigcomma_Cons_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (a: Sequent) => bigcomma_cons_R(a))
  case (x, Bigcomma_Cons_L2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (a: Sequent) => bigcomma_cons_L2(a))
  case (x, Bigcomma_Cons_L()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (a: Sequent) => bigcomma_cons_L(a))
}

def find[A](uu: A => Boolean, x1: List[A]): Option[A] = (uu, x1) match {
  case (uu, Nil) => None
  case (p, x :: xs) => (if (p(x)) Some[A](x) else find[A](p, xs))
}

def relAKACheck(fun: Action => Agent => List[Action],
                 mlist: List[(Sequent, Sequent)]):
      Boolean
  =
  (find[(Sequent,
          Sequent)]((x: (Sequent, Sequent)) =>
                      equal_Sequenta(fsta[Sequent, Sequent](x),
                                      Sequent_Structure(Structure_Formula(Formula_Action(Action_Freevar(List('a',
                              'l', 'p', 'h', 'a')))))),
                     mlist)
     match {
     case None => false
     case Some((_, Sequenta(_, _))) => false
     case Some((_, Sequent_Structure(Structure_Action_Structure(_, _, _)))) =>
       false
     case Some((_, Sequent_Structure(Structure_Agent_Structure(_, _, _)))) =>
       false
     case Some((_, Sequent_Structure(Structure_Bigcomma(_)))) => false
     case Some((_, Sequent_Structure(Structure_Bin(_, _, _)))) => false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Action(alpha)))))
       => (find[(Sequent,
                  Sequent)]((x: (Sequent, Sequent)) =>
                              equal_Sequenta(fsta[Sequent, Sequent](x),
      Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar(List('a')))))),
                             mlist)
             match {
             case None => false
             case Some(a) =>
               {
                 val (_, aa): (Sequent, Sequent) = a;
                 (aa match {
                    case Sequenta(_, _) => false
                    case Sequent_Structure(ab) =>
                      (ab match {
                         case Structure_Action_Structure(_, _, _) => false
                         case Structure_Agent_Structure(_, _, _) => false
                         case Structure_Bigcomma(_) => false
                         case Structure_Bin(_, _, _) => false
                         case Structure_Formula(ac) =>
                           (ac match {
                              case Formula_Action(_) => false
                              case Formula_Action_Formula(_, _, _) => false
                              case Formula_Agent(ad) =>
                                (find[(Sequent,
Sequent)]((x: (Sequent, Sequent)) =>
            equal_Sequenta(fsta[Sequent, Sequent](x),
                            Sequent_Structure(Structure_Formula(Formula_Action(Action_Freevar(List('b',
                    'e', 't', 'a')))))),
           mlist)
                                   match {
                                   case None => false
                                   case Some((_, Sequenta(_, _))) => false
                                   case Some((_,
       Sequent_Structure(Structure_Action_Structure(_, _, _))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Agent_Structure(_, _, _))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Bigcomma(_))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Bin(_, _, _))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Action(beta)))))
                                     => (find[Action]((x: Action) =>
                equal_Actiona(x, beta),
               (fun(alpha))(ad))
   match {
   case None => false
   case Some(_) => true
 })
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Action_Formula(_, _, _)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Agent(_)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Agent_Formula(_, _, _)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Atprop(_)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Bin(_, _, _)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Freevar(_)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Precondition(_)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Formula(Formula_Zer(_)))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Freevar(_))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Phi(_))))
                                     => false
                                   case Some((_,
       Sequent_Structure(Structure_Zer(_))))
                                     => false
                                 })
                              case Formula_Agent_Formula(_, _, _) => false
                              case Formula_Atprop(_) => false
                              case Formula_Bin(_, _, _) => false
                              case Formula_Freevar(_) => false
                              case Formula_Precondition(_) => false
                              case Formula_Zer(_) => false
                            })
                         case Structure_Freevar(_) => false
                         case Structure_Phi(_) => false
                         case Structure_Zer(_) => false
                       })
                  })
               }
           })
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Action_Formula(_,
                                       _, _)))))
       => false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Agent(_))))) =>
       false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Agent_Formula(_,
                                      _, _)))))
       => false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Atprop(_))))) =>
       false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Bin(_, _, _)))))
       => false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Freevar(_))))) =>
       false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Precondition(_)))))
       => false
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Zer(_))))) =>
       false
     case Some((_, Sequent_Structure(Structure_Freevar(_)))) => false
     case Some((_, Sequent_Structure(Structure_Phi(_)))) => false
     case Some((_, Sequent_Structure(Structure_Zer(_)))) => false
   })

def union[A : equal]: (List[A]) => (List[A]) => List[A] =
  (a: List[A]) =>
    (b: List[A]) =>
      fold[A, List[A]]((aa: A) => (ba: List[A]) => inserta[A](aa, ba), a, b)

def swapout_R_aux(relAKA: Action => Agent => List[Action], uv: List[Action],
                   seq: Sequent, x3: Sequent):
      Option[List[Sequent]]
  =
  (relAKA, uv, seq, x3) match {
  case (relAKA, Nil, seq, Sequenta(Structure_Bigcomma(Nil), x)) =>
    Some[List[Sequent]](Nil)
  case (relAKA, b :: list, seq, Sequenta(Structure_Bigcomma(y :: ys), x)) =>
    (swapout_R_aux(relAKA, list, seq, Sequenta(Structure_Bigcomma(ys), x)) match
       {
       case None => None
       case Some(lista) =>
         (if (relAKACheck(relAKA,
                           union[(Sequent,
                                   Sequent)].apply(match_Sequent(seq,
                          replaceAll[Sequent](map[(Structure, Structure),
           (Sequent,
             Sequent)]((a: (Structure, Structure)) =>
                         {
                           val (xa, ya): (Structure, Structure) = a;
                           (Sequent_Structure(xa), Sequent_Structure(ya))
                         },
                        (Structure_Formula(Formula_Action(Action_Freevar(List('b',
                                       'e', 't', 'a')))),
                          Structure_Formula(Formula_Action(b))) ::
                          (Structure_Freevar(List('Y')), y) ::
                            match_Structure(Structure_Action_Structure(Structure_ForwA(),
                                Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                                Structure_Agent_Structure(Structure_ForwK(),
                   Agent_Freevar(List('a')), Structure_Freevar(List('X')))),
     x)),
       seq))).apply(map[(Structure, Structure),
                         (Sequent,
                           Sequent)]((a: (Structure, Structure)) =>
                                       {
 val (xa, ya): (Structure, Structure) = a;
 (Sequent_Structure(xa), Sequent_Structure(ya))
                                       },
                                      (Structure_Formula(Formula_Action(Action_Freevar(List('b',
             'e', 't', 'a')))),
Structure_Formula(Formula_Action(b))) ::
(Structure_Freevar(List('Y')), y) ::
  match_Structure(Structure_Action_Structure(Structure_ForwA(),
      Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
      Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                 Structure_Freevar(List('X')))),
                   x)))))
           Some[List[Sequent]](replaceAll[Sequent](map[(Structure, Structure),
                (Sequent,
                  Sequent)]((a: (Structure, Structure)) =>
                              {
                                val (xa, ya): (Structure, Structure) = a;
                                (Sequent_Structure(xa), Sequent_Structure(ya))
                              },
                             (Structure_Formula(Formula_Action(Action_Freevar(List('b',
    'e', 't', 'a')))),
                               Structure_Formula(Formula_Action(b))) ::
                               (Structure_Freevar(List('Y')), y) ::
                                 match_Structure(Structure_Action_Structure(Structure_ForwA(),
                                     Action_Freevar(List('a', 'l', 'p', 'h',
                  'a')),
                                     Structure_Agent_Structure(Structure_ForwK(),
                        Agent_Freevar(List('a')),
                        Structure_Freevar(List('X')))),
          x)),
            seq) ::
                                 lista)
           else None)
     })
  case (uu, v :: va, uw, Sequenta(Structure_Action_Structure(vd, ve, vf), vc))
    => None
  case (uu, v :: va, uw, Sequenta(Structure_Agent_Structure(vd, ve, vf), vc)) =>
    None
  case (uu, v :: va, uw, Sequenta(Structure_Bigcomma(Nil), vc)) => None
  case (uu, v :: va, uw, Sequenta(Structure_Bin(vd, ve, vf), vc)) => None
  case (uu, v :: va, uw, Sequenta(Structure_Formula(vd), vc)) => None
  case (uu, v :: va, uw, Sequenta(Structure_Freevar(vd), vc)) => None
  case (uu, v :: va, uw, Sequenta(Structure_Phi(vd), vc)) => None
  case (uu, v :: va, uw, Sequenta(Structure_Zer(vd), vc)) => None
  case (uu, v :: va, uw, Sequent_Structure(vb)) => None
  case (uu, uv, uw, Sequenta(Structure_Action_Structure(vb, vc, vd), va)) =>
    None
  case (uu, uv, uw, Sequenta(Structure_Agent_Structure(vb, vc, vd), va)) => None
  case (uu, Nil, uw, Sequenta(Structure_Bigcomma(vc :: vd), va)) => None
  case (uu, uv, uw, Sequenta(Structure_Bin(vb, vc, vd), va)) => None
  case (uu, uv, uw, Sequenta(Structure_Formula(vb), va)) => None
  case (uu, uv, uw, Sequenta(Structure_Freevar(vb), va)) => None
  case (uu, uv, uw, Sequenta(Structure_Phi(vb), va)) => None
  case (uu, uv, uw, Sequenta(Structure_Zer(vb), va)) => None
  case (uu, uv, uw, Sequent_Structure(v)) => None
}

def betaList(fun: Action => Agent => List[Action],
              mlist: List[(Sequent, Sequent)]):
      List[Action]
  =
  (find[(Sequent,
          Sequent)]((x: (Sequent, Sequent)) =>
                      equal_Sequenta(fsta[Sequent, Sequent](x),
                                      Sequent_Structure(Structure_Formula(Formula_Action(Action_Freevar(List('a',
                              'l', 'p', 'h', 'a')))))),
                     mlist)
     match {
     case None => Nil
     case Some((_, Sequenta(_, _))) => Nil
     case Some((_, Sequent_Structure(Structure_Action_Structure(_, _, _)))) =>
       Nil
     case Some((_, Sequent_Structure(Structure_Agent_Structure(_, _, _)))) =>
       Nil
     case Some((_, Sequent_Structure(Structure_Bigcomma(_)))) => Nil
     case Some((_, Sequent_Structure(Structure_Bin(_, _, _)))) => Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Action(alpha)))))
       => (find[(Sequent,
                  Sequent)]((x: (Sequent, Sequent)) =>
                              equal_Sequenta(fsta[Sequent, Sequent](x),
      Sequent_Structure(Structure_Formula(Formula_Agent(Agent_Freevar(List('a')))))),
                             mlist)
             match {
             case None => Nil
             case Some(a) =>
               {
                 val (_, aa): (Sequent, Sequent) = a;
                 (aa match {
                    case Sequenta(_, _) => Nil
                    case Sequent_Structure(ab) =>
                      (ab match {
                         case Structure_Action_Structure(_, _, _) => Nil
                         case Structure_Agent_Structure(_, _, _) => Nil
                         case Structure_Bigcomma(_) => Nil
                         case Structure_Bin(_, _, _) => Nil
                         case Structure_Formula(ac) =>
                           (ac match {
                              case Formula_Action(_) => Nil
                              case Formula_Action_Formula(_, _, _) => Nil
                              case Formula_Agent(ad) => (fun(alpha))(ad)
                              case Formula_Agent_Formula(_, _, _) => Nil
                              case Formula_Atprop(_) => Nil
                              case Formula_Bin(_, _, _) => Nil
                              case Formula_Freevar(_) => Nil
                              case Formula_Precondition(_) => Nil
                              case Formula_Zer(_) => Nil
                            })
                         case Structure_Freevar(_) => Nil
                         case Structure_Phi(_) => Nil
                         case Structure_Zer(_) => Nil
                       })
                  })
               }
           })
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Action_Formula(_,
                                       _, _)))))
       => Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Agent(_))))) =>
       Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Agent_Formula(_,
                                      _, _)))))
       => Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Atprop(_))))) =>
       Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Bin(_, _, _)))))
       => Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Freevar(_))))) =>
       Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Precondition(_)))))
       => Nil
     case Some((_, Sequent_Structure(Structure_Formula(Formula_Zer(_))))) => Nil
     case Some((_, Sequent_Structure(Structure_Freevar(_)))) => Nil
     case Some((_, Sequent_Structure(Structure_Phi(_)))) => Nil
     case Some((_, Sequent_Structure(Structure_Zer(_)))) => Nil
   })

def swapout_R(relAKA: Action => Agent => List[Action], seq: Sequent,
               x2: Sequent):
      Option[List[Sequent]]
  =
  (relAKA, seq, x2) match {
  case (relAKA, seq, Sequenta(Structure_Bigcomma(y :: ys), x)) =>
    swapout_R_aux(relAKA,
                   betaList(relAKA,
                             map[(Structure, Structure),
                                  (Sequent,
                                    Sequent)]((a: (Structure, Structure)) =>
        {
          val (xa, ya): (Structure, Structure) = a;
          (Sequent_Structure(xa), Sequent_Structure(ya))
        },
       match_Structure(Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
           Structure_Agent_Structure(Structure_ForwK(),
                                      Agent_Freevar(List('a')),
                                      Structure_Freevar(List('X')))),
                        x))),
                   seq, Sequenta(Structure_Bigcomma(y :: ys), x))
  case (uu, uv, Sequenta(Structure_Action_Structure(vb, vc, vd), va)) => None
  case (uu, uv, Sequenta(Structure_Agent_Structure(vb, vc, vd), va)) => None
  case (uu, uv, Sequenta(Structure_Bigcomma(Nil), va)) => None
  case (uu, uv, Sequenta(Structure_Bin(vb, vc, vd), va)) => None
  case (uu, uv, Sequenta(Structure_Formula(vb), va)) => None
  case (uu, uv, Sequenta(Structure_Freevar(vb), va)) => None
  case (uu, uv, Sequenta(Structure_Phi(vb), va)) => None
  case (uu, uv, Sequenta(Structure_Zer(vb), va)) => None
  case (uu, uv, Sequent_Structure(v)) => None
}

def swapout_L_aux(relAKA: Action => Agent => List[Action], uu: List[Action],
                   seq: Sequent, x3: Sequent):
      Option[List[Sequent]]
  =
  (relAKA, uu, seq, x3) match {
  case (relAKA, Nil, seq, Sequenta(x, Structure_Bigcomma(Nil))) =>
    Some[List[Sequent]](Nil)
  case (relAKA, b :: list, seq, Sequenta(x, Structure_Bigcomma(y :: ys))) =>
    (swapout_L_aux(relAKA, list, seq, Sequenta(x, Structure_Bigcomma(ys))) match
       {
       case None => None
       case Some(lista) =>
         (if (relAKACheck(relAKA,
                           union[(Sequent,
                                   Sequent)].apply(match_Sequent(seq,
                          replaceAll[Sequent](map[(Structure, Structure),
           (Sequent,
             Sequent)]((a: (Structure, Structure)) =>
                         {
                           val (xa, ya): (Structure, Structure) = a;
                           (Sequent_Structure(xa), Sequent_Structure(ya))
                         },
                        (Structure_Formula(Formula_Action(Action_Freevar(List('b',
                                       'e', 't', 'a')))),
                          Structure_Formula(Formula_Action(b))) ::
                          (Structure_Freevar(List('Y')), y) ::
                            match_Structure(Structure_Action_Structure(Structure_ForwA(),
                                Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                                Structure_Agent_Structure(Structure_ForwK(),
                   Agent_Freevar(List('a')), Structure_Freevar(List('X')))),
     x)),
       seq))).apply(map[(Structure, Structure),
                         (Sequent,
                           Sequent)]((a: (Structure, Structure)) =>
                                       {
 val (xa, ya): (Structure, Structure) = a;
 (Sequent_Structure(xa), Sequent_Structure(ya))
                                       },
                                      (Structure_Formula(Formula_Action(Action_Freevar(List('b',
             'e', 't', 'a')))),
Structure_Formula(Formula_Action(b))) ::
(Structure_Freevar(List('Y')), y) ::
  match_Structure(Structure_Action_Structure(Structure_ForwA(),
      Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
      Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                 Structure_Freevar(List('X')))),
                   x)))))
           Some[List[Sequent]](replaceAll[Sequent](map[(Structure, Structure),
                (Sequent,
                  Sequent)]((a: (Structure, Structure)) =>
                              {
                                val (xa, ya): (Structure, Structure) = a;
                                (Sequent_Structure(xa), Sequent_Structure(ya))
                              },
                             (Structure_Formula(Formula_Action(Action_Freevar(List('b',
    'e', 't', 'a')))),
                               Structure_Formula(Formula_Action(b))) ::
                               (Structure_Freevar(List('Y')), y) ::
                                 match_Structure(Structure_Action_Structure(Structure_ForwA(),
                                     Action_Freevar(List('a', 'l', 'p', 'h',
                  'a')),
                                     Structure_Agent_Structure(Structure_ForwK(),
                        Agent_Freevar(List('a')),
                        Structure_Freevar(List('X')))),
          x)),
            seq) ::
                                 lista)
           else None)
     })
  case (relAKA, v :: va, uv,
         Sequenta(vb, Structure_Action_Structure(vd, ve, vf)))
    => None
  case (relAKA, v :: va, uv,
         Sequenta(vb, Structure_Agent_Structure(vd, ve, vf)))
    => None
  case (relAKA, v :: va, uv, Sequenta(vb, Structure_Bigcomma(Nil))) => None
  case (relAKA, v :: va, uv, Sequenta(vb, Structure_Bin(vd, ve, vf))) => None
  case (relAKA, v :: va, uv, Sequenta(vb, Structure_Formula(vd))) => None
  case (relAKA, v :: va, uv, Sequenta(vb, Structure_Freevar(vd))) => None
  case (relAKA, v :: va, uv, Sequenta(vb, Structure_Phi(vd))) => None
  case (relAKA, v :: va, uv, Sequenta(vb, Structure_Zer(vd))) => None
  case (relAKA, v :: va, uv, Sequent_Structure(vb)) => None
  case (relAKA, uu, uv, Sequenta(v, Structure_Action_Structure(vb, vc, vd))) =>
    None
  case (relAKA, uu, uv, Sequenta(v, Structure_Agent_Structure(vb, vc, vd))) =>
    None
  case (relAKA, Nil, uv, Sequenta(v, Structure_Bigcomma(vc :: vd))) => None
  case (relAKA, uu, uv, Sequenta(v, Structure_Bin(vb, vc, vd))) => None
  case (relAKA, uu, uv, Sequenta(v, Structure_Formula(vb))) => None
  case (relAKA, uu, uv, Sequenta(v, Structure_Freevar(vb))) => None
  case (relAKA, uu, uv, Sequenta(v, Structure_Phi(vb))) => None
  case (relAKA, uu, uv, Sequenta(v, Structure_Zer(vb))) => None
  case (relAKA, uu, uv, Sequent_Structure(v)) => None
}

def swapout_L(relAKA: Action => Agent => List[Action], seq: Sequent,
               x2: Sequent):
      Option[List[Sequent]]
  =
  (relAKA, seq, x2) match {
  case (relAKA, seq, Sequenta(x, Structure_Bigcomma(y :: ys))) =>
    swapout_L_aux(relAKA,
                   betaList(relAKA,
                             map[(Structure, Structure),
                                  (Sequent,
                                    Sequent)]((a: (Structure, Structure)) =>
        {
          val (xa, ya): (Structure, Structure) = a;
          (Sequent_Structure(xa), Sequent_Structure(ya))
        },
       match_Structure(Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
           Structure_Agent_Structure(Structure_ForwK(),
                                      Agent_Freevar(List('a')),
                                      Structure_Freevar(List('X')))),
                        x))),
                   seq, Sequenta(x, Structure_Bigcomma(y :: ys)))
  case (uu, uv, Sequenta(v, Structure_Action_Structure(vb, vc, vd))) => None
  case (uu, uv, Sequenta(v, Structure_Agent_Structure(vb, vc, vd))) => None
  case (uu, uv, Sequenta(v, Structure_Bigcomma(Nil))) => None
  case (uu, uv, Sequenta(v, Structure_Bin(vb, vc, vd))) => None
  case (uu, uv, Sequenta(v, Structure_Formula(vb))) => None
  case (uu, uv, Sequenta(v, Structure_Freevar(vb))) => None
  case (uu, uv, Sequenta(v, Structure_Phi(vb))) => None
  case (uu, uv, Sequenta(v, Structure_Zer(vb))) => None
  case (uu, uv, Sequent_Structure(v)) => None
}

def ruleRuleSwapout(x: Locale, xa1: RuleSwapout): ruleder = (x, xa1) match {
  case (x, Swapout_L()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(rel) =>
         ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
               Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
               Structure_Agent_Structure(Structure_ForwK(),
  Agent_Freevar(List('a')), Structure_Freevar(List('X')))),
                            Structure_Freevar(List('Y', 'l', 'i', 's', 't'))),
                   (a: Sequent) =>
                     swapout_L(rel, Sequenta(Structure_Agent_Structure(Structure_ForwK(),
                                Agent_Freevar(List('a')),
                                Structure_Action_Structure(Structure_ForwA(),
                    Action_Freevar(List('b', 'e', 't', 'a')),
                    Structure_Freevar(List('X')))),
      Structure_Freevar(List('Y'))),
                                a))
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, Swapout_R()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(rel) =>
         ruledera(Sequenta(Structure_Freevar(List('Y', 'l', 'i', 's', 't')),
                            Structure_Action_Structure(Structure_ForwA(),
                Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                Structure_Agent_Structure(Structure_ForwK(),
   Agent_Freevar(List('a')), Structure_Freevar(List('X'))))),
                   (a: Sequent) =>
                     swapout_R(rel, Sequenta(Structure_Freevar(List('Y')),
      Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                 Structure_Action_Structure(Structure_ForwA(),
                     Action_Freevar(List('b', 'e', 't', 'a')),
                     Structure_Freevar(List('X'))))),
                                a))
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
}

def ruleRuleStructK(x: Locale, xa1: RuleStructK): ruleder = (x, xa1) match {
  case (x, K_nec_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Agent_Structure(Structure_BackK(),
          Agent_Freevar(List('a')), Structure_Zer(Structure_Neutral()))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Zer(Structure_Neutral())))))
  case (x, Nec_K_L()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
         Agent_Freevar(List('a')), Structure_Zer(Structure_Neutral())),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('X'))))))
  case (x, K_mon_L()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_BackK(),
         Agent_Freevar(List('a')),
         Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                        Structure_Freevar(List('Y')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Agent_Structure(Structure_BackK(),
           Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                         Structure_Comma(),
                         Structure_Agent_Structure(Structure_BackK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('Y')))),
           Structure_Freevar(List('Z'))))))
  case (x, Mon_K_L()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
         Agent_Freevar(List('a')),
         Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                        Structure_Freevar(List('Y')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Agent_Structure(Structure_ForwK(),
           Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                         Structure_Comma(),
                         Structure_Agent_Structure(Structure_ForwK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('Y')))),
           Structure_Freevar(List('Z'))))))
  case (x, FS_K_L()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
         Agent_Freevar(List('a')),
         Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                        Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Agent_Structure(Structure_ForwK(),
           Agent_Freevar(List('a')), Structure_Freevar(List('Y'))),
                         Structure_ImpR(),
                         Structure_Agent_Structure(Structure_ForwK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('X'))))))
  case (x, FS_K_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Agent_Structure(Structure_ForwK(),
          Agent_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                         Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Agent_Structure(Structure_ForwK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('Y'))),
                          Structure_ImpR(),
                          Structure_Agent_Structure(Structure_ForwK(),
             Agent_Freevar(List('a')), Structure_Freevar(List('Z'))))))))
  case (x, Mon_K_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Agent_Structure(Structure_ForwK(),
          Agent_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                         Structure_Freevar(List('Y'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Agent_Structure(Structure_ForwK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                          Structure_Comma(),
                          Structure_Agent_Structure(Structure_ForwK(),
             Agent_Freevar(List('a')), Structure_Freevar(List('Y'))))))))
  case (x, K_mon_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Agent_Structure(Structure_BackK(),
          Agent_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                         Structure_Freevar(List('Y'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Agent_Structure(Structure_BackK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                          Structure_Comma(),
                          Structure_Agent_Structure(Structure_BackK(),
             Agent_Freevar(List('a')), Structure_Freevar(List('Y'))))))))
  case (x, K_FS_L()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_BackK(),
         Agent_Freevar(List('a')),
         Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                        Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Agent_Structure(Structure_BackK(),
           Agent_Freevar(List('a')), Structure_Freevar(List('Y'))),
                         Structure_ImpR(),
                         Structure_Agent_Structure(Structure_BackK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('X'))))))
  case (x, Nec_K_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Agent_Structure(Structure_ForwK(),
          Agent_Freevar(List('a')), Structure_Zer(Structure_Neutral()))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Zer(Structure_Neutral())))))
  case (x, K_FS_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Agent_Structure(Structure_BackK(),
          Agent_Freevar(List('a')),
          Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpR(),
                         Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Agent_Structure(Structure_BackK(),
            Agent_Freevar(List('a')), Structure_Freevar(List('Y'))),
                          Structure_ImpR(),
                          Structure_Agent_Structure(Structure_BackK(),
             Agent_Freevar(List('a')), Structure_Freevar(List('Z'))))))))
  case (x, K_nec_L()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_BackK(),
         Agent_Freevar(List('a')), Structure_Zer(Structure_Neutral())),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('X'))))))
}

def ruleRuleDispAct(x: Locale, xa1: RuleDispAct): ruleder = (x, xa1) match {
  case (x, Back_forw_A()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_BackA(),
          Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Action_Structure(Structure_ForwA(),
                                       Action_Freevar(List('a')),
                                       Structure_Freevar(List('Y')))))))
  case (x, Forw_back_A2()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Action_Structure(Structure_BackA(),
                                       Action_Freevar(List('a')),
                                       Structure_Freevar(List('Y')))))))
  case (x, Forw_back_A()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Action_Structure(Structure_BackA(),
           Action_Freevar(List('a')), Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Action_Structure(Structure_ForwA(),
                                      Action_Freevar(List('a')),
                                      Structure_Freevar(List('X'))),
           Structure_Freevar(List('Y'))))))
  case (x, Back_forw_A2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a')), Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Action_Structure(Structure_BackA(),
                                      Action_Freevar(List('a')),
                                      Structure_Freevar(List('X'))),
           Structure_Freevar(List('Y'))))))
}

def swapin(fun: Action => Agent => List[Action], m: Sequent, s: Sequent):
      Boolean
  =
  relAKACheck(fun, match_Sequent(m, s))

def ruleRuleSwapin(x: Locale, xa1: RuleSwapin): ruleder = (x, xa1) match {
  case (x, Swapin_L()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(rel) =>
         ruleder_cond((a: Sequent) =>
                        swapin(rel, Sequenta(Structure_Bin(Structure_Phi(Action_Freevar(List('a',
              'l', 'p', 'h', 'a'))),
                    Structure_Comma(),
                    Structure_Agent_Structure(Structure_ForwK(),
       Agent_Freevar(List('a')),
       Structure_Action_Structure(Structure_ForwA(),
                                   Action_Freevar(List('b', 'e', 't', 'a')),
                                   Structure_Freevar(List('X'))))),
      Structure_Freevar(List('Y'))),
                                a),
                       Sequenta(Structure_Bin(Structure_Phi(Action_Freevar(List('a',
 'l', 'p', 'h', 'a'))),
       Structure_Comma(),
       Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                  Structure_Action_Structure(Structure_ForwA(),
                      Action_Freevar(List('b', 'e', 't', 'a')),
                      Structure_Freevar(List('X'))))),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) =>
                         Some[List[Sequent]](List(Sequenta(Structure_Action_Structure(Structure_ForwA(),
       Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
       Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                  Structure_Freevar(List('X')))),
                    Structure_Freevar(List('Y'))))))
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, Swapin_R()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(rel) =>
         ruleder_cond((a: Sequent) =>
                        swapin(rel, Sequenta(Structure_Freevar(List('Y')),
      Structure_Bin(Structure_Phi(Action_Freevar(List('a', 'l', 'p', 'h',
               'a'))),
                     Structure_ImpR(),
                     Structure_Agent_Structure(Structure_ForwK(),
        Agent_Freevar(List('a')),
        Structure_Action_Structure(Structure_ForwA(),
                                    Action_Freevar(List('b', 'e', 't', 'a')),
                                    Structure_Freevar(List('X')))))),
                                a),
                       Sequenta(Structure_Freevar(List('Y')),
                                 Structure_Bin(Structure_Phi(Action_Freevar(List('a',
  'l', 'p', 'h', 'a'))),
        Structure_ImpR(),
        Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                   Structure_Action_Structure(Structure_ForwA(),
                       Action_Freevar(List('b', 'e', 't', 'a')),
                       Structure_Freevar(List('X')))))),
                       (_: Sequent) =>
                         Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
                    Structure_Action_Structure(Structure_ForwA(),
        Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
        Structure_Agent_Structure(Structure_ForwK(), Agent_Freevar(List('a')),
                                   Structure_Freevar(List('X'))))))))
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
}

def ruleRuleStruct(x: Locale, xa1: RuleStruct): ruleder = (x, xa1) match {
  case (x, W_impL_R()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_ImpL(),
                                     Structure_Freevar(List('Z'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Z'))))))
  case (x, ImpL_I()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_ImpL(),
                                     Structure_Freevar(List('Y'))),
                       Structure_Zer(Structure_Neutral())),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, W_impL_L()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')),
                       Structure_Bin(Structure_Freevar(List('Z')),
                                      Structure_ImpL(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Z'))))))
  case (x, ImpR_I2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('Y')),
                         Structure_ImpR(), Structure_Freevar(List('X'))),
           Structure_Zer(Structure_Neutral())))))
  case (x, E_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Freevar(List('Y', '2')),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y', '1')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Freevar(List('Y', '1')), Structure_Comma(),
                          Structure_Freevar(List('Y', '2')))))))
  case (x, IW_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Zer(Structure_Neutral())))))
  case (x, IW_L()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('Y'))))))
  case (x, A_L2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
           Structure_Comma(), Structure_Freevar(List('Y'))),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Z'))),
                       Structure_Freevar(List('W'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(),
                         Structure_Bin(Structure_Freevar(List('Y')),
Structure_Comma(), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('W'))))))
  case (x, E_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X', '2')),
                                     Structure_Comma(),
                                     Structure_Freevar(List('X', '1'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X',
        '1')),
                         Structure_Comma(), Structure_Freevar(List('X', '2'))),
           Structure_Freevar(List('Y'))))))
  case (x, A_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('W')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_Comma(),
                                      Structure_Bin(Structure_Freevar(List('Y')),
             Structure_Comma(), Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('W')),
           Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
Structure_Comma(), Structure_Freevar(List('Y'))),
                          Structure_Comma(), Structure_Freevar(List('Z')))))))
  case (x, W_impR_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_ImpR(),
                                      Structure_Freevar(List('Z')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Z'))))))
  case (x, C_L()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(), Structure_Freevar(List('X'))),
           Structure_Freevar(List('Y'))))))
  case (x, C_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Freevar(List('Y')), Structure_Comma(),
                          Structure_Freevar(List('Y')))))))
  case (x, ImpR_I()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('Y')),
                                     Structure_ImpR(),
                                     Structure_Freevar(List('X'))),
                       Structure_Zer(Structure_Neutral())),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, W_impR_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('Z')),
                                     Structure_ImpR(),
                                     Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Z'))))))
  case (x, A_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Bin(Structure_Freevar(List('Y')),
            Structure_Comma(), Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('W'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
                                       Structure_Comma(),
                                       Structure_Freevar(List('Y'))),
                         Structure_Comma(), Structure_Freevar(List('Z'))),
           Structure_Freevar(List('W'))))))
  case (x, A_R2()) =>
    ruledera(Sequenta(Structure_Freevar(List('W')),
                       Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
            Structure_Comma(), Structure_Freevar(List('Y'))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Z')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('W')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                          Structure_Bin(Structure_Freevar(List('Y')),
 Structure_Comma(), Structure_Freevar(List('Z'))))))))
  case (x, I_impR2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Bin(Structure_Freevar(List('X')), Structure_ImpR(),
                          Structure_Freevar(List('Y')))))))
  case (x, I_impL()) =>
    ruledera(Sequenta(Structure_Zer(Structure_Neutral()),
                       Structure_Bin(Structure_Freevar(List('Y')),
                                      Structure_ImpL(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, I_impR()) =>
    ruledera(Sequenta(Structure_Zer(Structure_Neutral()),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_ImpR(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Freevar(List('Y'))))))
  case (x, ImpL_I2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_ImpL(), Structure_Freevar(List('Y'))),
           Structure_Zer(Structure_Neutral())))))
  case (x, I_impL2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Bin(Structure_Freevar(List('Y')), Structure_ImpL(),
                          Structure_Freevar(List('X')))))))
}

def pre_r(a: Action, x1: Sequent): Boolean = (a, x1) match {
  case (a, Sequenta(x, Structure_Formula(Formula_Precondition(alpha)))) =>
    equal_Actiona(a, alpha)
  case (a, Sequenta(v, Structure_Action_Structure(vb, vc, vd))) => false
  case (a, Sequenta(v, Structure_Agent_Structure(vb, vc, vd))) => false
  case (a, Sequenta(v, Structure_Bigcomma(vb))) => false
  case (a, Sequenta(v, Structure_Bin(vb, vc, vd))) => false
  case (a, Sequenta(v, Structure_Formula(Formula_Action(vc)))) => false
  case (a, Sequenta(v, Structure_Formula(Formula_Action_Formula(vc, vd, ve))))
    => false
  case (a, Sequenta(v, Structure_Formula(Formula_Agent(vc)))) => false
  case (a, Sequenta(v, Structure_Formula(Formula_Agent_Formula(vc, vd, ve)))) =>
    false
  case (a, Sequenta(v, Structure_Formula(Formula_Atprop(vc)))) => false
  case (a, Sequenta(v, Structure_Formula(Formula_Bin(vc, vd, ve)))) => false
  case (a, Sequenta(v, Structure_Formula(Formula_Freevar(vc)))) => false
  case (a, Sequenta(v, Structure_Formula(Formula_Zer(vc)))) => false
  case (a, Sequenta(v, Structure_Freevar(vb))) => false
  case (a, Sequenta(v, Structure_Phi(vb))) => false
  case (a, Sequenta(v, Structure_Zer(vb))) => false
  case (a, Sequent_Structure(v)) => false
}

def pre_l(a: Action, x1: Sequent): Boolean = (a, x1) match {
  case (a, Sequenta(Structure_Formula(Formula_Precondition(alpha)), x)) =>
    equal_Actiona(a, alpha)
  case (a, Sequenta(Structure_Action_Structure(vb, vc, vd), va)) => false
  case (a, Sequenta(Structure_Agent_Structure(vb, vc, vd), va)) => false
  case (a, Sequenta(Structure_Bigcomma(vb), va)) => false
  case (a, Sequenta(Structure_Bin(vb, vc, vd), va)) => false
  case (a, Sequenta(Structure_Formula(Formula_Action(vc)), va)) => false
  case (a, Sequenta(Structure_Formula(Formula_Action_Formula(vc, vd, ve)), va))
    => false
  case (a, Sequenta(Structure_Formula(Formula_Agent(vc)), va)) => false
  case (a, Sequenta(Structure_Formula(Formula_Agent_Formula(vc, vd, ve)), va))
    => false
  case (a, Sequenta(Structure_Formula(Formula_Atprop(vc)), va)) => false
  case (a, Sequenta(Structure_Formula(Formula_Bin(vc, vd, ve)), va)) => false
  case (a, Sequenta(Structure_Formula(Formula_Freevar(vc)), va)) => false
  case (a, Sequenta(Structure_Formula(Formula_Zer(vc)), va)) => false
  case (a, Sequenta(Structure_Freevar(vb), va)) => false
  case (a, Sequenta(Structure_Phi(vb), va)) => false
  case (a, Sequenta(Structure_Zer(vb), va)) => false
  case (a, Sequent_Structure(v)) => false
}

def ruleRuleOpAct(x: Locale, xa1: RuleOpAct): ruleder = (x, xa1) match {
  case (x, FdiamA_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Action_Formula(Formula_FdiamA(),
                        Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                        Formula_Freevar(List('A')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Action_Structure(Structure_ForwA(),
                                      Action_Freevar(List('a', 'l', 'p', 'h',
                   'a')),
                                      Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('X'))))))
  case (x, One_R()) =>
    ruledera(Sequenta(Structure_Phi(Action_Freevar(List('a', 'l', 'p', 'h',
                 'a'))),
                       Structure_Formula(Formula_Precondition(Action_Freevar(List('a',
   'l', 'p', 'h', 'a'))))),
              (_: Sequent) => Some[List[Sequent]](Nil))
  case (x, BdiamA_R()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_BackA(),
          Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
          Structure_Freevar(List('X'))),
                       Structure_Formula(Formula_Action_Formula(Formula_BdiamA(),
                         Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                         Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))))))
  case (x, FboxA_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Formula(Formula_Action_Formula(Formula_FboxA(),
                         Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                         Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Action_Structure(Structure_ForwA(),
                                       Action_Freevar(List('a', 'l', 'p', 'h',
                    'a')),
                                       Structure_Formula(Formula_Freevar(List('A'))))))))
  case (x, Pre_L()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case PreFormula(alpha, f) =>
         ruleder_cond((a: Sequent) => pre_l(alpha, a),
                       Sequenta(Structure_Freevar(List('X')),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) =>
                         Some[List[Sequent]](List(Sequenta(Structure_Formula(f),
                    Structure_Freevar(List('Y'))))))
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, BboxA_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Formula(Formula_Action_Formula(Formula_BboxA(),
                         Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                         Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Action_Structure(Structure_BackA(),
                                       Action_Freevar(List('a', 'l', 'p', 'h',
                    'a')),
                                       Structure_Formula(Formula_Freevar(List('A'))))))))
  case (x, BboxA_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Action_Formula(Formula_BboxA(),
                        Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                        Formula_Freevar(List('A')))),
                       Structure_Action_Structure(Structure_BackA(),
           Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
           Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))))))
  case (x, FboxA_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Action_Formula(Formula_FboxA(),
                        Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                        Formula_Freevar(List('A')))),
                       Structure_Action_Structure(Structure_ForwA(),
           Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
           Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))))))
  case (x, Pre_R()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case PreFormula(alpha, f) =>
         ruleder_cond((a: Sequent) => pre_r(alpha, a),
                       Sequenta(Structure_Freevar(List('X')),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) =>
                         Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
                    Structure_Formula(f)))))
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, BdiamA_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Action_Formula(Formula_BdiamA(),
                        Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                        Formula_Freevar(List('A')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Action_Structure(Structure_BackA(),
                                      Action_Freevar(List('a', 'l', 'p', 'h',
                   'a')),
                                      Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('X'))))))
  case (x, One_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Precondition(Action_Freevar(List('a',
  'l', 'p', 'h', 'a')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Phi(Action_Freevar(List('a',
     'l', 'p', 'h', 'a'))),
           Structure_Freevar(List('X'))))))
  case (x, FdiamA_R()) =>
    ruledera(Sequenta(Structure_Action_Structure(Structure_ForwA(),
          Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
          Structure_Freevar(List('X'))),
                       Structure_Formula(Formula_Action_Formula(Formula_FdiamA(),
                         Action_Freevar(List('a', 'l', 'p', 'h', 'a')),
                         Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))))))
}

def ruleRuleGrish(x: Locale, xa1: RuleGrish): ruleder = (x, xa1) match {
  case (x, Grishin_R2()) =>
    ruledera(Sequenta(Structure_Freevar(List('W')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_ImpR(),
                                      Structure_Bin(Structure_Freevar(List('Y')),
             Structure_Comma(), Structure_Freevar(List('Z'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('W')),
           Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
Structure_ImpR(), Structure_Freevar(List('Y'))),
                          Structure_Comma(), Structure_Freevar(List('Z')))))))
  case (x, Grishin_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('W')),
                       Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
            Structure_ImpR(), Structure_Freevar(List('Y'))),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Z')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('W')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_ImpR(),
                          Structure_Bin(Structure_Freevar(List('Y')),
 Structure_Comma(), Structure_Freevar(List('Z'))))))))
  case (x, Grishin_L()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
           Structure_ImpR(), Structure_Freevar(List('Y'))),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Z'))),
                       Structure_Freevar(List('W'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_ImpR(),
                         Structure_Bin(Structure_Freevar(List('Y')),
Structure_Comma(), Structure_Freevar(List('Z')))),
           Structure_Freevar(List('W'))))))
  case (x, Grishin_L2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_ImpR(),
                                     Structure_Bin(Structure_Freevar(List('Y')),
            Structure_Comma(), Structure_Freevar(List('Z')))),
                       Structure_Freevar(List('W'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Bin(Structure_Freevar(List('X')),
                                       Structure_ImpR(),
                                       Structure_Freevar(List('Y'))),
                         Structure_Comma(), Structure_Freevar(List('Z'))),
           Structure_Freevar(List('W'))))))
}

def ruleRuleDispK(x: Locale, xa1: RuleDispK): ruleder = (x, xa1) match {
  case (x, Back_forw_K2()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Agent_Structure(Structure_ForwK(),
          Agent_Freevar(List('a')), Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Agent_Structure(Structure_BackK(),
                                     Agent_Freevar(List('a')),
                                     Structure_Freevar(List('X'))),
           Structure_Freevar(List('Y'))))))
  case (x, Back_forw_K()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_BackK(),
         Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Agent_Structure(Structure_ForwK(),
                                      Agent_Freevar(List('a')),
                                      Structure_Freevar(List('Y')))))))
  case (x, Forw_back_K2()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
         Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Agent_Structure(Structure_BackK(),
                                      Agent_Freevar(List('a')),
                                      Structure_Freevar(List('Y')))))))
  case (x, Forw_back_K()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Agent_Structure(Structure_BackK(),
          Agent_Freevar(List('a')), Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
                                     Agent_Freevar(List('a')),
                                     Structure_Freevar(List('X'))),
           Structure_Freevar(List('Y'))))))
}

def ruleRuleDisp(x: Locale, xa1: RuleDisp): ruleder = (x, xa1) match {
  case (x, Comma_impL_disp()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Bin(Structure_Freevar(List('Z')),
                                      Structure_ImpL(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(), Structure_Freevar(List('Y'))),
           Structure_Freevar(List('Z'))))))
  case (x, Comma_impR_disp2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Y'))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Y')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_ImpR(),
                          Structure_Freevar(List('Z')))))))
  case (x, ImpL_comma_disp2()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('Z')),
                         Structure_ImpL(), Structure_Freevar(List('Y'))),
           Structure_Freevar(List('X'))))))
  case (x, ImpR_comma_disp2()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_ImpR(), Structure_Freevar(List('Z'))),
           Structure_Freevar(List('Y'))))))
  case (x, ImpR_comma_disp()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_ImpR(),
                                     Structure_Freevar(List('Z'))),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                          Structure_Freevar(List('Y')))))))
  case (x, ImpL_comma_disp()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('Z')),
                                     Structure_ImpL(),
                                     Structure_Freevar(List('Y'))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Freevar(List('X')), Structure_Comma(),
                          Structure_Freevar(List('Y')))))))
  case (x, Comma_impR_disp()) =>
    ruledera(Sequenta(Structure_Freevar(List('Y')),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_ImpR(),
                                      Structure_Freevar(List('Z')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                         Structure_Comma(), Structure_Freevar(List('Y'))),
           Structure_Freevar(List('Z'))))))
  case (x, Comma_impL_disp2()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Y'))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Bin(Structure_Freevar(List('Z')), Structure_ImpL(),
                          Structure_Freevar(List('Y')))))))
}

def equal_option[A : equal](x0: Option[A], x1: Option[A]): Boolean = (x0, x1)
  match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => eq[A](x2, y2)
  case (None, None) => true
}

def is_act_mod(x0: Structure): Option[Atprop] = x0 match {
  case Structure_Formula(Formula_Atprop(p)) => Some[Atprop](p)
  case Structure_Action_Structure(uu, uv, s) => is_act_mod(s)
  case Structure_Agent_Structure(v, va, vb) => None
  case Structure_Bigcomma(v) => None
  case Structure_Bin(v, va, vb) => None
  case Structure_Formula(Formula_Action(va)) => None
  case Structure_Formula(Formula_Action_Formula(va, vb, vc)) => None
  case Structure_Formula(Formula_Agent(va)) => None
  case Structure_Formula(Formula_Agent_Formula(va, vb, vc)) => None
  case Structure_Formula(Formula_Bin(va, vb, vc)) => None
  case Structure_Formula(Formula_Freevar(va)) => None
  case Structure_Formula(Formula_Precondition(va)) => None
  case Structure_Formula(Formula_Zer(va)) => None
  case Structure_Freevar(v) => None
  case Structure_Phi(v) => None
  case Structure_Zer(v) => None
}

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def atom(x0: Sequent): Boolean = x0 match {
  case Sequenta(l, r) =>
    ! (is_none[Atprop](is_act_mod(l))) &&
      equal_option[Atprop](is_act_mod(l), is_act_mod(r))
  case Sequent_Structure(v) => false
}

def ruleRuleZer(x: Locale, xa1: RuleZer): ruleder = (x, xa1) match {
  case (x, Prem()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(seq) =>
         ruleder_cond((a: Sequent) => equal_Sequenta(seq, a),
                       Sequenta(Structure_Freevar(List('X')),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) => Some[List[Sequent]](Nil))
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, Partial()) =>
    (x match {
       case CutFormula(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(struct) =>
         ruleder_cond((a: Sequent) =>
                        {
                          val (Sequenta(lhs, rhs)): Sequent = a;
                          equal_Structurea(struct, lhs) ||
                            equal_Structurea(struct, rhs)
                        },
                       Sequenta(Structure_Freevar(List('X')),
                                 Structure_Freevar(List('Y'))),
                       (_: Sequent) => Some[List[Sequent]](Nil))
       case RelAKA(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
  case (x, Id()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Atprop(Atprop_Freevar(List('p')))),
                       Structure_Formula(Formula_Atprop(Atprop_Freevar(List('p'))))),
              (_: Sequent) => Some[List[Sequent]](Nil))
  case (x, Atom()) =>
    ruleder_cond((a: Sequent) => atom(a),
                  Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                  (_: Sequent) => Some[List[Sequent]](Nil))
}

def ruleRuleOpK(x: Locale, xa1: RuleOpK): ruleder = (x, xa1) match {
  case (x, BdiamK_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Agent_Formula(Formula_BdiamK(),
                       Agent_Freevar(List('a')), Formula_Freevar(List('A')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Agent_Structure(Structure_BackK(),
                                     Agent_Freevar(List('a')),
                                     Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('X'))))))
  case (x, FdiamK_R()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
         Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Formula(Formula_Agent_Formula(Formula_FdiamK(),
                        Agent_Freevar(List('a')), Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))))))
  case (x, FboxK_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Formula(Formula_Agent_Formula(Formula_FboxK(),
                        Agent_Freevar(List('a')), Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Agent_Structure(Structure_ForwK(),
                                      Agent_Freevar(List('a')),
                                      Structure_Formula(Formula_Freevar(List('A'))))))))
  case (x, BboxK_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Agent_Formula(Formula_BboxK(),
                       Agent_Freevar(List('a')), Formula_Freevar(List('A')))),
                       Structure_Agent_Structure(Structure_BackK(),
          Agent_Freevar(List('a')), Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))))))
  case (x, BboxK_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Formula(Formula_Agent_Formula(Formula_BboxK(),
                        Agent_Freevar(List('a')), Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Agent_Structure(Structure_BackK(),
                                      Agent_Freevar(List('a')),
                                      Structure_Formula(Formula_Freevar(List('A'))))))))
  case (x, FboxK_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Agent_Formula(Formula_FboxK(),
                       Agent_Freevar(List('a')), Formula_Freevar(List('A')))),
                       Structure_Agent_Structure(Structure_ForwK(),
          Agent_Freevar(List('a')), Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))))))
  case (x, FdiamK_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Agent_Formula(Formula_FdiamK(),
                       Agent_Freevar(List('a')), Formula_Freevar(List('A')))),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Agent_Structure(Structure_ForwK(),
                                     Agent_Freevar(List('a')),
                                     Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('X'))))))
  case (x, BdiamK_R()) =>
    ruledera(Sequenta(Structure_Agent_Structure(Structure_BackK(),
         Agent_Freevar(List('a')), Structure_Freevar(List('X'))),
                       Structure_Formula(Formula_Agent_Formula(Formula_BdiamK(),
                        Agent_Freevar(List('a')), Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))))))
}

def ruleRuleCut(x: Locale, xa1: RuleCut): ruleder = (x, xa1) match {
  case (x, SingleCut()) =>
    (x match {
       case CutFormula(f) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) =>
                     Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
                Structure_Formula(f)),
       Sequenta(Structure_Formula(f), Structure_Freevar(List('Y'))))))
       case Premise(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Part(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case RelAKA(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case PreFormula(_, _) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case LAgent(_) =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
       case Empty() =>
         ruledera(Sequenta(Structure_Freevar(List('X')),
                            Structure_Freevar(List('Y'))),
                   (_: Sequent) => None)
     })
}

def ruleRuleOp(x: Locale, xa1: RuleOp): ruleder = (x, xa1) match {
  case (x, Bot_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Formula(Formula_Zer(Formula_Bot()))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Zer(Structure_Neutral())))))
  case (x, Top_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Zer(Formula_Top())),
                       Structure_Freevar(List('X'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Zer(Structure_Neutral()),
           Structure_Freevar(List('X'))))))
  case (x, DImpR_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
             Formula_DImpR(), Formula_Freevar(List('B')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                         Structure_ImpR(),
                         Structure_Formula(Formula_Freevar(List('B')))),
           Structure_Freevar(List('Z'))))))
  case (x, ImpL_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Formula(Formula_Bin(Formula_Freevar(List('B')),
              Formula_ImpL(), Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('B'))),
                          Structure_ImpL(),
                          Structure_Formula(Formula_Freevar(List('A'))))))))
  case (x, DImpL_R()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('Y')),
                                     Structure_ImpL(),
                                     Structure_Freevar(List('X'))),
                       Structure_Formula(Formula_Bin(Formula_Freevar(List('B')),
              Formula_DImpL(), Formula_Freevar(List('A'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))),
  Sequenta(Structure_Freevar(List('Y')),
            Structure_Formula(Formula_Freevar(List('B')))))))
  case (x, And_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
             Formula_And(), Formula_Freevar(List('B')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                         Structure_Comma(),
                         Structure_Formula(Formula_Freevar(List('B')))),
           Structure_Freevar(List('Z'))))))
  case (x, ImpR_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
              Formula_ImpR(), Formula_Freevar(List('B'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                          Structure_ImpR(),
                          Structure_Formula(Formula_Freevar(List('B'))))))))
  case (x, Or_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
             Formula_Or(), Formula_Freevar(List('B')))),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_Comma(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))),
  Sequenta(Structure_Formula(Formula_Freevar(List('B'))),
            Structure_Freevar(List('Y'))))))
  case (x, Or_R()) =>
    ruledera(Sequenta(Structure_Freevar(List('Z')),
                       Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
              Formula_Or(), Formula_Freevar(List('B'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('Z')),
           Structure_Bin(Structure_Formula(Formula_Freevar(List('A'))),
                          Structure_Comma(),
                          Structure_Formula(Formula_Freevar(List('B'))))))))
  case (x, ImpR_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
             Formula_ImpR(), Formula_Freevar(List('B')))),
                       Structure_Bin(Structure_Freevar(List('X')),
                                      Structure_ImpR(),
                                      Structure_Freevar(List('Y')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))),
  Sequenta(Structure_Formula(Formula_Freevar(List('B'))),
            Structure_Freevar(List('Y'))))))
  case (x, DImpL_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Bin(Formula_Freevar(List('B')),
             Formula_DImpL(), Formula_Freevar(List('A')))),
                       Structure_Freevar(List('Z'))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Bin(Structure_Formula(Formula_Freevar(List('B'))),
                         Structure_ImpL(),
                         Structure_Formula(Formula_Freevar(List('A')))),
           Structure_Freevar(List('Z'))))))
  case (x, And_R()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_Comma(),
                                     Structure_Freevar(List('Y'))),
                       Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
              Formula_And(), Formula_Freevar(List('B'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))),
  Sequenta(Structure_Freevar(List('Y')),
            Structure_Formula(Formula_Freevar(List('B')))))))
  case (x, DImpR_R()) =>
    ruledera(Sequenta(Structure_Bin(Structure_Freevar(List('X')),
                                     Structure_ImpR(),
                                     Structure_Freevar(List('Y'))),
                       Structure_Formula(Formula_Bin(Formula_Freevar(List('A')),
              Formula_DImpR(), Formula_Freevar(List('B'))))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Formula(Formula_Freevar(List('A'))),
           Structure_Freevar(List('X'))),
  Sequenta(Structure_Freevar(List('Y')),
            Structure_Formula(Formula_Freevar(List('B')))))))
  case (x, ImpL_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Bin(Formula_Freevar(List('B')),
             Formula_ImpL(), Formula_Freevar(List('A')))),
                       Structure_Bin(Structure_Freevar(List('Y')),
                                      Structure_ImpL(),
                                      Structure_Freevar(List('X')))),
              (_: Sequent) =>
                Some[List[Sequent]](List(Sequenta(Structure_Freevar(List('X')),
           Structure_Formula(Formula_Freevar(List('A')))),
  Sequenta(Structure_Formula(Formula_Freevar(List('B'))),
            Structure_Freevar(List('Y'))))))
  case (x, Top_R()) =>
    ruledera(Sequenta(Structure_Zer(Structure_Neutral()),
                       Structure_Formula(Formula_Zer(Formula_Top()))),
              (_: Sequent) => Some[List[Sequent]](Nil))
  case (x, Bot_L()) =>
    ruledera(Sequenta(Structure_Formula(Formula_Zer(Formula_Bot())),
                       Structure_Zer(Structure_Neutral())),
              (_: Sequent) => Some[List[Sequent]](Nil))
}

def rule(l: Locale, x1: Rule): ruleder = (l, x1) match {
  case (l, RuleBigcommaa(r)) => ruleRuleBigcomma(l, r)
  case (l, RuleCuta(r)) => ruleRuleCut(l, r)
  case (l, RuleDispa(r)) => ruleRuleDisp(l, r)
  case (l, RuleDispActa(r)) => ruleRuleDispAct(l, r)
  case (l, RuleDispKa(r)) => ruleRuleDispK(l, r)
  case (l, RuleGrisha(r)) => ruleRuleGrish(l, r)
  case (l, RuleKnowledgea(r)) => ruleRuleKnowledge(l, r)
  case (l, RuleOpa(r)) => ruleRuleOp(l, r)
  case (l, RuleOpActa(r)) => ruleRuleOpAct(l, r)
  case (l, RuleOpKa(r)) => ruleRuleOpK(l, r)
  case (l, RuleStructa(r)) => ruleRuleStruct(l, r)
  case (l, RuleStructActa(r)) => ruleRuleStructAct(l, r)
  case (l, RuleStructEAa(r)) => ruleRuleStructEA(l, r)
  case (l, RuleStructKa(r)) => ruleRuleStructK(l, r)
  case (l, RuleSwapina(r)) => ruleRuleSwapin(l, r)
  case (l, RuleSwapouta(r)) => ruleRuleSwapout(l, r)
  case (l, RuleZera(r)) => ruleRuleZer(l, r)
  case (uu, RuleMacro(v, va)) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) => None)
  case (uu, Fail()) =>
    ruledera(Sequenta(Structure_Freevar(List('X')),
                       Structure_Freevar(List('Y'))),
              (_: Sequent) => None)
}

def cond(x0: ruleder): Option[Sequent => Boolean] = x0 match {
  case ruleder_cond(c, va, vb) => Some[Sequent => Boolean](c)
  case ruledera(vc, vd) => None
}

def snd(x0: ruleder): Sequent => Option[List[Sequent]] = x0 match {
  case ruledera(ux, y) => y
  case ruleder_cond(uy, uz, y) => y
}

def fst(x0: ruleder): Sequent = x0 match {
  case ruledera(x, uu) => x
  case ruleder_cond(uv, x, uw) => x
}

def der(l: Locale, r: Rule, s: Sequent): (Rule, List[Sequent]) =
  ((snd(rule(l, r))).apply(s) match {
     case None => (Fail(), Nil)
     case Some(conclusion) =>
       (if (ruleMatch[Sequent](fst(rule(l, r)), s))
         (cond(rule(l, r)) match {
            case None =>
              (r, map[Sequent,
                       Sequent]((a: Sequent) =>
                                  replaceAll[Sequent](match_Sequent(fst(rule(l,
                                      r)),
                             s),
               a),
                                 conclusion))
            case Some(condition) =>
              (if (condition(s))
                (r, map[Sequent,
                         Sequent]((a: Sequent) =>
                                    replaceAll[Sequent](match_Sequent(fst(rule(l,
r)),
                               s),
                 a),
                                   conclusion))
                else (Fail(), Nil))
          })
         else (Fail(), Nil))
   })

def concl(x0: Prooftree): Sequent = x0 match {
  case Prooftreea(a, b, c) => a
}

def consq(x0: Sequent): Structure = x0 match {
  case Sequenta(x, y) => y
  case Sequent_Structure(x) => x
}

def extract[A](p: A => Boolean, x1: List[A]): Option[(List[A], (A, List[A]))] =
  (p, x1) match {
  case (p, x :: xs) =>
    (if (p(x)) Some[(List[A], (A, List[A]))]((Nil, (x, xs)))
      else (extract[A](p, xs) match {
              case None => None
              case Some((ys, (y, zs))) =>
                Some[(List[A], (A, List[A]))]((x :: ys, (y, zs)))
            }))
  case (p, Nil) => None
}

def ruleList: List[Rule] =
  map[RuleBigcomma,
       Rule]((a: RuleBigcomma) => RuleBigcommaa(a),
              List(Bigcomma_Nil_R(), Bigcomma_Cons_R(), Bigcomma_Cons_L2(),
                    Bigcomma_Nil_L2(), Bigcomma_Cons_R2(), Bigcomma_Cons_L(),
                    Bigcomma_Nil_R2(), Bigcomma_Nil_L())) ++
    (map[RuleCut, Rule]((a: RuleCut) => RuleCuta(a), List(SingleCut())) ++
      (map[RuleDisp,
            Rule]((a: RuleDisp) => RuleDispa(a),
                   List(Comma_impL_disp(), Comma_impR_disp2(),
                         ImpL_comma_disp2(), ImpR_comma_disp2(),
                         ImpR_comma_disp(), ImpL_comma_disp(),
                         Comma_impR_disp(), Comma_impL_disp2())) ++
        (map[RuleDispAct,
              Rule]((a: RuleDispAct) => RuleDispActa(a),
                     List(Back_forw_A(), Forw_back_A2(), Forw_back_A(),
                           Back_forw_A2())) ++
          (map[RuleDispK,
                Rule]((a: RuleDispK) => RuleDispKa(a),
                       List(Back_forw_K2(), Back_forw_K(), Forw_back_K2(),
                             Forw_back_K())) ++
            (map[RuleGrish,
                  Rule]((a: RuleGrish) => RuleGrisha(a),
                         List(Grishin_R2(), Grishin_R(), Grishin_L(),
                               Grishin_L2())) ++
              (map[RuleKnowledge,
                    Rule]((a: RuleKnowledge) => RuleKnowledgea(a),
                           List(Refl_ForwK())) ++
                (map[RuleOp,
                      Rule]((a: RuleOp) => RuleOpa(a),
                             List(Bot_R(), Top_L(), DImpR_L(), ImpL_R(),
                                   DImpL_R(), And_L(), ImpR_R(), Or_L(), Or_R(),
                                   ImpR_L(), DImpL_L(), And_R(), DImpR_R(),
                                   ImpL_L(), Top_R(), Bot_L())) ++
                  (map[RuleOpAct,
                        Rule]((a: RuleOpAct) => RuleOpActa(a),
                               List(FdiamA_L(), One_R(), BdiamA_R(), FboxA_R(),
                                     Pre_L(), BboxA_R(), BboxA_L(), FboxA_L(),
                                     Pre_R(), BdiamA_L(), One_L(),
                                     FdiamA_R())) ++
                    (map[RuleOpK,
                          Rule]((a: RuleOpK) => RuleOpKa(a),
                                 List(BdiamK_L(), FdiamK_R(), FboxK_R(),
                                       BboxK_L(), BboxK_R(), FboxK_L(),
                                       FdiamK_L(), BdiamK_R())) ++
                      (map[RuleStruct,
                            Rule]((a: RuleStruct) => RuleStructa(a),
                                   List(W_impL_R(), ImpL_I(), W_impL_L(),
 ImpR_I2(), E_R(), IW_R(), IW_L(), A_L2(), E_L(), A_R(), W_impR_R(), C_L(),
 C_R(), ImpR_I(), W_impR_L(), A_L(), A_R2(), I_impR2(), I_impL(), I_impR(),
 ImpL_I2(), I_impL2())) ++
                        (map[RuleStructAct,
                              Rule]((a: RuleStructAct) => RuleStructActa(a),
                                     List(A_nec_L(), A_mon_L(), Mon_A_R(),
   Nec_A_L(), FS_A_L(), FS_A_R(), A_mon_R(), A_FS_R(), Nec_A_R(), Mon_A_L(),
   A_FS_L(), A_nec_R())) ++
                          (map[RuleStructEA,
                                Rule]((a: RuleStructEA) => RuleStructEAa(a),
                                       List(Reduce_R(), CompA_R(), Balance(),
     CompA_L(), Reduce_L())) ++
                            (map[RuleStructK,
                                  Rule]((a: RuleStructK) => RuleStructKa(a),
 List(K_nec_R(), Nec_K_L(), K_mon_L(), Mon_K_L(), FS_K_L(), FS_K_R(), Mon_K_R(),
       K_mon_R(), K_FS_L(), Nec_K_R(), K_FS_R(), K_nec_L())) ++
                              (map[RuleSwapin,
                                    Rule]((a: RuleSwapin) => RuleSwapina(a),
   List(Swapin_L(), Swapin_R())) ++
                                (map[RuleSwapout,
                                      Rule]((a: RuleSwapout) => RuleSwapouta(a),
     List(Swapout_L(), Swapout_R())) ++
                                  map[RuleZer,
                                       Rule]((a: RuleZer) => RuleZera(a),
      List(Prem(), Partial(), Id(), Atom())))))))))))))))))

def pred_list[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && pred_list[A](p, xs)
}

def fresh_name_aux(x0: List[List[Char]], s: List[Char], uu: set[List[Char]]):
      List[Char]
  =
  (x0, s, uu) match {
  case (Nil, s, uu) => s
  case (x :: xs, s, full) =>
    (if (! (member[List[Char]](s ++ x, full))) s ++ x
      else fresh_name_aux(xs, s ++ x, full))
}

def fresh_name(list: List[List[Char]]): List[Char] =
  fresh_name_aux(list, List('X'), seta[List[Char]](list))

def less_eq_set[A : equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => pred_list[A]((y: A) => ! (member[A](y, a)), ys)
  case (seta(xs), b) => pred_list[A]((x: A) => member[A](x, b), xs)
}

def equal_set[A : equal](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

def collectPremises(x0: Prooftree): List[Sequent] = x0 match {
  case Prooftreea(p, RuleZera(Prem()), Nil) => List(p)
  case Prooftreea(uu, RuleMacro(uv, pt), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleBigcommaa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleCuta(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleDispa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleDispActa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleDispKa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleGrisha(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleKnowledgea(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleOpa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleOpActa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleOpKa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleStructa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleStructActa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleStructEAa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleStructKa(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleSwapina(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleSwapouta(v), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(Atom()), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(Id()), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(Partial()), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, Fail(), list) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            list)).apply(Nil)
  case Prooftreea(uw, RuleZera(vb), v :: va) =>
    (foldr[Prooftree,
            List[Sequent]](comp[List[Sequent], (List[Sequent]) => List[Sequent],
                                 Prooftree]((a: List[Sequent]) =>
      (b: List[Sequent]) => a ++ b,
     (a: Prooftree) => collectPremises(a)),
                            v :: va)).apply(Nil)
}

def collectPremisesToLocale(pt: Prooftree): List[Locale] =
  map[Sequent, Locale]((a: Sequent) => Premise(a), collectPremises(pt))

def isProofTree(loc: List[Locale], x1: Prooftree): Boolean = (loc, x1) match {
  case (loc, Prooftreea(s, RuleMacro(n, pt), ptlist)) =>
    equal_Sequenta(s, concl(pt)) &&
      (isProofTree(loc ++ collectPremisesToLocale(pt), pt) &&
        (equal_set[Sequent](seta[Sequent](collectPremises(pt)),
                             seta[Sequent](map[Prooftree,
        Sequent]((a: Prooftree) => concl(a), ptlist))) &&
          (foldr[Prooftree,
                  Boolean](comp[Boolean, Boolean => Boolean,
                                 Prooftree]((a: Boolean) =>
      (b: Boolean) => a && b,
     (a: Prooftree) => isProofTree(loc, a)),
                            ptlist)).apply(true)))
  case (loc, Prooftreea(s, RuleBigcommaa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleBigcommaa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleBigcommaa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleCuta(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleCuta(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleCuta(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleDispa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleDispa(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleDispa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleDispActa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleDispActa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleDispActa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleDispKa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleDispKa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleDispKa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleGrisha(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleGrisha(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleGrisha(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleKnowledgea(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleKnowledgea(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleKnowledgea(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleOpa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleOpa(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleOpa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleOpActa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleOpActa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleOpActa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleOpKa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleOpKa(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleOpKa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleStructa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleStructa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleStructa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleStructActa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleStructActa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleStructActa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleStructEAa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleStructEAa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleStructEAa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleStructKa(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleStructKa(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleStructKa(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleSwapina(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleSwapina(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleSwapina(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleSwapouta(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleSwapouta(v),
                   s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(),
                 fsta[Rule, List[Sequent]](der(x, RuleSwapouta(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, RuleZera(v), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule,
                                       List[Sequent]](der(x, RuleZera(v), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, RuleZera(v), s))))),
                        loc)).apply(false)
  case (loc, Prooftreea(s, Fail(), l)) =>
    (foldr[Prooftree,
            Boolean](comp[Boolean, Boolean => Boolean,
                           Prooftree]((a: Boolean) => (b: Boolean) => a && b,
                                       (a: Prooftree) => isProofTree(loc, a)),
                      l)).apply(true) &&
      (foldr[Locale,
              Boolean](comp[Boolean, Boolean => Boolean,
                             Locale]((a: Boolean) => (b: Boolean) => a || b,
                                      (x: Locale) =>
equal_set[Sequent](seta[Sequent](snda[Rule, List[Sequent]](der(x, Fail(), s))),
                    seta[Sequent](map[Prooftree,
                                       Sequent]((a: Prooftree) => concl(a),
         l))) &&
  ! (equal_Rule(Fail(), fsta[Rule, List[Sequent]](der(x, Fail(), s))))),
                        loc)).apply(false)
}

def rulifyAgent(x0: Agent): Agent = x0 match {
  case Agenta(a) => Agent_Freevar(a)
  case Agent_Freevar(a) => Agent_Freevar(a)
}

def ms_lesseq_impl[A : equal](x0: List[A], ys: List[A]): Option[Boolean] =
  (x0, ys) match {
  case (Nil, ys) => Some[Boolean](! (nulla[A](ys)))
  case (x :: xs, ys) =>
    (extract[A]((a: A) => eq[A](x, a), ys) match {
       case None => None
       case Some((ys1, (_, ys2))) => ms_lesseq_impl[A](xs, ys1 ++ ys2)
     })
}

def equal_multiset[A : equal](x0: multiset[A], x1: multiset[A]): Boolean =
  (x0, x1) match {
  case (multiset_of(xs), multiset_of(ys)) =>
    equal_option[Boolean](ms_lesseq_impl[A](xs, ys), Some[Boolean](false))
}

def collect_freevars_Structure(x0: Structure): List[Structure] = x0 match {
  case Structure_Formula(f) => List(Structure_Formula(f))
  case Structure_Bin(l, uu, r) =>
    collect_freevars_Structure(l) ++ collect_freevars_Structure(r)
  case Structure_Freevar(free) => List(Structure_Freevar(free))
  case Structure_Action_Structure(oper, ac, struct) =>
    List(Structure_Formula(Formula_Action(ac))) ++
      collect_freevars_Structure(struct)
  case Structure_Agent_Structure(oper, ag, struct) =>
    List(Structure_Formula(Formula_Agent(ag))) ++
      collect_freevars_Structure(struct)
  case Structure_Phi(a) => List(Structure_Phi(a))
  case Structure_Zer(z) => List(Structure_Zer(z))
  case Structure_Bigcomma(list) =>
    (foldr[Structure,
            List[Structure]](comp[List[Structure],
                                   (List[Structure]) => List[Structure],
                                   Structure]((a: List[Structure]) =>
        (b: List[Structure]) => a ++ b,
       (a: Structure) => collect_freevars_Structure(a)),
                              list)).apply(Nil)
}

def collect_freevars_Sequent(x0: Sequent): List[Structure] = x0 match {
  case Sequenta(l, r) =>
    collect_freevars_Structure(l) ++ collect_freevars_Structure(r)
  case Sequent_Structure(uu) => Nil
}

def is_display_rule(r: Rule): List[Rule] =
  (if (((snd(rule(Empty(), r))).apply(fst(rule(Empty(), r))) match {
          case None => false
          case Some(Nil) => false
          case Some(h :: _) =>
            equal_multiset[Structure](multiset_of[Structure](collect_freevars_Sequent(fst(rule(Empty(),
                r)))),
                                       multiset_of[Structure](collect_freevars_Sequent(h)))
        }))
    List(r) else Nil)

def displayRules: List[Rule] =
  (foldr[Rule,
          List[Rule]](comp[List[Rule], (List[Rule]) => List[Rule],
                            Rule]((a: List[Rule]) => (b: List[Rule]) => a ++ b,
                                   (a: Rule) => is_display_rule(a)),
                       ruleList)).apply(Nil)

def structure_Op_polarity(x0: Structure_Bin_Op): (polarity, polarity) = x0 match
  {
  case Structure_Comma() => (Plus(), Plus())
  case Structure_ImpL() => (Plus(), Minus())
  case Structure_ImpR() => (Minus(), Plus())
}

def polarity_weird_xor(xa0: polarity, x: polarity): polarity = (xa0, x) match {
  case (Plus(), N()) => Plus()
  case (Minus(), N()) => Minus()
  case (N(), x) => x
  case (Plus(), Plus()) => N()
  case (Plus(), Minus()) => N()
  case (Minus(), Plus()) => N()
  case (Minus(), Minus()) => N()
}

def polarity_not(x0: polarity): polarity = x0 match {
  case Minus() => Plus()
  case Plus() => Minus()
  case N() => N()
}

def polarity_weird_and(xa0: polarity, x: polarity): polarity = (xa0, x) match {
  case (Minus(), x) => polarity_not(x)
  case (Plus(), x) => x
  case (N(), uu) => N()
}

def polarity_Structure(s: Structure, x1: Structure): polarity = (s, x1) match {
  case (s, Structure_Bin(l, oper, r)) =>
    (if (equal_Structurea(l, s))
      fsta[polarity, polarity](structure_Op_polarity(oper))
      else (if (equal_Structurea(r, s))
             snda[polarity, polarity](structure_Op_polarity(oper))
             else polarity_weird_xor(polarity_weird_and(fsta[polarity,
                      polarity](structure_Op_polarity(oper)),
                 polarity_Structure(s, l)),
                                      polarity_weird_and(snda[polarity,
                       polarity](structure_Op_polarity(oper)),
                  polarity_Structure(s, r)))))
  case (s, Structure_Action_Structure(oper, ac, struct)) =>
    polarity_Structure(s, struct)
  case (s, Structure_Agent_Structure(oper, ag, struct)) =>
    polarity_Structure(s, struct)
  case (s, Structure_Bigcomma(v)) =>
    (if (equal_Structurea(s, Structure_Bigcomma(v))) Plus() else N())
  case (s, Structure_Formula(v)) =>
    (if (equal_Structurea(s, Structure_Formula(v))) Plus() else N())
  case (s, Structure_Freevar(v)) =>
    (if (equal_Structurea(s, Structure_Freevar(v))) Plus() else N())
  case (s, Structure_Phi(v)) =>
    (if (equal_Structurea(s, Structure_Phi(v))) Plus() else N())
  case (s, Structure_Zer(v)) =>
    (if (equal_Structurea(s, Structure_Zer(v))) Plus() else N())
}

def partial_goal(s: Structure, x1: Structure): Structure = (s, x1) match {
  case (s, Structure_Bin(l, oper, r)) =>
    (polarity_Structure(s, l) match {
       case Plus() => l
       case Minus() => l
       case N() => (if (equal_Structurea(s, l)) l else r)
     })
  case (s, Structure_Action_Structure(oper, ac, struct)) => struct
  case (s, Structure_Agent_Structure(oper, ag, struct)) => struct
  case (s, Structure_Bigcomma(v)) => Structure_Bigcomma(v)
  case (s, Structure_Formula(v)) => Structure_Formula(v)
  case (s, Structure_Freevar(v)) => Structure_Freevar(v)
  case (s, Structure_Phi(v)) => Structure_Phi(v)
  case (s, Structure_Zer(v)) => Structure_Zer(v)
}

def rulifyAction(x0: Action): Action = x0 match {
  case Actiona(a) => Action_Freevar(a)
  case Action_Freevar(a) => Action_Freevar(a)
}

def replaceIntoPT_list(list: List[(Sequent, Sequent)], x1: List[Prooftree]):
      List[Prooftree]
  =
  (list, x1) match {
  case (list, Nil) => Nil
  case (list, l :: ist) =>
    replaceIntoPT_aux(list, l) :: replaceIntoPT_list(list, ist)
}

def replaceIntoPT_aux(list: List[(Sequent, Sequent)], x1: Prooftree): Prooftree
  =
  (list, x1) match {
  case (list, Prooftreea(c, RuleMacro(s, pt), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c),
                RuleMacro(s, replaceIntoPT_aux(list, pt)),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleBigcommaa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleBigcommaa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleCuta(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleCuta(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleDispa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleDispa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleDispActa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleDispActa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleDispKa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleDispKa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleGrisha(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleGrisha(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleKnowledgea(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleKnowledgea(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleOpa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleOpa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleOpActa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleOpActa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleOpKa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleOpKa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleStructa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleStructa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleStructActa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleStructActa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleStructEAa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleStructEAa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleStructKa(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleStructKa(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleSwapina(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleSwapina(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleSwapouta(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleSwapouta(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, RuleZera(v), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), RuleZera(v),
                replaceIntoPT_list(list, ptlist))
  case (list, Prooftreea(c, Fail(), ptlist)) =>
    Prooftreea(replaceAll[Sequent](list, c), Fail(),
                replaceIntoPT_list(list, ptlist))
}

def replaceIntoPT(seq: Sequent, x1: Prooftree): Prooftree = (seq, x1) match {
  case (seq, Prooftreea(c, r, ptlist)) =>
    replaceIntoPT_aux(match_Sequent(c, seq), Prooftreea(c, r, ptlist))
}

def rulifyFormula(x0: Formula): Formula = x0 match {
  case Formula_Atprop(Atpropa(f :: a)) =>
    (if ('A' <= f && f <= 'Z') Formula_Freevar(f :: a)
      else Formula_Atprop(Atprop_Freevar(f :: a)))
  case Formula_Bin(x, c, y) =>
    Formula_Bin(rulifyFormula(x), c, rulifyFormula(y))
  case Formula_Agent_Formula(c, a, x) =>
    Formula_Agent_Formula(c, rulifyAgent(a), rulifyFormula(x))
  case Formula_Action_Formula(c, a, x) =>
    Formula_Action_Formula(c, rulifyAction(a), rulifyFormula(x))
  case Formula_Precondition(a) => Formula_Precondition(rulifyAction(a))
  case Formula_Action(v) => Formula_Action(v)
  case Formula_Agent(v) => Formula_Agent(v)
  case Formula_Atprop(Atpropa(Nil)) => Formula_Atprop(Atpropa(Nil))
  case Formula_Atprop(Atprop_Freevar(va)) => Formula_Atprop(Atprop_Freevar(va))
  case Formula_Freevar(v) => Formula_Freevar(v)
  case Formula_Zer(v) => Formula_Zer(v)
}

def rulifyStructure(x0: Structure): Structure = x0 match {
  case Structure_Formula(Formula_Atprop(Atpropa(f :: a))) =>
    (if ('A' <= f && f <= 'Z')
      (if (f == 'F') Structure_Formula(Formula_Freevar(f :: a))
        else Structure_Freevar(f :: a))
      else Structure_Formula(Formula_Atprop(Atprop_Freevar(f :: a))))
  case Structure_Formula(Formula_Action(v)) =>
    Structure_Formula(rulifyFormula(Formula_Action(v)))
  case Structure_Formula(Formula_Action_Formula(v, va, vb)) =>
    Structure_Formula(rulifyFormula(Formula_Action_Formula(v, va, vb)))
  case Structure_Formula(Formula_Agent(v)) =>
    Structure_Formula(rulifyFormula(Formula_Agent(v)))
  case Structure_Formula(Formula_Agent_Formula(v, va, vb)) =>
    Structure_Formula(rulifyFormula(Formula_Agent_Formula(v, va, vb)))
  case Structure_Formula(Formula_Atprop(Atpropa(Nil))) =>
    Structure_Formula(rulifyFormula(Formula_Atprop(Atpropa(Nil))))
  case Structure_Formula(Formula_Atprop(Atprop_Freevar(va))) =>
    Structure_Formula(rulifyFormula(Formula_Atprop(Atprop_Freevar(va))))
  case Structure_Formula(Formula_Bin(v, va, vb)) =>
    Structure_Formula(rulifyFormula(Formula_Bin(v, va, vb)))
  case Structure_Formula(Formula_Freevar(v)) =>
    Structure_Formula(rulifyFormula(Formula_Freevar(v)))
  case Structure_Formula(Formula_Precondition(v)) =>
    Structure_Formula(rulifyFormula(Formula_Precondition(v)))
  case Structure_Formula(Formula_Zer(v)) =>
    Structure_Formula(rulifyFormula(Formula_Zer(v)))
  case Structure_Bin(x, c, y) =>
    Structure_Bin(rulifyStructure(x), c, rulifyStructure(y))
  case Structure_Agent_Structure(c, a, x) =>
    Structure_Agent_Structure(c, rulifyAgent(a), rulifyStructure(x))
  case Structure_Action_Structure(c, a, x) =>
    Structure_Action_Structure(c, rulifyAction(a), rulifyStructure(x))
  case Structure_Bigcomma(list) =>
    Structure_Bigcomma(map[Structure,
                            Structure]((a: Structure) => rulifyStructure(a),
list))
  case Structure_Phi(a) => Structure_Phi(rulifyAction(a))
  case Structure_Freevar(v) => Structure_Freevar(v)
  case Structure_Zer(v) => Structure_Zer(v)
}

def rulifySequent(x0: Sequent): Sequent = x0 match {
  case Sequenta(x, y) => Sequenta(rulifyStructure(x), rulifyStructure(y))
  case Sequent_Structure(x) => Sequent_Structure(x)
}

def replaceIntoProoftree(list: List[Prooftree], x1: Prooftree): Prooftree =
  (list, x1) match {
  case (Nil, Prooftreea(s, RuleZera(Prem()), Nil)) =>
    Prooftreea(s, RuleZera(Prem()), Nil)
  case (l :: ist, Prooftreea(s, RuleZera(Prem()), Nil)) =>
    (if (equal_Sequenta(concl(l), s)) l
      else replaceIntoProoftree(ist, Prooftreea(s, RuleZera(Prem()), Nil)))
  case (v :: va, Prooftreea(s, RuleBigcommaa(vb), Nil)) =>
    Prooftreea(s, RuleBigcommaa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleCuta(vb), Nil)) =>
    Prooftreea(s, RuleCuta(vb), Nil)
  case (v :: va, Prooftreea(s, RuleDispa(vb), Nil)) =>
    Prooftreea(s, RuleDispa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleDispActa(vb), Nil)) =>
    Prooftreea(s, RuleDispActa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleDispKa(vb), Nil)) =>
    Prooftreea(s, RuleDispKa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleGrisha(vb), Nil)) =>
    Prooftreea(s, RuleGrisha(vb), Nil)
  case (v :: va, Prooftreea(s, RuleKnowledgea(vb), Nil)) =>
    Prooftreea(s, RuleKnowledgea(vb), Nil)
  case (v :: va, Prooftreea(s, RuleOpa(vb), Nil)) =>
    Prooftreea(s, RuleOpa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleOpActa(vb), Nil)) =>
    Prooftreea(s, RuleOpActa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleOpKa(vb), Nil)) =>
    Prooftreea(s, RuleOpKa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleStructa(vb), Nil)) =>
    Prooftreea(s, RuleStructa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleStructActa(vb), Nil)) =>
    Prooftreea(s, RuleStructActa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleStructEAa(vb), Nil)) =>
    Prooftreea(s, RuleStructEAa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleStructKa(vb), Nil)) =>
    Prooftreea(s, RuleStructKa(vb), Nil)
  case (v :: va, Prooftreea(s, RuleSwapina(vb), Nil)) =>
    Prooftreea(s, RuleSwapina(vb), Nil)
  case (v :: va, Prooftreea(s, RuleSwapouta(vb), Nil)) =>
    Prooftreea(s, RuleSwapouta(vb), Nil)
  case (v :: va, Prooftreea(s, RuleZera(Atom()), Nil)) =>
    Prooftreea(s, RuleZera(Atom()), Nil)
  case (v :: va, Prooftreea(s, RuleZera(Id()), Nil)) =>
    Prooftreea(s, RuleZera(Id()), Nil)
  case (v :: va, Prooftreea(s, RuleZera(Partial()), Nil)) =>
    Prooftreea(s, RuleZera(Partial()), Nil)
  case (v :: va, Prooftreea(s, RuleMacro(vb, vc), Nil)) =>
    Prooftreea(s, RuleMacro(vb, vc), Nil)
  case (v :: va, Prooftreea(s, Fail(), Nil)) => Prooftreea(s, Fail(), Nil)
  case (list, Prooftreea(s, RuleBigcommaa(v), Nil)) =>
    Prooftreea(s, RuleBigcommaa(v), Nil)
  case (list, Prooftreea(s, RuleCuta(v), Nil)) =>
    Prooftreea(s, RuleCuta(v), Nil)
  case (list, Prooftreea(s, RuleDispa(v), Nil)) =>
    Prooftreea(s, RuleDispa(v), Nil)
  case (list, Prooftreea(s, RuleDispActa(v), Nil)) =>
    Prooftreea(s, RuleDispActa(v), Nil)
  case (list, Prooftreea(s, RuleDispKa(v), Nil)) =>
    Prooftreea(s, RuleDispKa(v), Nil)
  case (list, Prooftreea(s, RuleGrisha(v), Nil)) =>
    Prooftreea(s, RuleGrisha(v), Nil)
  case (list, Prooftreea(s, RuleKnowledgea(v), Nil)) =>
    Prooftreea(s, RuleKnowledgea(v), Nil)
  case (list, Prooftreea(s, RuleOpa(v), Nil)) => Prooftreea(s, RuleOpa(v), Nil)
  case (list, Prooftreea(s, RuleOpActa(v), Nil)) =>
    Prooftreea(s, RuleOpActa(v), Nil)
  case (list, Prooftreea(s, RuleOpKa(v), Nil)) =>
    Prooftreea(s, RuleOpKa(v), Nil)
  case (list, Prooftreea(s, RuleStructa(v), Nil)) =>
    Prooftreea(s, RuleStructa(v), Nil)
  case (list, Prooftreea(s, RuleStructActa(v), Nil)) =>
    Prooftreea(s, RuleStructActa(v), Nil)
  case (list, Prooftreea(s, RuleStructEAa(v), Nil)) =>
    Prooftreea(s, RuleStructEAa(v), Nil)
  case (list, Prooftreea(s, RuleStructKa(v), Nil)) =>
    Prooftreea(s, RuleStructKa(v), Nil)
  case (list, Prooftreea(s, RuleSwapina(v), Nil)) =>
    Prooftreea(s, RuleSwapina(v), Nil)
  case (list, Prooftreea(s, RuleSwapouta(v), Nil)) =>
    Prooftreea(s, RuleSwapouta(v), Nil)
  case (list, Prooftreea(s, RuleZera(Atom()), Nil)) =>
    Prooftreea(s, RuleZera(Atom()), Nil)
  case (list, Prooftreea(s, RuleZera(Id()), Nil)) =>
    Prooftreea(s, RuleZera(Id()), Nil)
  case (list, Prooftreea(s, RuleZera(Partial()), Nil)) =>
    Prooftreea(s, RuleZera(Partial()), Nil)
  case (list, Prooftreea(s, RuleMacro(v, va), Nil)) =>
    Prooftreea(s, RuleMacro(v, va), Nil)
  case (list, Prooftreea(s, Fail(), Nil)) => Prooftreea(s, Fail(), Nil)
  case (v :: va, Prooftreea(s, RuleBigcommaa(vb), vc :: vd)) =>
    Prooftreea(s, RuleBigcommaa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleCuta(vb), vc :: vd)) =>
    Prooftreea(s, RuleCuta(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleDispa(vb), vc :: vd)) =>
    Prooftreea(s, RuleDispa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleDispActa(vb), vc :: vd)) =>
    Prooftreea(s, RuleDispActa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleDispKa(vb), vc :: vd)) =>
    Prooftreea(s, RuleDispKa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleGrisha(vb), vc :: vd)) =>
    Prooftreea(s, RuleGrisha(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleKnowledgea(vb), vc :: vd)) =>
    Prooftreea(s, RuleKnowledgea(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleOpa(vb), vc :: vd)) =>
    Prooftreea(s, RuleOpa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleOpActa(vb), vc :: vd)) =>
    Prooftreea(s, RuleOpActa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleOpKa(vb), vc :: vd)) =>
    Prooftreea(s, RuleOpKa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleStructa(vb), vc :: vd)) =>
    Prooftreea(s, RuleStructa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleStructActa(vb), vc :: vd)) =>
    Prooftreea(s, RuleStructActa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleStructEAa(vb), vc :: vd)) =>
    Prooftreea(s, RuleStructEAa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleStructKa(vb), vc :: vd)) =>
    Prooftreea(s, RuleStructKa(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleSwapina(vb), vc :: vd)) =>
    Prooftreea(s, RuleSwapina(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleSwapouta(vb), vc :: vd)) =>
    Prooftreea(s, RuleSwapouta(vb),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vc :: vd))
  case (v :: va, Prooftreea(s, RuleZera(Atom()), vb :: vc)) =>
    Prooftreea(s, RuleZera(Atom()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, RuleZera(Id()), vb :: vc)) =>
    Prooftreea(s, RuleZera(Id()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, RuleZera(Partial()), vb :: vc)) =>
    Prooftreea(s, RuleZera(Partial()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, RuleMacro(vb, vc), vd :: ve)) =>
    Prooftreea(s, RuleMacro(vb, vc),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vd :: ve))
  case (v :: va, Prooftreea(s, Fail(), vb :: vc)) =>
    Prooftreea(s, Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (v :: va, Prooftreea(s, r, vb :: vc)) =>
    Prooftreea(s, r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(v :: va, a),
                                 vb :: vc))
  case (list, Prooftreea(s, RuleBigcommaa(v), va :: vb)) =>
    Prooftreea(s, RuleBigcommaa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleCuta(v), va :: vb)) =>
    Prooftreea(s, RuleCuta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleDispa(v), va :: vb)) =>
    Prooftreea(s, RuleDispa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleDispActa(v), va :: vb)) =>
    Prooftreea(s, RuleDispActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleDispKa(v), va :: vb)) =>
    Prooftreea(s, RuleDispKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleGrisha(v), va :: vb)) =>
    Prooftreea(s, RuleGrisha(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleKnowledgea(v), va :: vb)) =>
    Prooftreea(s, RuleKnowledgea(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleOpa(v), va :: vb)) =>
    Prooftreea(s, RuleOpa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleOpActa(v), va :: vb)) =>
    Prooftreea(s, RuleOpActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleOpKa(v), va :: vb)) =>
    Prooftreea(s, RuleOpKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleStructa(v), va :: vb)) =>
    Prooftreea(s, RuleStructa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleStructActa(v), va :: vb)) =>
    Prooftreea(s, RuleStructActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleStructEAa(v), va :: vb)) =>
    Prooftreea(s, RuleStructEAa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleStructKa(v), va :: vb)) =>
    Prooftreea(s, RuleStructKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleSwapina(v), va :: vb)) =>
    Prooftreea(s, RuleSwapina(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleSwapouta(v), va :: vb)) =>
    Prooftreea(s, RuleSwapouta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 va :: vb))
  case (list, Prooftreea(s, RuleZera(Atom()), v :: va)) =>
    Prooftreea(s, RuleZera(Atom()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, RuleZera(Id()), v :: va)) =>
    Prooftreea(s, RuleZera(Id()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, RuleZera(Partial()), v :: va)) =>
    Prooftreea(s, RuleZera(Partial()),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, RuleMacro(v, va), vb :: vc)) =>
    Prooftreea(s, RuleMacro(v, va),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 vb :: vc))
  case (list, Prooftreea(s, Fail(), v :: va)) =>
    Prooftreea(s, Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
  case (list, Prooftreea(s, r, v :: va)) =>
    Prooftreea(s, r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) => replaceIntoProoftree(list, a),
                                 v :: va))
}

def expandProoftree(x0: Prooftree): Prooftree = x0 match {
  case Prooftreea(uu, RuleMacro(n, Prooftreea(s, r, l)), list) =>
    Prooftreea(s, r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replaceIntoProoftree(map[Prooftree,
                    Prooftree]((aa: Prooftree) => expandProoftree(aa), list),
                a),
                                 map[Prooftree,
                                      Prooftree]((a: Prooftree) =>
           expandProoftree(a),
          l)))
  case Prooftreea(s, RuleBigcommaa(v), list) =>
    Prooftreea(s, RuleBigcommaa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleCuta(v), list) =>
    Prooftreea(s, RuleCuta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleDispa(v), list) =>
    Prooftreea(s, RuleDispa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleDispActa(v), list) =>
    Prooftreea(s, RuleDispActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleDispKa(v), list) =>
    Prooftreea(s, RuleDispKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleGrisha(v), list) =>
    Prooftreea(s, RuleGrisha(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleKnowledgea(v), list) =>
    Prooftreea(s, RuleKnowledgea(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleOpa(v), list) =>
    Prooftreea(s, RuleOpa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleOpActa(v), list) =>
    Prooftreea(s, RuleOpActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleOpKa(v), list) =>
    Prooftreea(s, RuleOpKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleStructa(v), list) =>
    Prooftreea(s, RuleStructa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleStructActa(v), list) =>
    Prooftreea(s, RuleStructActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleStructEAa(v), list) =>
    Prooftreea(s, RuleStructEAa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleStructKa(v), list) =>
    Prooftreea(s, RuleStructKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleSwapina(v), list) =>
    Prooftreea(s, RuleSwapina(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleSwapouta(v), list) =>
    Prooftreea(s, RuleSwapouta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, RuleZera(v), list) =>
    Prooftreea(s, RuleZera(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
  case Prooftreea(s, Fail(), list) =>
    Prooftreea(s, Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => expandProoftree(a), list))
}

def rulifyProoftree(x0: Prooftree): Prooftree = x0 match {
  case Prooftreea(s, RuleMacro(str, pt), list) =>
    Prooftreea(rulifySequent(s), RuleMacro(str, rulifyProoftree(pt)),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleBigcommaa(v), list) =>
    Prooftreea(rulifySequent(s), RuleBigcommaa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleCuta(v), list) =>
    Prooftreea(rulifySequent(s), RuleCuta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleDispa(v), list) =>
    Prooftreea(rulifySequent(s), RuleDispa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleDispActa(v), list) =>
    Prooftreea(rulifySequent(s), RuleDispActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleDispKa(v), list) =>
    Prooftreea(rulifySequent(s), RuleDispKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleGrisha(v), list) =>
    Prooftreea(rulifySequent(s), RuleGrisha(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleKnowledgea(v), list) =>
    Prooftreea(rulifySequent(s), RuleKnowledgea(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleOpa(v), list) =>
    Prooftreea(rulifySequent(s), RuleOpa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleOpActa(v), list) =>
    Prooftreea(rulifySequent(s), RuleOpActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleOpKa(v), list) =>
    Prooftreea(rulifySequent(s), RuleOpKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleStructa(v), list) =>
    Prooftreea(rulifySequent(s), RuleStructa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleStructActa(v), list) =>
    Prooftreea(rulifySequent(s), RuleStructActa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleStructEAa(v), list) =>
    Prooftreea(rulifySequent(s), RuleStructEAa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleStructKa(v), list) =>
    Prooftreea(rulifySequent(s), RuleStructKa(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleSwapina(v), list) =>
    Prooftreea(rulifySequent(s), RuleSwapina(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleSwapouta(v), list) =>
    Prooftreea(rulifySequent(s), RuleSwapouta(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, RuleZera(v), list) =>
    Prooftreea(rulifySequent(s), RuleZera(v),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
  case Prooftreea(s, Fail(), list) =>
    Prooftreea(rulifySequent(s), Fail(),
                map[Prooftree,
                     Prooftree]((a: Prooftree) => rulifyProoftree(a), list))
}

def polarity_Sequent(s: Structure, x1: Sequent): polarity = (s, x1) match {
  case (s, Sequenta(lhs, rhs)) =>
    polarity_weird_xor(polarity_not(polarity_Structure(s, lhs)),
                        polarity_Structure(s, rhs))
  case (s, Sequent_Structure(v)) => N()
}

def collectCutFormulas(x0: Prooftree): List[Formula] = x0 match {
  case Prooftreea(uu, RuleCuta(uv), List(l, r)) =>
    (consq(concl(l)) match {
       case Structure_Action_Structure(_, _, _) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Agent_Structure(_, _, _) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Bigcomma(_) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Bin(_, _, _) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Formula(f) =>
         (ant(concl(r)) match {
            case Structure_Action_Structure(_, _, _) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Agent_Structure(_, _, _) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Bigcomma(_) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Bin(_, _, _) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Formula(fa) =>
              (if (equal_Formulaa(f, fa))
                List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                else collectCutFormulas(l) ++ collectCutFormulas(r))
            case Structure_Freevar(_) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Phi(_) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
            case Structure_Zer(_) =>
              collectCutFormulas(l) ++ collectCutFormulas(r)
          })
       case Structure_Freevar(_) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Phi(_) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
       case Structure_Zer(_) =>
         {
           val (Structure_Formula(f)): Structure = consq(concl(r));
           (ant(concl(l)) match {
              case Structure_Action_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Agent_Structure(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bigcomma(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Bin(_, _, _) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Formula(fa) =>
                (if (equal_Formulaa(f, fa))
                  List(f) ++ (collectCutFormulas(l) ++ collectCutFormulas(r))
                  else collectCutFormulas(l) ++ collectCutFormulas(r))
              case Structure_Freevar(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Phi(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
              case Structure_Zer(_) =>
                collectCutFormulas(l) ++ collectCutFormulas(r)
            })
         }
     })
  case Prooftreea(uw, RuleMacro(ux, pt), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(collectCutFormulas(pt))
  case Prooftreea(uy, RuleBigcommaa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleDispa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleDispActa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleDispKa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleGrisha(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleKnowledgea(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleOpa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleOpActa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleOpKa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleStructa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleStructActa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleStructEAa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleStructKa(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleSwapina(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleSwapouta(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleZera(v), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, Fail(), list) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            list)).apply(Nil)
  case Prooftreea(uy, RuleCuta(v), Nil) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            Nil)).apply(Nil)
  case Prooftreea(uy, RuleCuta(va), List(v)) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            List(v))).apply(Nil)
  case Prooftreea(uy, RuleCuta(va), v :: vb :: vd :: ve) =>
    (foldr[Prooftree,
            List[Formula]](comp[List[Formula], (List[Formula]) => List[Formula],
                                 Prooftree]((a: List[Formula]) =>
      (b: List[Formula]) => a ++ b,
     (a: Prooftree) => collectCutFormulas(a)),
                            v :: vb :: vd :: ve)).apply(Nil)
}

def collectCutFormulasToLocale(pt: Prooftree): List[Locale] =
  map[Formula, Locale]((a: Formula) => CutFormula(a), collectCutFormulas(pt))

def isProofTreeWithCut(loc: List[Locale], pt: Prooftree): Boolean =
  isProofTree(loc ++ collectCutFormulasToLocale(pt), pt)

def collect_SFAtprop_names(x0: Structure): List[List[Char]] = x0 match {
  case Structure_Formula(Formula_Atprop(Atpropa(x))) => List(x)
  case Structure_Bin(l, oper, r) =>
    collect_SFAtprop_names(l) ++ collect_SFAtprop_names(r)
  case Structure_Action_Structure(oper, ac, struct) =>
    collect_SFAtprop_names(struct)
  case Structure_Agent_Structure(oper, ag, struct) =>
    collect_SFAtprop_names(struct)
  case Structure_Bigcomma(v) => Nil
  case Structure_Formula(Formula_Action(va)) => Nil
  case Structure_Formula(Formula_Action_Formula(va, vb, vc)) => Nil
  case Structure_Formula(Formula_Agent(va)) => Nil
  case Structure_Formula(Formula_Agent_Formula(va, vb, vc)) => Nil
  case Structure_Formula(Formula_Atprop(Atprop_Freevar(vb))) => Nil
  case Structure_Formula(Formula_Bin(va, vb, vc)) => Nil
  case Structure_Formula(Formula_Freevar(va)) => Nil
  case Structure_Formula(Formula_Precondition(va)) => Nil
  case Structure_Formula(Formula_Zer(va)) => Nil
  case Structure_Freevar(v) => Nil
  case Structure_Phi(v) => Nil
  case Structure_Zer(v) => Nil
}

def sequent_fresh_name(x0: Sequent): Structure = x0 match {
  case Sequenta(l, r) =>
    Structure_Formula(Formula_Atprop(Atpropa(fresh_name(collect_SFAtprop_names(l) ++
                  collect_SFAtprop_names(r)))))
  case Sequent_Structure(v) =>
    Structure_Formula(Formula_Atprop(Atpropa(List('X'))))
}

def equal_polarity(x0: polarity, x1: polarity): Boolean = (x0, x1) match {
  case (Minus(), N()) => false
  case (N(), Minus()) => false
  case (Plus(), N()) => false
  case (N(), Plus()) => false
  case (Plus(), Minus()) => false
  case (Minus(), Plus()) => false
  case (N(), N()) => true
  case (Minus(), Minus()) => true
  case (Plus(), Plus()) => true
}

def position_in_Sequent(s: Structure, x1: Sequent): polarity = (s, x1) match {
  case (s, Sequenta(l, r)) =>
    (if (equal_Structurea(s, l)) Minus()
      else (if (! (equal_polarity(polarity_Structure(s, l), N()))) Minus()
             else (if (equal_Structurea(s, r)) Plus()
                    else (if (! (equal_polarity(polarity_Structure(s, r), N())))
                           Plus() else N()))))
  case (s, Sequent_Structure(v)) => N()
}

def partial_goal_complement(s: Structure, x1: Structure): Structure = (s, x1)
  match {
  case (s, Structure_Bin(l, oper, r)) =>
    (polarity_Structure(s, l) match {
       case Plus() => r
       case Minus() => r
       case N() => (if (equal_Structurea(s, l)) r else l)
     })
  case (s, Structure_Action_Structure(oper, ac, struct)) => struct
  case (s, Structure_Agent_Structure(oper, ag, struct)) => struct
  case (s, Structure_Bigcomma(v)) => Structure_Bigcomma(v)
  case (s, Structure_Formula(v)) => Structure_Formula(v)
  case (s, Structure_Freevar(v)) => Structure_Freevar(v)
  case (s, Structure_Phi(v)) => Structure_Phi(v)
  case (s, Structure_Zer(v)) => Structure_Zer(v)
}

def replace_SFAtprop_into_Structure(sfa: Structure, repl: Structure,
                                     x2: Structure):
      Structure
  =
  (sfa, repl, x2) match {
  case (sfa, repl, Structure_Bin(l, oper, r)) =>
    Structure_Bin(replace_SFAtprop_into_Structure(sfa, repl, l), oper,
                   replace_SFAtprop_into_Structure(sfa, repl, r))
  case (sfa, repl, Structure_Action_Structure(oper, ac, struct)) =>
    Structure_Action_Structure(oper, ac,
                                replace_SFAtprop_into_Structure(sfa, repl,
                         struct))
  case (sfa, repl, Structure_Agent_Structure(oper, ag, struct)) =>
    Structure_Agent_Structure(oper, ag,
                               replace_SFAtprop_into_Structure(sfa, repl,
                        struct))
  case (sfa, repl, Structure_Bigcomma(v)) =>
    (if (equal_Structurea(sfa, Structure_Bigcomma(v))) repl
      else Structure_Bigcomma(v))
  case (sfa, repl, Structure_Formula(v)) =>
    (if (equal_Structurea(sfa, Structure_Formula(v))) repl
      else Structure_Formula(v))
  case (sfa, repl, Structure_Freevar(v)) =>
    (if (equal_Structurea(sfa, Structure_Freevar(v))) repl
      else Structure_Freevar(v))
  case (sfa, repl, Structure_Phi(v)) =>
    (if (equal_Structurea(sfa, Structure_Phi(v))) repl else Structure_Phi(v))
  case (sfa, repl, Structure_Zer(v)) =>
    (if (equal_Structurea(sfa, Structure_Zer(v))) repl else Structure_Zer(v))
}

def replace_SFAtprop_into_Sequent(sfa: Structure, repl: Structure, x2: Sequent):
      Sequent
  =
  (sfa, repl, x2) match {
  case (sfa, repl, Sequenta(l, r)) =>
    Sequenta(replace_SFAtprop_into_Structure(sfa, repl, l),
              replace_SFAtprop_into_Structure(sfa, repl, r))
  case (sfa, relp, Sequent_Structure(v)) => Sequent_Structure(v)
}

def replace_SFAtprop_into_PT(sfa: Structure, repl: Structure, x2: Prooftree):
      Prooftree
  =
  (sfa, repl, x2) match {
  case (sfa, repl, Prooftreea(s, r, list)) =>
    Prooftreea(replace_SFAtprop_into_Sequent(sfa, repl, s), r,
                map[Prooftree,
                     Prooftree]((a: Prooftree) =>
                                  replace_SFAtprop_into_PT(sfa, repl, a),
                                 list))
}

} /* object DEAK */
