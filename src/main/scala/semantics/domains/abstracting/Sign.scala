package semantics.domains.abstracting

import semantics.domains._
import semantics.domains.common.Powerset.PowersetLattice
import semantics.domains.common.{ConcreteAbstractGalois, Lattice, Powerset}

sealed trait Sign
case object SignBot extends Sign
case object Neg extends Sign
case object NonPos extends Sign
case object Zero extends Sign
case object NonNeg extends Sign
case object Pos extends Sign
case object SignTop extends Sign

object Sign {
  implicit val SignLattice = new Lattice[Sign] {
    override def bot: Sign = SignBot

    override def top: Sign = SignTop

    override def lub(a1: Sign, a2: Sign): Sign = (a1, a2) match {
      case (SignBot, a) => a
      case (a, SignBot) => a
      case (SignTop, _) | (_, SignTop) => SignTop
      case (Neg, Zero) | (Zero, Neg) | (NonPos, Zero) | (Zero, NonPos) | (NonPos, Neg) | (Neg, NonPos) => NonPos
      case (Pos, Zero) | (Zero, Pos) | (NonNeg, Zero) | (Zero, NonNeg) | (NonNeg, Pos) | (Pos, NonNeg) => NonNeg
      case _ => if (a1 == a2) a1 else SignTop
    }

    override def glb(a1: Sign, a2: Sign): Sign = (a1, a2) match {
      case (SignBot, _) | (_, SignBot) => SignBot
      case (SignTop, a) => a
      case (a, SignTop) => a
      case (NonPos, Neg) | (Neg, NonPos) => Neg
      case (NonPos, Zero) | (Zero, NonPos) | (NonNeg, Zero) | (Zero, NonNeg) => Zero
      case (NonNeg, Pos) | (Pos, NonNeg) => Pos
      case _ => if (a1 == a2) a1 else SignBot
    }

    override def <=(a1: Sign, a2: Sign): Boolean = (a1, a2) match {
      case (SignBot, _) => true
      case (_, SignTop) => true
      case (Neg, NonPos) | (Zero, NonPos) => true
      case (Pos, NonNeg) | (Zero, NonNeg) => true
      case _ => a1 == a2
    }

    override def widen(a1: Sign, a2: Sign, depth: Int): Sign = lub(a1, a2)
  }

  implicit val IntSignGalois = new ConcreteAbstractGalois[Int, Sign] {
    override def alpha(dcs: Set[Int]): Sign =
      Lattice[Sign].lubs(dcs.map(i => if (i > 0) Pos else if (i < 0) Neg else Zero))

    override def gamma(da: Sign, bound: Int): Set[Int] = da match {
      case SignBot => Set()
      case Neg => (-bound to -1).toSet
      case NonPos => (-(bound - 1) to 0).toSet
      case Zero => Set(0)
      case NonNeg => (0 until bound).toSet
      case Pos => (1 to bound).toSet
      case SignTop =>
        val boundPos = bound / 2
        val boundNeg = bound - boundPos - 1
        (-boundNeg to boundPos).toSet
    }

    override def latticeC: Lattice[Set[Int]] = PowersetLattice

    override def latticeA: Lattice[Sign] = SignLattice
  }
}