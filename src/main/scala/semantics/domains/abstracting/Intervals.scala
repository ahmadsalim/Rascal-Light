package semantics.domains.abstracting

import semantics.domains.common.Lattice

sealed trait IntegerW
case object IntegerInf extends IntegerW
case class IntegerVal(value: Integer) extends IntegerW
case object IntegerNegInf extends IntegerW

object IntegerW {
  def <=(iw1: IntegerW, iw2: IntegerW): Boolean = (iw1, iw2) match {
    case (IntegerNegInf, _) => true
    case (_, IntegerInf) => true
    case (IntegerVal(v1), IntegerVal(v2)) => v1 <= v2
    case _ => false
  }

  def min(iw1: IntegerW, iw2: IntegerW): IntegerW = (iw1, iw2) match {
    case (IntegerNegInf, _) | (_, IntegerNegInf) => IntegerNegInf
    case (IntegerInf, _) => iw2
    case (_, IntegerInf) => iw1
    case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(Math.min(v1, v2))
  }


  def max(iw1: IntegerW, iw2: IntegerW): IntegerW = (iw1, iw2) match {
    case (IntegerInf, _) | (_, IntegerInf) => IntegerInf
    case (IntegerNegInf, _) => iw2
    case (_, IntegerNegInf) => iw1
    case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(Math.max(v1, v2))
  }

  def +(iw1: IntegerW, iw2: IntegerW): IntegerW = {
    require(!(iw1 == IntegerNegInf && iw2 == IntegerInf) && !(iw1 == IntegerInf && iw2 == IntegerNegInf))
    (iw1, iw2) match {
      case (IntegerNegInf, _) | (_, IntegerNegInf) => IntegerNegInf
      case (IntegerInf, _) | (_, IntegerInf)  => IntegerInf
      case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(v1 + v2)
    }
  }
}

case class Interval(lb: IntegerW, ub: IntegerW)

case class Intervals(mlb: IntegerW, mub: IntegerW) {
  require(IntegerW.<=(mlb, mub) && mub != IntegerNegInf && mlb != IntegerInf)

  implicit def IntervalLattice: Lattice[Interval] = new Lattice[Interval] {
    override def <=(i1: Interval, i2: Interval): Boolean =
      IntegerW.<=(i2.lb, i1.lb) && IntegerW.<=(i1.ub, i2.ub)

    override def bot: Interval = Interval(mub, mlb)

    override def isBot(i: Interval): Boolean = !IntegerW.<=(i.lb, i.ub)

    override def top: Interval = Interval(mlb, mub)

    override def lub(i1: Interval, i2: Interval): Interval =
      Interval(IntegerW.min(i1.lb, i2.lb), IntegerW.max(i1.ub, i2.ub))

    override def glb(i1: Interval, i2: Interval): Interval =
      Interval(IntegerW.max(i1.lb, i2.lb), IntegerW.max(i1.ub, i2.ub))

    override def widen(i1: Interval, i2: Interval, bound: Int): Interval = {
      val newlb = if (IntegerW.<=(i1.lb, i2.lb)) i1.lb else mlb
      val newub = if (IntegerW.<=(i2.ub, i1.ub)) i1.ub else mub
      Interval(newlb, newub)
    }
  }

  def +(i1: Interval, i2: Interval): Interval = {
    Interval(IntegerW.min(mub, IntegerW.+(i1.lb, i2.lb)), IntegerW.min(mub, IntegerW.+(i1.ub, i2.ub)))
  }
}

object Intervals {
  val Positive = Intervals(IntegerVal(0), IntegerInf)
}
