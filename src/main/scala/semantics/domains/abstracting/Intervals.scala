package semantics.domains.abstracting

import semantics.domains.common.Lattice

sealed trait IntegerW
case object IntegerInf extends IntegerW {
  override def toString: String = "∞"
}
case class IntegerVal(value: Int) extends IntegerW {
  override def toString: String = value.toString
}
case object IntegerNegInf extends IntegerW {
  override def toString: String = "-∞"
}

object IntegerW {
  def <=(iw1: IntegerW, iw2: IntegerW): Boolean = (iw1, iw2) match {
    case (IntegerNegInf, _) => true
    case (_, IntegerInf) => true
    case (IntegerVal(v1), IntegerVal(v2)) => v1 <= v2
    case _ => false
  }

  def <(iw1: IntegerW, iw2: IntegerW): Boolean = <=(iw1, iw2) && iw1 != iw2

  private
  def min2(iw1: IntegerW, iw2: IntegerW): IntegerW = (iw1, iw2) match {
    case (IntegerNegInf, _) | (_, IntegerNegInf) => IntegerNegInf
    case (IntegerInf, _) => iw2
    case (_, IntegerInf) => iw1
    case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(Math.min(v1, v2))
  }

  def min(iws: IntegerW*): IntegerW = iws.fold(IntegerInf)(min2)

  private
  def max2(iw1: IntegerW, iw2: IntegerW): IntegerW = (iw1, iw2) match {
    case (IntegerInf, _) | (_, IntegerInf) => IntegerInf
    case (IntegerNegInf, _) => iw2
    case (_, IntegerNegInf) => iw1
    case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(Math.max(v1, v2))
  }

  def max(iws: IntegerW*): IntegerW = iws.fold(IntegerNegInf)(max2)

  def +(iw1: IntegerW, iw2: IntegerW): IntegerW = {
    require(!(iw1 == IntegerNegInf && iw2 == IntegerInf) && !(iw1 == IntegerInf && iw2 == IntegerNegInf))
    (iw1, iw2) match {
      case (IntegerNegInf, _) | (_, IntegerNegInf) => IntegerNegInf
      case (IntegerInf, _) | (_, IntegerInf)  => IntegerInf
      case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(v1 + v2)
    }
  }

  def -(iw1: IntegerW, iw2: IntegerW): IntegerW = {
    require(!(iw1 == IntegerNegInf && iw2 == IntegerInf) && !(iw1 == IntegerInf && iw2 == IntegerNegInf))
    (iw1, iw2) match {
      case (IntegerNegInf, _) | (_, IntegerInf) => IntegerNegInf
      case (IntegerInf, _) | (_, IntegerNegInf)=> IntegerInf
      case (IntegerVal(v1), IntegerVal(v2)) => IntegerVal(v1 - v2)
    }
  }

  private def sgn(iw: IntegerW): Int = iw match {
    case IntegerInf => 1
    case IntegerVal(value) =>
      if (value > 0) 1
      else if (value < 0) -1
      else 0
    case IntegerNegInf => -1
  }

  private def applySgn(iw: IntegerW, sign: Int): IntegerW = {
    require(-1 <= sign && sign <= 1)
    iw match {
      case IntegerInf =>
        sign match {
          case -1 => IntegerNegInf
          case 0 => IntegerVal(0)
          case 1 => IntegerInf
        }
      case IntegerVal(value) => IntegerVal(sign * value)
      case IntegerNegInf =>
        sign match {
          case -1 => IntegerInf
          case 0 => IntegerVal(0)
          case 1 => IntegerNegInf
        }
    }
  }

  private def absValue(iw: IntegerW): IntegerW = iw match {
    case IntegerInf | IntegerNegInf => IntegerInf
    case IntegerVal(value) => IntegerVal(Math.abs(value))
  }


  def *(iw1: IntegerW, iw2: IntegerW): IntegerW = {
    val absMult = (absValue(iw1), absValue(iw2)) match {
      case (IntegerInf, _) | (_, IntegerInf) => IntegerInf
      case (IntegerVal(i1), IntegerVal(i2)) => IntegerVal(i1 * i2)
      case _ => assert(false); throw new Exception("Unreachable")
    }
    val sign = sgn(iw1) * sgn(iw2)
    applySgn(absMult, sign)
  }

  def /(iw1: IntegerW, iw2: IntegerW): IntegerW = {
    require(iw2 != IntegerVal(0))
    val absDiv = (absValue(iw1), absValue(iw2)) match {
      case (IntegerInf, _) => IntegerInf
      case (_, IntegerInf) => IntegerVal(0)
      case (IntegerVal(i1), IntegerVal(i2)) => IntegerVal(i1 / i2)
      case _ => assert(false); throw new Exception("Unreachable")
    }
    val sign = sgn(iw1) * sgn(iw2)
    applySgn(absDiv, sign)
  }
}


case class Intervals(mlb: IntegerW = IntegerNegInf, mub: IntegerW = IntegerInf) {
  require(IntegerW.<=(mlb, mub) && mub != IntegerNegInf && mlb != IntegerInf)
  case class Interval(lb: IntegerW, ub: IntegerW) {
    override def toString: String = s"[$lb;$ub]"
  }

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
      val newlb = if (IntegerW.<(i2.lb, i1.lb)) mlb else i1.lb
      val newub = if (IntegerW.<(i1.ub, i2.ub)) mub else i1.ub
      Interval(newlb, newub)
    }
  }

  private
  def boundsAdjusted(iw: IntegerW): IntegerW = {
    IntegerW.max(mlb, IntegerW.min(mub, iw))
  }

  private
  def coerceBot(i: Interval): Interval =
    if (Lattice[Interval].isBot(i)) Lattice[Interval].bot else i

  def contains(i: Interval, iv: Int): Boolean = {
    IntegerW.<=(i.lb, IntegerVal(iv)) &&
      IntegerW.<=(IntegerVal(iv), i.ub)
  }

  def exclude(i: Interval, iw: IntegerW): Interval = {
    val res = if (i.lb  == iw) {
      if (iw == i.ub) Lattice[Interval].bot
      else Interval(IntegerW.+(i.lb, IntegerVal(1)), i.ub)
    } else if (iw == i.ub) {
      Interval(i.lb, IntegerW.-(i.ub, IntegerVal(1)))
    } else {
      i
    }
    coerceBot(res)
  }

  def singleton(iv: IntegerW): Interval = mkInterval(iv, iv)

  def mkInterval(lb: IntegerW, ub: IntegerW): Interval = {
    coerceBot(Interval(boundsAdjusted(lb), boundsAdjusted(ub)))
  }

  def +(i1: Interval, i2: Interval): Interval = {
    val newlb = IntegerW.+(i1.lb, i2.lb)
    val newub = IntegerW.+(i1.ub, i2.ub)
    mkInterval(newlb, newub)
  }

  def -(i1: Interval, i2: Interval): Interval = {
    val newlb = IntegerW.-(i1.lb, i2.lb)
    val newub = IntegerW.-(i1.ub, i2.ub)
    mkInterval(newlb, newub)
  }

  def *(i1: Interval, i2: Interval): Interval = {
    val ia = IntegerW.*(i1.lb, i2.lb)
    val ib = IntegerW.*(i1.lb, i2.ub)
    val ic = IntegerW.*(i1.ub, i2.lb)
    val id = IntegerW.*(i1.ub, i2.ub)
    mkInterval(IntegerW.min(ia,ib,ic,id), IntegerW.max(ia,ib,ic,id))
  }

  def /(i1: Interval, i2: Interval): Interval = {
    if (contains(i2, 0)) Lattice[Interval].top
    else {
      val ia = IntegerW./(i1.lb, i2.lb)
      val ib = IntegerW./(i1.lb, i2.ub)
      val ic = IntegerW./(i1.ub, i2.lb)
      val id = IntegerW./(i1.ub, i2.ub)
      mkInterval(IntegerW.min(ia,ib,ic,id), IntegerW.max(ia,ib,ic,id))
    }
  }

  def %(i1: Interval, i2: Interval): Interval = {
    require(IntegerW.<(IntegerVal(0), i2.lb))
    mkInterval(IntegerVal(0), i2.ub) // TODO Do something smarter?
  }
}

object Intervals {
  val Positive = Intervals(IntegerVal(0), IntegerInf)
  val Unbounded = Intervals()
}
