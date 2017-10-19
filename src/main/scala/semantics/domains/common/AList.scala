package semantics.domains.common

sealed trait AList[+V]
case object AListBot extends AList[Nothing]
case class AListVals[V](vs: List[V]) extends AList[V]
case object AListTop extends AList[Nothing]

case object NonFixedList extends Exception

object AList {
  def botToSizedBot[V: Lattice](alist: AList[V], n: Int): AList[V] = alist match {
    case AListBot => sizedBot[V](n)
    case _ => alist
  }

  def sizedBot[V: Lattice](n : Int): AList[V] = AListVals(List.fill(n)(Lattice[V].bot))

  def getList[V](alist: AList[V]): List[V] = alist match {
    case AListVals(vs) => vs
    case _ => throw NonFixedList
  }

  implicit def AListLattice[V : Lattice]: Lattice[AList[V]] = new Lattice[AList[V]] {
    override def <=(a1: AList[V], a2: AList[V]): Boolean = (a1, a2) match {
      case (AListBot, _) => true
      case (_, AListTop) => true
      case (AListVals(vs1), AListVals(vs2)) =>
        vs1.length == vs2.length &&
          vs1.zip(vs2).forall { case (v1, v2) => Lattice[V].<=(v1, v2) }
      case _ => false
    }

    override def widen(a1: AList[V], a2: AList[V], depth: Int): AList[V] =
      upperBound(a1, a2,  Lattice[V].widen(_,_,depth))

    override def bot: AList[V] = AListBot

    override def top: AList[V] = AListTop

    private def upperBound(a1: AList[V], a2: AList[V], ub : (V, V) => V): AList[V] = {
      (a1, a2) match {
        case (AListBot, a) => a
        case (a, AListBot) => a
        case (_, AListTop) | (AListTop, _) => AListTop
        case (AListVals(vs1), AListVals(vs2)) =>
          if (vs1.length == vs2.length) AListVals(vs1.zip(vs2).map {
            case (v1, v2) => ub(v1,v2) })
          else AListTop
      }
    }

    override def lub(a1: AList[V], a2: AList[V]): AList[V] = upperBound(a1, a2,  Lattice[V].lub)

    override def glb(a1: AList[V], a2: AList[V]): AList[V] = (a1, a2) match {
      case (AListBot, _) | (_, AListBot) => AListBot
      case (AListTop, a) => a
      case (a, AListTop) => a
      case (AListVals(vs1), AListVals(vs2)) =>
        if (vs1.length == vs2.length) AListVals(vs1.zip(vs2).map {
          case (v1, v2) => Lattice[V].glb(v1,v2) })
        else  AListBot
    }
  }
}
