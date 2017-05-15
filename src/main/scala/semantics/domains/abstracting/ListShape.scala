import semantics.domains._
import semantics.domains.common.Lattice

sealed trait ListShape[E]
case class ListBot[E]() extends ListShape[E]
case class ListElements[E] private (e : E) extends ListShape[E]
case class ListTop[E]() extends ListShape[E]

object ListShape {

  implicit def listLattice[E : Lattice] = new Lattice[ListShape[E]] {
    override def bot: ListShape[E] = ListBot()

    override def top: ListShape[E] = ListTop()

    override def lub(a1: ListShape[E], a2: ListShape[E]): ListShape[E] = ???

    override def glb(a1: ListShape[E], a2: ListShape[E]): ListShape[E] = ???

    override def <=(a1: ListShape[E], a2: ListShape[E]): Boolean = (a1, a2) match {
      case (ListBot(), _) => true
      case (_, ListTop()) => true
      case (ListElements(e1), ListElements(e2)) => Lattice[E].<=(e1, e2)
      case _ => false
    }

    override def widen(a1: ListShape[E], a2: ListShape[E]): ListShape[E] = ???
  }

  def listElements[E : Lattice](e : E): ListShape[E] = {
    if (e == Lattice[E].bot) Lattice[ListShape[E]].bot
    else if (e == Lattice[E].top) Lattice[ListShape[E]].top
    else ListElements(e)
  }
}
