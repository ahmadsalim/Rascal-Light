package semantics.domains.abstracting

import scalaz.std.list._
import scalaz.syntax.traverse._
import semantics.domains.common.{ConcreteAbstractGalois, Galois, Lattice}
import semantics.domains.concrete.Powerset.PowersetLattice

sealed trait ListShape[E]
case class ListBot[E]() extends ListShape[E]
case class ListElements[E] private (e : E) extends ListShape[E]
case class ListTop[E]() extends ListShape[E]

object ListShape {

  implicit def ListShapeLattice[E : Lattice] = new Lattice[ListShape[E]] {
    override def bot: ListShape[E] = ListBot()

    override def top: ListShape[E] = ListTop()

    override def lub(a1: ListShape[E], a2: ListShape[E]): ListShape[E] = (a1, a2) match {
      case (ListBot(), a) => a
      case (a, ListBot()) => a
      case (ListTop(), _) | (_, ListTop()) => ListTop()
      case (ListElements(e1), ListElements(e2)) => listElements(Lattice[E].lub(e1, e2))
    }

    override def glb(a1: ListShape[E], a2: ListShape[E]): ListShape[E] = (a1, a2) match {
      case (ListBot(), _) | (_, ListBot()) => ListBot()
      case (ListTop(), a) => a
      case (a, ListTop()) => a
      case (ListElements(e1), ListElements(e2)) => listElements(Lattice[E].glb(e1, e2))
    }

    override def <=(a1: ListShape[E], a2: ListShape[E]): Boolean = (a1, a2) match {
      case (ListBot(), _) => true
      case (_, ListTop()) => true
      case (ListElements(e1), ListElements(e2)) => Lattice[E].<=(e1, e2)
      case _ => false
    }

    override def widen(a1: ListShape[E], a2: ListShape[E]): ListShape[E] = (a1, a2) match {
      case (ListBot(), a) => a
      case (a, ListBot()) => a
      case (ListTop(), _) | (_, ListTop()) => ListTop()
      case (ListElements(e1), ListElements(e2)) => listElements(Lattice[E].widen(e1, e2))
    }
  }

  implicit def ListListShapeGalois[CE, E]
  (implicit elemGalois: ConcreteAbstractGalois[CE, E]) = new ConcreteAbstractGalois[List[CE], ListShape[E]] {
    override def latticeC: Lattice[Set[List[CE]]] = PowersetLattice

    override def latticeA: Lattice[ListShape[E]] = ListShapeLattice[E](Galois[CE, E].latticeA)

    override def alpha(dcs: Set[List[CE]]): ListShape[E] = {
      implicit val latticeE = Galois[CE, E].latticeA
      listElements(Lattice[E].lub(dcs.map(dc => Galois[CE, E].alpha(dc.toSet))))
    }

    override def gamma(da: ListShape[E], bound: Int): Set[List[CE]] = {
      implicit val latticeE = Galois[CE, E].latticeA

      def concretizeElementsOf(e : E) = {
        val innerBound: Int = Math.sqrt(bound).toInt
        val outerBound: Int = if (innerBound > 0) bound / innerBound else 1
        (0 until outerBound).toSet.flatMap { (size: Int) =>
          (1 to size).toList.traverseU(_ =>
            Galois[CE, E].gamma(e, innerBound).toList
          )
        }
      }

      da match {
        case ListBot() => Set()
        case ListElements(e) =>
          concretizeElementsOf(e)
        case ListTop() =>
          concretizeElementsOf(Lattice[E].top)
      }
    }
  }

  def listElements[E : Lattice](e : E): ListShape[E] = {
    if (e == Lattice[E].bot) Lattice[ListShape[E]].bot
    else if (e == Lattice[E].top) Lattice[ListShape[E]].top
    else ListElements(e)
  }
}
