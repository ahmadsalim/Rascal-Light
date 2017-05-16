package semantics.domains.abstracting

import semantics.domains.common.Lattice
import syntax.{ConsName, TypeName}


sealed trait DataShape[E]

case class DataBot[E]() extends DataShape[E]

case class DataElements[E] private(allConstructors: Set[ConsName], consShape: Map[ConsName, E]) extends DataShape[E]

case class DataTop[E]() extends DataShape[E]

object DataShape {
  def dataElements[E : Lattice](allConstructors: Set[ConsName], consShape: Map[ConsName, E]): DataShape[E] = {
    val validConsShape = consShape.filterKeys(cons => consShape(cons) != Lattice[E].bot)
    if (consShape.isEmpty) DataBot()
    else if ((allConstructors subsetOf validConsShape.keySet) && validConsShape.values.forall(_ == Lattice[E].top)) DataTop()
    else DataElements(allConstructors, validConsShape)
  }

  implicit def DataShapeLattice[E : Lattice] = new Lattice[DataShape[E]] {
    override def bot: DataShape[E] = DataBot()

    override def top: DataShape[E] = DataTop()

    override def lub(a1: DataShape[E], a2: DataShape[E]) = upperbound(a1, a2, Lattice[E].lub)

    private def upperbound(a1: DataShape[E], a2: DataShape[E], eub : (E, E) => E): DataShape[E] = {
      (a1, a2) match {
        case (DataBot(), a) => a
        case (a, DataBot()) => a
        case (DataTop(), _) | (_, DataTop()) => DataTop()
        case (DataElements(allConstructors1, consShape1), DataElements(allConstructors2, consShape2)) =>
          assert(allConstructors1 == allConstructors2)
          dataElements(allConstructors1, (consShape1.keySet union consShape2.keySet).toList.map { cons =>
            val v1 = consShape1.get(cons).fold(Lattice[E].bot)(identity)
            val v2 = consShape2.get(cons).fold(Lattice[E].bot)(identity)
            cons -> eub(v1, v2)
          }.toMap)
      }
    }

    override def glb(a1: DataShape[E], a2: DataShape[E]): DataShape[E] = (a1, a2) match {
      case (DataTop(), a) => a
      case (a, DataTop()) => a
      case (DataBot(), _) | (_, DataBot()) => DataBot()
      case (DataElements(allConstructors1, consShape1), DataElements(allConstructors2, consShape2)) =>
        assert(allConstructors1 == allConstructors2)
        dataElements(allConstructors1, (consShape1.keySet intersect consShape2.keySet).toList.map { cons =>
          val v1 = consShape1.get(cons).fold(Lattice[E].bot)(identity)
          val v2 = consShape2.get(cons).fold(Lattice[E].bot)(identity)
          cons -> Lattice[E].glb(v1, v2)
        }.toMap)
    }

    override def <=(a1: DataShape[E], a2: DataShape[E]): Boolean = (a1, a2) match {
      case (DataBot(), _) => true
      case (_, DataTop()) => true
      case (DataElements(allConstructors1, consShape1), DataElements(allConstructors2, consShape2)) =>
        assert(allConstructors1 == allConstructors2)
        (consShape1.keySet subsetOf consShape2.keySet) &&
          consShape1.forall { case (k,v1) =>
            val v2 = consShape2(k)
            Lattice[E].<=(v1, v2)
          }
      case _ => false
    }

    override def widen(a1: DataShape[E], a2: DataShape[E]): DataShape[E] = upperbound(a1, a2, Lattice[E].widen)
  }
}
