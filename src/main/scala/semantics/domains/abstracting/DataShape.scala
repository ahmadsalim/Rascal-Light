package semantics.domains.abstracting

import semantics.Typing
import semantics.domains.common.Powerset.PowersetLattice
import semantics.domains.common.{ConcreteAbstractGalois, Lattice, Module}
import semantics.domains.concrete.{ConstructorValue, Value}
import syntax.{ConsName, Type, TypeName}

import scalaz.std.list._
import scalaz.syntax.traverse._
import scalaz.BijectionT.Bijection


sealed trait DataShape[E]
case class DataBot[E]() extends DataShape[E]
case class DataElements[E] private(consShape: Map[ConsName, List[E]]) extends DataShape[E]
case class DataTop[E]() extends DataShape[E]

case class DataShapeOf(module: Module, typeName: TypeName) {
  private val typing: Typing = Typing(module)
  private val allConstructors: Map[ConsName, List[Type]] =
    module.datatypes(typeName).map(cons => cons -> module.constructors(cons)._2.map(_.typ)).toMap

  def dataElements[E : Lattice](consShape: Map[ConsName, List[E]]): DataShape[E] = {
    val validConsShape = consShape.filterKeys(cons => consShape(cons) != Lattice[E].bot)
    if (consShape.isEmpty) DataBot()
    else if ((allConstructors.keySet subsetOf validConsShape.keySet) && validConsShape.values.forall(_ == Lattice[E].top)) DataTop()
    else DataElements(validConsShape)
  }

  implicit def DataShapeLattice[E : Lattice]: Lattice[DataShape[E]] = new Lattice[DataShape[E]] {
    override def bot: DataShape[E] = DataBot()

    override def top: DataShape[E] = DataTop()

    override def lub(a1: DataShape[E], a2: DataShape[E]): DataShape[E] = upperbound(a1, a2, Lattice[E].lub)

    private def upperbound(a1: DataShape[E], a2: DataShape[E], eub : (E, E) => E): DataShape[E] = {
      (a1, a2) match {
        case (DataBot(), a) => a
        case (a, DataBot()) => a
        case (DataTop(), _) | (_, DataTop()) => DataTop()
        case (DataElements(consShape1), DataElements(consShape2)) =>
          dataElements((consShape1.keySet union consShape2.keySet).toList.map { cons =>
            val arity = allConstructors(cons).size
            val bots = (1 to arity).toList.map(_ => Lattice[E].bot)
            val v1 = consShape1.get(cons).fold(bots)(identity)
            val v2 = consShape2.get(cons).fold(bots)(identity)
            cons -> v1.zip(v2).map(eub.tupled)
          }.toMap)
      }
    }

    override def glb(a1: DataShape[E], a2: DataShape[E]): DataShape[E] = (a1, a2) match {
      case (DataTop(), a) => a
      case (a, DataTop()) => a
      case (DataBot(), _) | (_, DataBot()) => DataBot()
      case (DataElements(consShape1), DataElements(consShape2)) =>
        dataElements((consShape1.keySet intersect consShape2.keySet).toList.map { cons =>
          val arity = allConstructors(cons).size
          val tops = (1 to arity).toList.map(_ => Lattice[E].top)
          val v1 = consShape1.get(cons).fold(tops)(identity)
          val v2 = consShape2.get(cons).fold(tops)(identity)
          cons -> v1.zip(v2).map { case (e1, e2) => Lattice[E].glb(e1, e2) }
        }.toMap)
    }

    override def <=(a1: DataShape[E], a2: DataShape[E]): Boolean = (a1, a2) match {
      case (DataBot(), _) => true
      case (_, DataTop()) => true
      case (DataElements(consShape1), DataElements(consShape2)) =>
        (consShape1.keySet subsetOf consShape2.keySet) &&
          consShape1.forall { case (k,vs1) =>
            val vs2 = consShape2(k)
            vs1.zip(vs2).forall { case (v1, v2) => Lattice[E].<=(v1, v2) }
          }
      case _ => false
    }

    override def widen(a1: DataShape[E], a2: DataShape[E], depth : Int): DataShape[E] = upperbound(a1, a2, Lattice[E].widen(_,_,depth))
  }

  implicit def DataConsGalois[CE,E]
    (implicit elementGalois: ConcreteAbstractGalois[CE, E],
              convValue: Bijection[CE, Value]) : ConcreteAbstractGalois[ConstructorValue, DataShape[E]]
  = new ConcreteAbstractGalois[ConstructorValue, DataShape[E]] {
    override def latticeC: Lattice[Set[ConstructorValue]] = PowersetLattice

    override def latticeA: Lattice[DataShape[E]] = {
      implicit val latte = elementGalois.latticeA
      DataShapeLattice[E]
    }

    override def alpha(dcs: Set[ConstructorValue]): DataShape[E] = {
      implicit val latte = elementGalois.latticeA
      latticeA.lub(dcs.map(consValue =>
        dataElements(Map(consValue.name ->
          consValue.vals.map(convValue.from).map(ce => elementGalois.alpha(Set(ce))).toList))))
    }

    override def gamma(da: DataShape[E], bound: Int): Set[ConstructorValue] = {
      da match {
        case DataBot() => Set()
        case DataElements(consShape) =>
          consShape.toList.flatMap { case (cons, shapes) =>
            val arity = shapes.size
            val innerBound = if (arity > 0) bound / arity else 1
            val elements = shapes.zipWithIndex.traverseU { case (shape, idx) =>
              val ty = allConstructors(cons)(idx)
                elementGalois.gamma(shape, innerBound).map(convValue.to).filter(v =>
                  typing.checkType(v, ty)
                ).toList
            }
              elements.map(vs => ConstructorValue(cons, vs))
          }.toSet
        case DataTop() =>
          allConstructors.toList.flatMap { case (cons, types) =>
            val arity = types.size
            val innerBound = if (arity > 0) bound / arity else 1
            val elements = types.traverseU { ty =>
              elementGalois.gamma(elementGalois.latticeA.top, innerBound).map(convValue.to).filter(v =>
                typing.checkType(v, ty)
              ).toList
            }
            elements.map(vs => ConstructorValue(cons, vs))
          }.toSet
      }
    }
  }
}
