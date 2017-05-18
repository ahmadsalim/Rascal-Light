package semantics.domains.abstracting

import semantics.domains.common.Powerset.PowersetLattice
import semantics.domains.common._
import semantics.domains.concrete._
import Empty._
import syntax.{IntLit, StringLit}
import ListShape._

import scalaz.BijectionT.{Bijection, bijection}
import scalaz.{BijectionT, Id, ~>, ~~>}

case class ValueShapeOf(module: Module) {
  private
  type PCValue[E] = Sum3[E, Lambda[E => Int], List, Lambda[E => ConstructorValue]]
  private
  type CValue = Fix[PCValue]

  type PValueShape[E] = Sum3[E, Lambda[E => Sign], ListShape, DataShape]
  type ValueShape = Fix[PValueShape]

  private
  val DataShape = DataShapeOf(module)

  import DataShape._

  private implicit
  val bijValueFValue = {
    def from(fvl : CValue): Value = fvl match {
      case Fix(fvlout) =>
        // Pattern matching seems broken
        fvlout match {
          case _: SumBot[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            BottomValue
          case _: SumTop[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            throw new UnsupportedOperationException("Top abstraction is not convertible to value")
          case inj1: Inj1[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            BasicValue(IntLit(inj1.ret1))
          case inj2: Inj2[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            ListValue(inj2.ret2.map(from))
          case inj3: Inj3[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            inj3.ret3 // This is a constructor value already!
          case inj4: Inj4[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            inj4.ret4 // This has type Nothing so is impossible
          case inj5: Inj5[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing] =>
            inj5.ret5 // This has type Nothing so is impossible
        }
    }
    def to(vl : Value): CValue = vl match {
        case BasicValue(b) =>
          b match {
            case IntLit(i) =>
              Fix[PCValue](Inj1[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing](i))
            case StringLit(s) => throw new UnsupportedOperationException("String literals are unsupported")
          }
        case cvl@ConstructorValue(name, vals) =>
            Fix[PCValue](Inj3[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing](cvl))
        case ListValue(vals) =>
            Fix[PCValue](Inj2[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing](vals.map(to)))
        case SetValue(vals) => throw new UnsupportedOperationException("Set values are unsupported")
        case MapValue(vals) => throw new UnsupportedOperationException("Map values are unsupported")
        case BottomValue => Fix[PCValue](SumBot[CValue, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing]())
      }
    bijection[Id.Id, Id.Id, CValue, Value](from, to)
  }

  private
  val FValueShapeGalois = {
    implicit
    val flattice = new (Lattice ~> Lambda[E => Lattice[PValueShape[E]]]) {
      override def apply[E](fa: Lattice[E]): Lattice[PValueShape[E]] = {
        implicit val ifa = fa
        Sums.Sum5Lattice[E, Lambda[E => Sign], ListShape, DataShape, Nothing, Nothing]
      }
    }
    implicit val cffgalois = new (Lambda[(CE, E) => (Bijection[CE, Value], DummyImplicit, ConcreteAbstractGalois[CE, E])] ~~> Lambda[(CE, E) => ConcreteAbstractGalois[PCValue[CE], PValueShape[E]]]) {
      override def apply[CE, E](f: (Bijection[CE, Value], DummyImplicit, ConcreteAbstractGalois[CE, E])): ConcreteAbstractGalois[PCValue[CE], PValueShape[E]] = {
        implicit
        val (bij, _, cagalois) = f
        implicit val flattice = cagalois.latticeA
        Sums.SumSumGalois[CE, Lambda[E => Int], List, Lambda[E => ConstructorValue], Nothing, Nothing,
          E, Lambda[E => Sign], ListShape, DataShape, Nothing, Nothing](flattice, Sign.IntSignGalois, ListShape.ListListShapeGalois[CE, E],
        DataShape.DataConsGalois[CE, E], Empty.EmptyGalois, Empty.EmptyGalois)
      }
    }
    Fix.FixFixGalois[Bijection[?, Value], Lambda[E => DummyImplicit], PCValue, PValueShape]
  }

  implicit val ValueValueShapeGalois = new ConcreteAbstractGalois[Value, ValueShape] {
     override def latticeC: Lattice[Set[Value]] = PowersetLattice

    override def latticeA: Lattice[ValueShape] = {
      implicit val sumLatticeBNT : Lattice ~> Lambda[E => Lattice[Sum3[E, Lambda[E => Sign], ListShape, DataShape]]]
        = new (Lattice ~> Lambda[E => Lattice[Sum3[E, Lambda[E => Sign], ListShape, DataShape]]]) {
        override def apply[E](fa: Lattice[E]): Lattice[Sum3[E, Lambda[E => Sign], ListShape, DataShape]] = {
          implicit val ifa = fa
          Sums.Sum5Lattice[E, Lambda[E => Sign], ListShape, DataShape, Nothing, Nothing]
        }
      }
      Fix.FixLattice[Sum3[?, Lambda[E => Sign], ListShape, DataShape]]
    }

    override def alpha(dcs: Set[Value]): ValueShape = FValueShapeGalois.alpha(dcs.map(bijValueFValue.from))

    override def gamma(da: ValueShape, bound: Int): Set[Value] = FValueShapeGalois.gamma(da, bound).map(bijValueFValue.to)
  }
}
