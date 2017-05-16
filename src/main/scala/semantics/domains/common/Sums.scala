package semantics.domains.common

import semantics.domains.concrete.Powerset
import semantics.domains.concrete.Powerset._

import scala.language.higherKinds

sealed trait Sum5[E, F1[_], F2[_], F3[_], F4[_], F5[_]]

case class SumBot[E,F1[_],F2[_],F3[_],F4[_],F5[_]]() extends Sum5[E,F1,F2,F3,F4,F5]
case class SumTop[E,F1[_],F2[_],F3[_],F4[_],F5[_]]() extends Sum5[E,F1,F2,F3,F4,F5]
case class Inj1[E,F1[_],F2[_],F3[_],F4[_],F5[_]](ret1: F1[E]) extends Sum5[E,F1,F2,F3,F4,F5]
case class Inj2[E,F1[_],F2[_],F3[_],F4[_],F5[_]](ret2: F2[E]) extends Sum5[E,F1,F2,F3,F4,F5]
case class Inj3[E,F1[_],F2[_],F3[_],F4[_],F5[_]](ret3: F3[E]) extends Sum5[E,F1,F2,F3,F4,F5]
case class Inj4[E,F1[_],F2[_],F3[_],F4[_],F5[_]](ret4: F4[E]) extends Sum5[E,F1,F2,F3,F4,F5]
case class Inj5[E,F1[_],F2[_],F3[_],F4[_],F5[_]](ret5: F5[E]) extends Sum5[E,F1,F2,F3,F4,F5]

object Sums {
  implicit def Sum5Lattice[E : Lattice, F1[_], F2[_], F3[_], F4[_], F5[_]]
          (implicit lattf1 : Lattice[F1[E]],
                    lattf2 : Lattice[F2[E]],
                    lattf3 : Lattice[F3[E]],
                    lattf4 : Lattice[F4[E]],
                    lattf5 : Lattice[F5[E]]) = new Lattice[Sum5[E, F1, F2, F3, F4, F5]] {


    override def bot: Sum5[E, F1, F2, F3, F4, F5] = SumBot()

    override def top: Sum5[E, F1, F2, F3, F4, F5] = SumTop()

    override def lub(a1: Sum5[E, F1, F2, F3, F4, F5], a2: Sum5[E, F1, F2, F3, F4, F5]): Sum5[E, F1, F2, F3, F4, F5] = (a1, a2) match {
      case (SumBot(), a) => a
      case (a, SumBot()) => a
      case (SumTop(), _) | (_, SumTop()) => SumTop()
      case (Inj1(fe1), Inj1(fe2)) => Inj1(lattf1.lub(fe1, fe2))
      case (Inj2(fe1), Inj2(fe2)) => Inj2(lattf2.lub(fe1, fe2))
      case (Inj3(fe1), Inj3(fe2)) => Inj3(lattf3.lub(fe1, fe2))
      case (Inj4(fe1), Inj4(fe2)) => Inj4(lattf4.lub(fe1, fe2))
      case (Inj5(fe1), Inj5(fe2)) => Inj5(lattf5.lub(fe1, fe2))
      case _ => SumTop()
    }

    override def glb(a1: Sum5[E, F1, F2, F3, F4, F5], a2: Sum5[E, F1, F2, F3, F4, F5]): Sum5[E, F1, F2, F3, F4, F5] = (a1, a2) match {
      case (SumTop(), a) => a
      case (a, SumTop()) => a
      case (SumBot(), _) | (_, SumBot()) => SumBot()
      case (Inj1(fe1), Inj1(fe2)) => Inj1(lattf1.glb(fe1, fe2))
      case (Inj2(fe1), Inj2(fe2)) => Inj2(lattf2.glb(fe1, fe2))
      case (Inj3(fe1), Inj3(fe2)) => Inj3(lattf3.glb(fe1, fe2))
      case (Inj4(fe1), Inj4(fe2)) => Inj4(lattf4.glb(fe1, fe2))
      case (Inj5(fe1), Inj5(fe2)) => Inj5(lattf5.glb(fe1, fe2))
      case _ => SumBot()
    }

    override def <=(a1: Sum5[E, F1, F2, F3, F4, F5], a2: Sum5[E, F1, F2, F3, F4, F5]): Boolean = (a1, a2) match {
      case (SumBot(), _) => true
      case (_, SumTop()) => true
      case (Inj1(fe1), Inj1(fe2)) => lattf1.<=(fe1, fe2)
      case (Inj2(fe1), Inj2(fe2)) => lattf2.<=(fe1, fe2)
      case (Inj3(fe1), Inj3(fe2)) => lattf3.<=(fe1, fe2)
      case (Inj4(fe1), Inj4(fe2)) => lattf4.<=(fe1, fe2)
      case (Inj5(fe1), Inj5(fe2)) => lattf5.<=(fe1, fe2)
      case _ => false
    }

    override def widen(a1: Sum5[E, F1, F2, F3, F4, F5], a2: Sum5[E, F1, F2, F3, F4, F5]): Sum5[E, F1, F2, F3, F4, F5] = (a1, a2) match {
      case (SumBot(), a) => a
      case (a, SumBot()) => a
      case (SumTop(), _) | (_, SumTop()) => SumTop()
      case (Inj1(fe1), Inj1(fe2)) => Inj1(lattf1.widen(fe1, fe2))
      case (Inj2(fe1), Inj2(fe2)) => Inj2(lattf2.widen(fe1, fe2))
      case (Inj3(fe1), Inj3(fe2)) => Inj3(lattf3.widen(fe1, fe2))
      case (Inj4(fe1), Inj4(fe2)) => Inj4(lattf4.widen(fe1, fe2))
      case (Inj5(fe1), Inj5(fe2)) => Inj5(lattf5.widen(fe1, fe2))
      case _ => SumTop()
    }
  }

  implicit def SumSumGalois[CE : Lattice,CF1[_],CF2[_],CF3[_],CF4[_],CF5[_],E : Lattice,F1[_],F2[_],F3[_],F4[_],F5[_]]
    (implicit
      lattf1 : Lattice[F1[E]]
    , lattf2 : Lattice[F2[E]]
    , lattf3 : Lattice[F3[E]]
    , lattf4 : Lattice[F4[E]]
    , lattf5 : Lattice[F5[E]]
    , lattcf1 : Lattice[CF1[CE]]
    , lattcf2 : Lattice[CF2[CE]]
    , lattcf3 : Lattice[CF3[CE]]
    , lattcf4 : Lattice[CF4[CE]]
    , lattcf5 : Lattice[CF5[CE]]
    , cagalois1 : ConcreteAbstractGalois[CF1[CE], F1[E]]
    , cagalois2 : ConcreteAbstractGalois[CF2[CE], F2[E]]
    , cagalois3 : ConcreteAbstractGalois[CF3[CE], F3[E]]
    , cagalois4 : ConcreteAbstractGalois[CF4[CE], F4[E]]
    , cagalois5 : ConcreteAbstractGalois[CF5[CE], F5[E]]):
       ConcreteAbstractGalois[Sum5[CE,CF1,CF2,CF3,CF4,CF5], Sum5[E,F1,F2,F3,F4,F5]] =
         new ConcreteAbstractGalois[Sum5[CE,CF1,CF2,CF3,CF4,CF5], Sum5[E,F1,F2,F3,F4,F5]] {
           override def latticeC: Lattice[Set[Sum5[CE, CF1, CF2, CF3, CF4, CF5]]] = PowersetLattice

           override def latticeA: Lattice[Sum5[E, F1, F2, F3, F4, F5]] = Sum5Lattice

           override def alpha(dcs: Set[Sum5[CE, CF1, CF2, CF3, CF4, CF5]]): Sum5[E, F1, F2, F3, F4, F5] =
            Lattice[Sum5[E, F1, F2, F3, F4, F5]].lub(dcs.map {
              case SumBot() => SumBot[E,F1,F2,F3,F4,F5]()
              case SumTop() => SumTop[E,F1,F2,F3,F4,F5]()
              case Inj1(ce) => Inj1[E,F1,F2,F3,F4,F5](Galois[CF1[CE], F1[E]].alpha(Set(ce)))
              case Inj2(ce) => Inj2[E,F1,F2,F3,F4,F5](Galois[CF2[CE], F2[E]].alpha(Set(ce)))
              case Inj3(ce) => Inj3[E,F1,F2,F3,F4,F5](Galois[CF3[CE], F3[E]].alpha(Set(ce)))
              case Inj4(ce) => Inj4[E,F1,F2,F3,F4,F5](Galois[CF4[CE], F4[E]].alpha(Set(ce)))
              case Inj5(ce) => Inj5[E,F1,F2,F3,F4,F5](Galois[CF5[CE], F5[E]].alpha(Set(ce)))
            })

           override def gamma(da: Sum5[E, F1, F2, F3, F4, F5], bound: Int): Set[Sum5[CE, CF1, CF2, CF3, CF4, CF5]] = da match {
             case SumBot() => Set()
             case SumTop() =>
               (((Galois[CF1[CE],F1[E]].gamma(Lattice[F1[E]].top, bound - 1).map(Inj1 (_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5]) union
                 Galois[CF2[CE],F2[E]].gamma(Lattice[F2[E]].top, bound - 1).map(Inj2(_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])) union
                 Galois[CF3[CE],F3[E]].gamma(Lattice[F3[E]].top, bound - 1).map(Inj3(_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])) union
                 Galois[CF4[CE],F4[E]].gamma(Lattice[F4[E]].top, bound - 1).map(Inj4(_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])) union
                 Galois[CF5[CE],F5[E]].gamma(Lattice[F5[E]].top, bound - 1).map(Inj5(_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])
             case Inj1(ret1) =>
               Galois[CF1[CE],F1[E]].gamma(ret1, bound - 1).map(Inj1 (_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])
             case Inj2(ret2) =>
               Galois[CF2[CE],F2[E]].gamma(ret2, bound - 1).map(Inj2 (_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])
             case Inj3(ret3) =>
               Galois[CF3[CE],F3[E]].gamma(ret3, bound - 1).map(Inj3 (_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])
             case Inj4(ret4) =>
               Galois[CF4[CE],F4[E]].gamma(ret4, bound - 1).map(Inj4 (_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])
             case Inj5(ret5) =>
               Galois[CF5[CE],F5[E]].gamma(ret5, bound - 1).map(Inj5 (_) : Sum5[CE, CF1, CF2, CF3, CF4, CF5])
           }
         }
}