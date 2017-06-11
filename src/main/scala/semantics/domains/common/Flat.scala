package semantics.domains.common

import scalaz.Functor

sealed trait Flat[+V]
case object FlatBot extends Flat[Nothing]
case class FlatValue[V](v: V) extends Flat[V]
case object FlatTop extends Flat[Nothing]

case object NonFlatValue extends Exception

object Flat {
  def unflat[V](flat: Flat[V]): V = flat match {
    case FlatValue(v) => v
    case _ => throw NonFlatValue
  }

  implicit def FlatFunctor: Functor[Flat] = new Functor[Flat] {
    override def map[A, B](fa: Flat[A])(f: (A) => B): Flat[B] = fa match {
      case FlatBot => FlatBot
      case FlatValue(v) => FlatValue(f(v))
      case FlatTop => FlatTop
    }
  }

  implicit def FlatLattice[V]: Lattice[Flat[V]] = new Lattice[Flat[V]] {
    override def <=(a1: Flat[V], a2: Flat[V]): Boolean = (a1, a2) match {
      case (FlatBot, _) => true
      case (_, FlatTop) => true
      case (FlatValue(v1), FlatValue(v2)) => v1 == v2
      case _ => false
    }

    override def widen(a1: Flat[V], a2: Flat[V], depth: Int): Flat[V] = lub(a1, a2)

    override def bot: Flat[V] = FlatBot

    override def top: Flat[V] = FlatTop

    override def lub(a1: Flat[V], a2: Flat[V]): Flat[V] = (a1, a2) match {
      case (FlatBot, a) => a
      case (a, FlatBot) => a
      case (_, FlatTop) | (FlatTop, _) => FlatTop
      case (FlatValue(v1), FlatValue(v2)) =>
        if (v1 == v2) FlatValue(v1) else FlatTop
    }

    override def glb(a1: Flat[V], a2: Flat[V]): Flat[V] = (a1, a2) match {
      case (FlatBot, _) | (_, FlatBot) => FlatBot
      case (FlatTop, a) => a
      case (a, FlatTop) => a
      case (FlatValue(v1), FlatValue(v2)) =>
        if (v1 == v2) FlatValue(v1) else FlatBot
    }
  }
}
