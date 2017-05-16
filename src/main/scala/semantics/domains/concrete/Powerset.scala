package semantics.domains.concrete

import semantics.domains.common.Lattice

object Powerset {
  implicit def PowersetLattice[A]: Lattice[Set[A]] = new Lattice[Set[A]] {
    override def <=(a1: Set[A], a2: Set[A]): Boolean = a1 subsetOf a2

    override def widen(a1: Set[A], a2: Set[A]): Set[A] =
      throw new UnsupportedOperationException("Widening not supported for Powerset lattice")

    override def bot: Set[A] = Set()

    override def top: Set[A] =
    throw new UnsupportedOperationException("Widening not supported for Powerset lattice")

    override def lub(a1: Set[A], a2: Set[A]): Set[A] = a1 union a2

    override def glb(a1: Set[A], a2: Set[A]): Set[A] = a1 intersect a2
  }
}
