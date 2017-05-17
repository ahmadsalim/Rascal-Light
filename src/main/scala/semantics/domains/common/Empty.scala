package semantics.domains.common

import Powerset.PowersetLattice

object Empty {
  implicit def EmptyLattice = new Lattice[Nothing] {
    override def bot: Nothing = throw IsEmpty

    override def top: Nothing = throw IsEmpty

    override def lub(a1: Nothing, a2: Nothing): Nothing = a1

    override def glb(a1: Nothing, a2: Nothing): Nothing = a1

    override def <=(a1: Nothing, a2: Nothing): Boolean = a1

    override def widen(a1: Nothing, a2: Nothing, depth : Int): Nothing = a1
  }

  implicit def EmptyGalois = new ConcreteAbstractGalois[Nothing, Nothing] {
    override def latticeC: Lattice[Set[Nothing]] = PowersetLattice

    override def latticeA: Lattice[Nothing] = EmptyLattice

    override def alpha(dcs: Set[Nothing]): Nothing = latticeA.lub(dcs)

    override def gamma(da: Nothing, bound: Int): Set[Nothing] = Set()
  }
}