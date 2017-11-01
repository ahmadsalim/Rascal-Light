package semantics.domains.common

object Unit {
  implicit def unitLattice: Lattice[Unit] = new Lattice[Unit] {
    override def <=(a1: Unit, a2: Unit): Boolean = true

    override def widen(a1: Unit, a2: Unit, bound: Int): Unit = ()

    override def bot: Unit = ()

    override def top: Unit = ()

    override def lub(a1: Unit, a2: Unit): Unit = ()

    override def glb(a1: Unit, a2: Unit): Unit = ()
  }
}
