package semantics.domains.common

object Boolean {
  implicit def boolLattice = new Lattice[Boolean] {
    override def bot: Boolean = ???

    override def top: Boolean = ???

    override def lub(a1: Boolean, a2: Boolean): Boolean = ???

    override def glb(a1: Boolean, a2: Boolean): Boolean = ???

    override def <=(a1: Boolean, a2: Boolean): Boolean = ???

    override def widen(a1: Boolean, a2: Boolean, depth: Int): Boolean = lub(a1, a2)
  }
}
