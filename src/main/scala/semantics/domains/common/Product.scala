package semantics.domains.common

/**
  * Created by asal on 25/05/2017.
  */
object Product {

  implicit def cartesianLattice[E1 : Lattice, E2 : Lattice]: Lattice[(E1, E2)] = new Lattice[(E1, E2)] {
    override def bot: (E1, E2) = (Lattice[E1].bot, Lattice[E2].bot)

    override def top: (E1, E2) = (Lattice[E1].top, Lattice[E2].top)

    override def lub(a1: (E1, E2), a2: (E1, E2)): (E1, E2) =
      (Lattice[E1].lub(a1._1, a2._1), Lattice[E2].lub(a1._2, a2._2))

    override def glb(a1: (E1, E2), a2: (E1, E2)): (E1, E2) =
      (Lattice[E1].glb(a1._1, a2._1), Lattice[E2].glb(a1._2, a2._2))

    override def <=(a1: (E1, E2), a2: (E1, E2)): Boolean =
      Lattice[E1].<=(a1._1, a2._1) && Lattice[E2].<=(a1._2, a2._2)

    override def widen(a1: (E1, E2), a2: (E1, E2), depth: Int): (E1, E2) =
      (Lattice[E1].widen(a1._1, a2._1, depth), Lattice[E2].widen(a1._2, a2._2, depth))
  }

}
