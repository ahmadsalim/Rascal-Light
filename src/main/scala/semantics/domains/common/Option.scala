package semantics.domains.common

/**
  * Created by asal on 25/05/2017.
  */
object Option {

  implicit def optionLattice[E : Lattice] = new Lattice[Option[E]] {
    override def isBot(a: Option[E]): Boolean = a.isEmpty

    override def isTop(a: Option[E]): Boolean = a.nonEmpty && Lattice[E].isTop(a.get)

    override def bot: Option[E] = None

    override def top: Option[E] = Some(Lattice[E].top)

    override def lub(a1: Option[E], a2: Option[E]): Option[E] =
      a1.fold(a2)(a1e => a2.fold(a1)(a2e => Some(Lattice[E].lub(a1e, a2e))))

    override def glb(a1: Option[E], a2: Option[E]): Option[E] = a1.flatMap(a1e => a2.map(a2e => Lattice[E].glb(a1e, a2e)))

    override def <=(a1: Option[E], a2: Option[E]): Boolean = a1.forall(a1e => a2.exists(a2e => Lattice[E].<=(a1e, a2e)))

    override def widen(a1: Option[E], a2: Option[E], bound: Int): Option[E] =
      a1.fold(a2)(a1e => a2.fold(a1)(a2e => Some(Lattice[E].widen(a1e, a2e, bound))))
  }

}
