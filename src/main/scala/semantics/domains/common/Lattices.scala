package semantics.domains.common

/**
  * Created by asal on 15/05/2017.
  */

sealed trait LatticeLimitation extends Exception
case object IsInfinite extends LatticeLimitation
case object IsEmpty extends LatticeLimitation

trait RSLattice[A, R, S] {
  def bot : A
  def top : A

  def isBot(r : R, s : S, a : A): Boolean = a == bot
  def isTop(r : R, s : S, a : A): Boolean = a == top

  def lub(r : R, s : S, a1 : A, a2 : A): (S, A)
  def glb(r : R, s : S, a1 : A, a2 : A): (S, A)
  def <=(r : R, s : S, a1 : A, a2 : A): Boolean
  def ===(r : R, s : S, a1 : A, a2 : A): Boolean = <=(r,s,a1,a2) && <=(r,s,a2,a1)
  def widen(r : R, s : S, a1 : A, a2 : A, bound : Int = 10): (S, A)

  final def lubs(r : R, s : S, as : Set[A]): (S, A) = as.foldLeft((s, bot)) { (st, a2) =>
    val (s2, a1) = st
    lub(r, s2, a1, a2)
  }
  final def glbs(r : R, s : S, as : Set[A]): (S, A) = as.foldLeft((s, top)) { (st, a2) =>
    val (s2, a1) = st
    glb(r, s2, a1, a2)
  }
}

object RSLattice {
  def apply[A, R, S](implicit lattas: RSLattice[A, R, S]): RSLattice[A, R, S] = lattas
}

trait Lattice[A] {
  def bot : A
  def top : A

  def isBot(a : A): Boolean = a == bot
  def isTop(a : A): Boolean = a == top

  def lub(a1 : A, a2 : A) : A
  def glb(a1 : A, a2 : A) : A
  def <=(a1 : A, a2 : A) : Boolean
  def ===(a1 : A, a2 : A): Boolean = <=(a1,a2) && <=(a2,a1)
  def widen(a1 : A, a2 : A, bound : Int = 10) : A

  final def lubs(as : Set[A]): A = as.fold(bot)(lub)
  final def glbs(as : Set[A]): A = as.fold(top)(glb)
}

object Lattice {
  def apply[A](implicit latta: Lattice[A]) = latta
}

object Lattices {
  implicit
  def latticeToRSLattice[A : Lattice, R, S] = new RSLattice[A, R, S] {
    override def bot: A = Lattice[A].bot

    override def top: A = Lattice[A].top

    override def lub(r: R, s: S, a1: A, a2: A): (S, A) = (s, Lattice[A].lub(a1, a2))

    override def glb(r: R, s: S, a1: A, a2: A): (S, A) = (s, Lattice[A].glb(a1, a2))

    override def <=(r: R, s: S, a1: A, a2: A): Boolean = Lattice[A].<=(a1, a2)

    override def widen(r: R, s: S, a1: A, a2: A, bound: Int): (S, A) = (s, Lattice[A].widen(a1, a2, bound))
  }
}