package semantics.domains.common

/**
  * Created by asal on 15/05/2017.
  */

trait Lattice[A] {
  def bot : A
  def top : A
  def lub(a1 : A, a2 : A) : A
  def glb(a1 : A, a2 : A) : A
  def <=(a1 : A, a2 : A) : Boolean
  def widen(a1 : A, a2 : A) : A
}

object Lattice {
  def apply[A](implicit latta: Lattice[A]) = latta
}

object latticesyntax {
  final def bot[A : Lattice] : A = implicitly[Lattice[A]].bot
  final def top[A : Lattice] : A = implicitly[Lattice[A]].top

  // Unicode
  final def ⊥[A : Lattice] : A = bot
  final def ⊤[A : Lattice] : A = top

  implicit class LatticeOps[A: Lattice](a1 : A) {
    final def lub(a2 : A) : A = implicitly[Lattice[A]].lub(a1,a2)
    final def glb(a2 : A) : A = implicitly[Lattice[A]].glb(a1,a2)
    final def <=(a2 : A) : Boolean = implicitly[Lattice[A]].<=(a1,a2)
    final def widen(a2 : A) = implicitly[Lattice[A]].widen(a1, a2)

    // Unicode
    final def ⊔(a2 : A) : A = lub(a2)
    final def ⊓(a2 : A) : A = glb(a2)
    final def ⊑(a2 : A) : Boolean = <=(a2)
    final def ∇(a2 : A) = widen(a2)
  }
}
