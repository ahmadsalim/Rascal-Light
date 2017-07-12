package semantics.domains.common

/**
  * Created by asal on 15/05/2017.
  */

sealed trait LatticeLimitation extends Exception
case object IsInfinite extends LatticeLimitation
case object IsEmpty extends LatticeLimitation

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
  def apply[A](implicit latta: Lattice[A]): Lattice[A] = latta
}