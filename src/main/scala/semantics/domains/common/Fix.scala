package semantics.domains.common

import scalaz.~>
import scala.language.higherKinds

case class Fix[F[_]](out : F[Fix[F]])

object Fix {
  implicit def FixLattice[F[_]] (implicit flattice : Lattice ~> Lambda[E => Lattice[F[E]]]) : Lattice[Fix[F]] = new Lattice[Fix[F]] {
    override def bot: Fix[F] = Fix(flattice(this).bot)

    override def top: Fix[F] = Fix(flattice(this).top)

    override def lub(a1: Fix[F], a2: Fix[F]): Fix[F] = Fix(flattice(this).lub(a1.out, a2.out))

    override def glb(a1: Fix[F], a2: Fix[F]): Fix[F] = Fix(flattice(this).glb(a1.out, a2.out))

    override def <=(a1: Fix[F], a2: Fix[F]): Boolean = flattice(this).<=(a1.out, a2.out)

    override def widen(a1: Fix[F], a2: Fix[F], depth: Int): Fix[F] = Fix(flattice(this).widen(a1.out,a2.out,depth - 1))
  }
}