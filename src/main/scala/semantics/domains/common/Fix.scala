package semantics.domains.common

import semantics.domains.common.Powerset.PowersetLattice

import scalaz.{~>, ~~>}
import scala.language.higherKinds
import scalaz.BijectionT.Bijection

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

  implicit def FixFixGalois[XCF[_], XF[_], CF[_], F[_]] // XF, XCF are for constraints
    (implicit flattice : Lattice ~> Lambda[E => Lattice[F[E]]]
    ,         xCF: XCF[Fix[CF]] // TO DO This seems hacky, but oh well!
    ,         xF: XF[Fix[F]]
    ,         cffgalois : Lambda[(CE,E) => (XCF[CE], XF[E], ConcreteAbstractGalois[CE,E])] ~~> Lambda[(CE, E) => ConcreteAbstractGalois[CF[CE], F[E]]]) =
      new ConcreteAbstractGalois[Fix[CF], Fix[F]] {
        private
        val cffgaloisres: ConcreteAbstractGalois[CF[Fix[CF]], F[Fix[F]]] = cffgalois((xCF, xF, this))

        override def latticeC: Lattice[Set[Fix[CF]]] = PowersetLattice

        override def latticeA: Lattice[Fix[F]] = FixLattice

        override def alpha(dcs: Set[Fix[CF]]): Fix[F] =
          Lattice[Fix[F]].lubs(dcs.map(cf => Fix(cffgaloisres.alpha(Set(cf.out)))))

        override def gamma(da: Fix[F], bound: Int): Set[Fix[CF]] =
          cffgaloisres.gamma(da.out, bound).map(Fix(_))
      }
}