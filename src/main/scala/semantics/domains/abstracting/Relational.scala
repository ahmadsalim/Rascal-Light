package semantics.domains.abstracting

import semantics.domains.common.{DataPath, Lattice}
import syntax.{ConsName, OpName, VarName}

sealed trait RelCt
// TO DO Support map constraints
case class IsCt(dataPath: DataPath[Nothing], cons: ConsName) extends RelCt
case class OpCt(lhs: DataPath[Nothing], op: OpName, rhs: DataPath[Nothing]) extends RelCt
case class IndCallCt(p: VarName, path: DataPath[Nothing]) extends RelCt
case class AndCt(phi: RelCt, psi: RelCt) extends RelCt
case class OrCt(phi: RelCt, psi: RelCt) extends RelCt
case class NotCt(phi: RelCt) extends RelCt
case object TrueCt extends RelCt
case object FalseCt extends RelCt

object Relational {
  implicit val RelCtLattice: Lattice[RelCt] = new Lattice[RelCt] {
    override def bot: RelCt = FalseCt

    override def top: RelCt = TrueCt

    override def lub(a1: RelCt, a2: RelCt): RelCt = OrCt(a1,a2)

    override def glb(a1: RelCt, a2: RelCt): RelCt = AndCt(a1, a2)

    override def <=(a1: RelCt, a2: RelCt): Boolean = ???
    // TODO Call SMT solver

    override def widen(a1: RelCt, a2: RelCt, depth: Int): RelCt = ???
    // TODO Call SMT solver
  }
}