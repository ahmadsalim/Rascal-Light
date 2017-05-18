package semantics.domains.abstracting

import semantics.domains.common.DataPath
import syntax.{ConsName, OpName, VarName}

sealed trait RelCt
// TO DO Support map constraints
case class CaseCt(dataPath: DataPath[Nothing], cons: ConsName, phi: RelCt) extends RelCt
case class OpCt(lhs: DataPath[Nothing], op: OpName, rhs: DataPath[Nothing]) extends RelCt
case class IndCallCt(p: VarName, path: DataPath[Nothing]) extends RelCt
case class AndCt(lhs: DataPath[Nothing], rhs: DataPath[Nothing]) extends RelCt
case class OrCt(lhs: DataPath[Nothing], rhs: DataPath[Nothing]) extends RelCt
case object TrueCt extends RelCt
case object FalseCt extends RelCt
