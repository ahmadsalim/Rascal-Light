package semantics

import semantics.domains.abstracting.Memory.AMemory
import semantics.domains.abstracting.{AMemories, MemoryOf}
import semantics.domains.common.{Lattice, Module}
import syntax.{Expr, Type, VarName}

case class AbstractExecutor(module: Module) {
  val Memory = MemoryOf(module)
  import Memory._

  private
  def evalLocal(localVars: Map[VarName, Type], mem: AMemory, expr: Expr): AMemories = ???

  def eval(mems: AMemories, expr: Expr): AMemories =
     implicitly[Lattice[AMemories]].lub(mems.memories.map(mem =>  evalLocal(Map.empty, mem, expr)))

}
