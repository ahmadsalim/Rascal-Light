package semantics.domains.abstracting

import semantics.Result
import semantics.domains.common.{Module, ResultV}
import syntax.VarName

case class MemoryOf(module: Module) {
  val ValueShape = ValueShapeOf(module)
  type ValueShape = ValueShape.ValueShape

  type AValue = (ValueShape, Symbol)

  type AStore = Map[VarName, AValue]

  type AResult[T] = ResultV[Unit, T]

  type AMemory = List[(AResult[AValue], AStore, RelCt)]
}
