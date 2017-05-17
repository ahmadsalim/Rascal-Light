package semantics.domains.abstracting

import semantics.domains.common._

case class ValueShapeOf(module: Module) {
  type ValueShape = Fix[Sum3[?, Lambda[E => Sign], ListShape, DataShape]]

  val DataShape = DataShapeOf(module)
}
