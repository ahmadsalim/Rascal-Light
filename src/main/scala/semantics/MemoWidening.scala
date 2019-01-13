package semantics

import semantics.domains.abstracting.RefinementType
import syntax.Type

sealed trait MemoWidening
case object SimpleWidening extends MemoWidening
case object TypeWidening extends MemoWidening
case class ConstructorWidening(depth: Int) extends MemoWidening