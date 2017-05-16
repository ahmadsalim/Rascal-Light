package semantics.domains.concrete

import semantics.domains.common.Module
import syntax._

sealed trait Value { val children: List[Value] }
case class BasicValue(b: Basic) extends Value {
  override val children: List[Value] = List()
  override val toString: String = s"$b"
}
case class ConstructorValue(name: ConsName, vals: Seq[Value]) extends Value {
  override val children: List[Value] = vals.toList
  override val toString: String = s"$name(${vals.mkString(",")})"
}
case class ListValue(vals: List[Value]) extends Value {
  override val children: List[Value] = vals
  override val toString: TypeName = s"[${vals.mkString(",")}]"
}
case class SetValue(vals: Set[Value]) extends Value {
  override val children: List[Value] = vals.toList
  override val toString: TypeName = s"{${vals.mkString(",")}}"
}
case class MapValue(vals: Map[Value, Value]) extends Value {
  override val children: List[Value] = vals.keys.toList ++ vals.values.toList
  override val toString: TypeName = s"(${vals.map(v => s"${v._1}: ${v._2}").mkString(",")})"
}
case object BottomValue extends Value {
  override val children: List[Value] = List()
  override val toString: TypeName = "⊥"
}

case class Store(map: Map[VarName, Value])

case class ExecutionResult(store: Store, module: Module, failingTests: List[VarName])

sealed trait Result[+T]
case class SuccessResult[T](t: T) extends Result[T]
case class ExceptionalResult[T](exres: Exceptional) extends Result[T]

sealed trait Exceptional
case class Return(value: Value) extends Exceptional
case class Throw(value: Value) extends Exceptional
case object Break extends Exceptional
case object Continue extends Exceptional
case object Fail extends Exceptional
case class Error(kind: ErrorKind) extends Exceptional

sealed trait ErrorKind
case class TypeError(value: Value, typ: Type) extends ErrorKind
case class FieldError(value: Value, fieldName: FieldName) extends ErrorKind
case class ReconstructError(value: Value, newchildren: List[Value]) extends ErrorKind
case class UnassignedVarError(varname: VarName) extends ErrorKind
case class NotEnumerableError(value: Value) extends ErrorKind
case class InvalidOperationError(opname: OpName, values: List[Value]) extends ErrorKind
case class SignatureMismatch(fun: Name, vals: List[Value], typ: List[Type]) extends ErrorKind
case object EscapedControlOperator extends ErrorKind
case class AssertionError(cond: Expr) extends ErrorKind
case object OtherError extends ErrorKind

case class DataPath(varName: VarName, accessPaths: List[AccessPath])
sealed trait AccessPath
case class MapAccessPath(value: Value) extends AccessPath
case class FieldAccessPath(fieldName: FieldName) extends AccessPath
