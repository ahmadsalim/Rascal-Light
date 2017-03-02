package semantics.domains

import syntax.{Module => _, _}

case class Module( globalVars: Map[VarName, Type]
                 , funs: Map[VarName, (Type, List[Parameter], Expr)]
                 , datatypes: Map[TypeName, List[ConsName]]
                 , constructors: Map[ConsName, (TypeName, List[Parameter])]
                 )

sealed trait Value { val children: List[Value] }
case class BasicValue(b: Basic) extends Value { override val children: List[Value] = List() }
case class ConstructorValue(name: ConsName, vals: Seq[Value]) extends Value { override val children: List[Value] = vals.toList }
case class ListValue(vals: List[Value]) extends Value { override val children: List[Value] = vals }
case class SetValue(vals: Set[Value]) extends Value { override val children: List[Value] = vals.toList }
case class MapValue(vals: Map[Value, Value]) extends Value { override val children: List[Value] = vals.keys.toList ++ vals.values.toList }
case object BottomValue extends Value { override val children: List[Value] = List() }

case class Store(map: Map[VarName, Value])

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
case class ReconstructError(value: Value, newchildren: List[Value]) extends ErrorKind
case class UnassignedVarError(varname: VarName) extends ErrorKind
case class NotEnumerableError(value: Value) extends ErrorKind
case class InvalidOperationError(opname: OpName, values: List[Value]) extends ErrorKind
case class SignatureMismatch(fun: Name, vals: List[Value], typ: List[Type]) extends ErrorKind
case object EscapedControlOperator extends ErrorKind
case object OtherError extends ErrorKind

object Domains {
  val prelude = Module(Map.empty, Map.empty,
    Map("Bool" -> List("true", "false"), "NoKey" -> List("nokey"), "Pair" -> List("pair")),
    Map("true" -> ("Bool", List()),
        "false" -> ("Bool", List()),
        "nokey" -> ("NoKey", List(Parameter(ValueType, "key"))),
        "pair" -> ("Pair", List(Parameter(ValueType, "fst"), Parameter(ValueType, "snd")))))
}