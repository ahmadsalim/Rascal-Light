package semantics.domains.common

import syntax._

case class DataPath[+T](varName: VarName, accessPaths: List[AccessPath[T]])
sealed trait AccessPath[+T]
case class MapAccessPath[T](value: T) extends AccessPath[T]
case class FieldAccessPath(fieldName: FieldName) extends AccessPath[Nothing]

sealed trait ResultV[+V,+T]
case class SuccessResult[T](t: T) extends ResultV[Nothing,T]
case class ExceptionalResult[V,T](exres: Exceptional[V]) extends ResultV[V,T]

sealed trait Exceptional[+T]
case class Return[T](value: T) extends Exceptional[T]
case class Throw[T](value: T) extends Exceptional[T]
case object Break extends Exceptional[Nothing]
case object Continue extends Exceptional[Nothing]
case object Fail extends Exceptional[Nothing]
case class Error[T](kind: ErrorKind[T]) extends Exceptional[T]

sealed trait ErrorKind[+T]
case class TypeError[T](value: T, typ: Type) extends ErrorKind[T]
case class FieldError[T](value: T, fieldName: FieldName) extends ErrorKind[T]
case class ReconstructError[T](value: T, newchildren: List[T]) extends ErrorKind[T]
case class UnassignedVarError(varname: VarName) extends ErrorKind[Nothing]
case class NotEnumerableError[T](value: T) extends ErrorKind[T]
case class InvalidOperationError[T](opname: OpName, values: List[T]) extends ErrorKind[T]
case class SignatureMismatch[T](fun: Name, vals: List[T], typ: List[Type]) extends ErrorKind[T]
case object EscapedControlOperator extends ErrorKind[Nothing]
case class AssertionError(cond: Expr) extends ErrorKind[Nothing]
case object OtherError extends ErrorKind[Nothing]

sealed trait FunBody
case class ExprFunBody(expr: Expr) extends FunBody
case object PrimitiveFunBody extends FunBody

case class Module(globalVars: Map[VarName, Type]
                 , funs: Map[VarName, (Type, List[Parameter], FunBody)]
                 , datatypes: Map[TypeName, List[ConsName]]
                 , constructors: Map[ConsName, (TypeName, List[Parameter])]
                 )

object Domains {
  val prelude = Module(Map.empty,
    Map("delete" -> (MapType(ValueType, ValueType),
         List(Parameter(MapType(ValueType, ValueType),"emap"),
             Parameter(ValueType,"ekey")), PrimitiveFunBody)
       ,"toString" -> (BaseType(StringType), List(Parameter(ValueType, "earg")), PrimitiveFunBody)),
    Map("Bool" -> List("true", "false"), "NoKey" -> List("nokey"), "Pair" -> List("pair")),
    Map("true" -> ("Bool", List()),
        "false" -> ("Bool", List()),
        "nokey" -> ("NoKey", List(Parameter(ValueType, "key"))),
        "pair" -> ("Pair", List(Parameter(ValueType, "fst"), Parameter(ValueType, "snd")))))
}