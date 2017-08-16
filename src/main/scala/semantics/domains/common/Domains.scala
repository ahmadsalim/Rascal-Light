package semantics.domains.common

import syntax._

case object NonNormalFormMemories extends Throwable

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
case class Error(kinds: Set[ErrorKind]) extends Exceptional[Nothing]

sealed trait ErrorKind
case class TypeError(value: Any, typ: Type) extends ErrorKind
case class FieldError(value: Any, fieldName: FieldName) extends ErrorKind
case class ReconstructError(value: Any, newchildren: List[Any]) extends ErrorKind
case class UnassignedVarError(varname: VarName) extends ErrorKind
case class NotEnumerableError(value: Any) extends ErrorKind
case class InvalidOperationError(opname: OpName, values: List[Any]) extends ErrorKind
case class SignatureMismatch(fun: Name, vals: List[Any], typ: List[Type]) extends ErrorKind
case object EscapedControlOperator extends ErrorKind
case class AssertionError(cond: Expr) extends ErrorKind
case object OtherError extends ErrorKind

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
    Map("Bool" -> List("true", "false"), "NoKey" -> List("nokey"), "Pair" -> List("pair"),
      "DivByZero" -> List("divByZero"), "ModNonPos" -> List("modNonPos")),
    Map("true" -> ("Bool", List()),
        "false" -> ("Bool", List()),
        "nokey" -> ("NoKey", List(Parameter(ValueType, "key"))),
        "divByZero" -> ("DivByZero", List()),
        "modNonPos" -> ("ModNonPos", List()),
        "pair" -> ("Pair", List(Parameter(ValueType, "fst"), Parameter(ValueType, "snd")))))
}