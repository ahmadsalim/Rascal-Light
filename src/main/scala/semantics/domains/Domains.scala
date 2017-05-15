package semantics.domains

import syntax._

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