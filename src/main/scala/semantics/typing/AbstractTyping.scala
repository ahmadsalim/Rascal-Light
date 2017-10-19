package semantics.typing

import semantics.domains.abstracting._
import semantics.domains.common.Module
import syntax._

case class AbstractTyping(module: Module) {
  private val typing = Typing(module)

  def inferType(rtyp: RefinementType): Type = rtyp match {
    case BaseRefinementType(basicType) =>
      val bt = basicType match {
        case IntRefinementType(_) => IntType
        case StringRefinementType => StringType
      }
      BaseType(bt)
    case DataRefinementType(dataname, _) => DataType(dataname)
    case ListRefinementType(elementType,_) => ListType(inferType(elementType))
    case SetRefinementType(elementType,_) => SetType(inferType(elementType))
    case MapRefinementType(keyType, valueType,_) =>
      MapType(inferType(keyType), inferType(valueType))
    case NoRefinementType => VoidType
    case ValueRefinementType => ValueType
  }

  def checkType(rtyp: RefinementType, typ: Type): Set[Boolean] = {
    val inferredtyp = inferType(rtyp)
    isSubtype(inferredtyp, typ)
  }

  def isSubtype(ty1: Type, ty2: Type): Set[Boolean] = {
    //Assumes target type is not overapproximated
    if (typing.isSubType(ty1, ty2)) Set(true)
    else if (typing.isSubType(ty2, ty1)) { Set(true, false) }
    else Set(false)
  }
}