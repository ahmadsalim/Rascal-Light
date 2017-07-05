package semantics.typing

import semantics.domains.common.{Lattice, Module}
import semantics.domains.concrete.TypeOps._
import semantics.domains.concrete._
import syntax._

import scalaz.std.list._
import scalaz.std.option._
import scalaz.syntax.monad._
import scalaz.syntax.traverse._

case class Typing(module: Module) {

  private def lubs(types: List[Type]): Type = Lattice[Type].lubs(types.toSet)

  def inferType(basic: Basic): BasicType = basic match {
    case IntLit(i) => IntType
    case StringLit(s) => StringType
  }
  
  def inferType(value: Value): Type = value match {
    case BasicValue(b) => BaseType(inferType(b))
    case ConstructorValue(cname, vals) =>
       val (typeName, _) = module.constructors(cname)
       DataType(typeName)
    case ListValue(vals) => ListType(lubs(vals.map(inferType)))
    case SetValue(vals) => SetType(lubs(vals.toList.map(inferType)))
    case MapValue(vals) =>
      val keyType = lubs(vals.keySet.toList.map(inferType))
      val valueType = lubs(vals.values.toList.map(inferType))
      MapType(keyType, valueType)
    case BottomValue => VoidType
  }
  def checkType(value: Value, typ: Type): Boolean = isSubType(inferType(value),typ)

  def isSubType(t1: Type, t2: Type): Boolean = Lattice[Type].<=(t1, t2)
}

