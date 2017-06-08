package semantics

import semantics.domains.common.{Lattice, Module}
import semantics.domains.concrete._
import TypeOps._
import syntax._

import scalaz.syntax.monad._
import scalaz.syntax.traverse._
import scalaz.std.option._
import scalaz.std.list._

case class Typing(module: Module) {

  private def lub(types: List[Type]): Type = Lattice[Type].lub(types.toSet)

  def inferType(basic: Basic): BasicType = basic match {
    case IntLit(i) => IntType
    case StringLit(s) => StringType
  }
  
  def inferType(value: Value): Option[Type] = value match {
    case BasicValue(b) => BaseType(inferType(b)).pure[Option]
    case ConstructorValue(cname, vals) =>
       module.constructors.get(cname).flatMap { case (typeName, parameters) =>
          if (vals.zip(parameters.map(_.typ)).forall((checkType _).tupled)) DataType(typeName).pure[Option]
          else None
       }
    case ListValue(vals) => vals.traverse(inferType).map(lub).map(ListType)
    case SetValue(vals) => vals.toList.traverse(inferType).map(lub).map(SetType)
    case MapValue(vals) =>
      vals.keys.toList.traverse(inferType).map(lub)
        .flatMap(keyType => vals.values.toList.traverse(inferType).map(lub)
        .map(valueType => MapType(keyType, valueType)))
    case BottomValue => VoidType.pure[Option]
  }
  def checkType(value: Value, typ: Type): Boolean = {
    val inferRes = inferType(value)
    inferRes.exists(inftyp => isSubType(inftyp, typ))
  }
  
  def isSubType(t1: Type, t2: Type): Boolean = Lattice[Type].<=(t1, t2)
}

