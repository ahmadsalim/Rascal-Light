package semantics

import semantics.domains._
import syntax._

import scalaz.syntax.monad._
import scalaz.syntax.traverse._
import scalaz.std.option._
import scalaz.std.list._

case class Typing(module: domains.Module) {

  private def lub(types: List[Type]): Type =
    types.fold(VoidType) { (t1, t2) =>
      if (isSubType(t1, t2)) t2
      else if (isSubType(t2, t1)) t1
      else ValueType
    }

  private def inferType(basic: Basic): BasicType = basic match {
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
  
  def isSubType(t1: Type, t2: Type): Boolean = (t1, t2) match {
    case _ if t1 == t2 => true
    case (VoidType, _) => true
    case (_, ValueType) => true
    case (ListType(t1_), ListType(t2_)) => isSubType(t1_, t2_)
    case (SetType(t1_), SetType(t2_)) => isSubType(t1_, t2_)
    case (MapType(tk1, tv1), MapType(tk2, tv2)) => isSubType(tk1, tk2) && isSubType(tv1, tv2)
    case _ => false
  }
}

