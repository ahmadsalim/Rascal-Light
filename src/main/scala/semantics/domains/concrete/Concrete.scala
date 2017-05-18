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

