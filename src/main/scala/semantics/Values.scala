package semantics

import syntax.Basic


sealed trait Value
case class BasicValue(b: Basic) extends Value
case class ConstructorValue(vals: Seq[Value]) extends Value
case class ListValue(vals: List[Value]) extends Value
case class SetValue(vals: Set[Value]) extends Value
case class MapValue(vals: Map[Value, Value]) extends Value
case object BottomValue extends Value