package semantics

import syntax.{IntLit, StringLit, Type}

object Typing {
  def valueTyping(value: Value, typ: Type): Boolean = value match {
    case ConstructorValue(vals) => ???
    case ListValue(vals) => ???
    case SetValue(vals) => ???
    case MapValue(vals) => ???
    case BottomValue => ???
    case BasicValue(IntLit(i)) => ???
    case BasicValue(StringLit(s)) => ???
  }
}
