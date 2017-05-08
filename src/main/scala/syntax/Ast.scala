package syntax


case class Module(defs: Seq[Def])

sealed trait Def
case class GlobalVarDef(typ: Type, name: VarName, initialValue: Expr) extends Def
case class FunDef(returntype: Type, name: VarName, parameters: Seq[Parameter], body: Expr) extends Def
case class DataDef(name: TypeName, constructors: Seq[ConstructorDef]) extends Def

case class ConstructorDef(name: ConsName, parameters: Seq[Parameter])

case class Parameter(typ: Type, name: VarName)

sealed trait Basic
case class IntLit(i: Int) extends Basic
case class StringLit(s: String) extends Basic

// Not strictly necessary part of semantics, but convenient
// and makes it easier to part programs without much rewriting involved
sealed trait Assignable
case class VarAssgn(name: VarName) extends Assignable
case class FieldAccAssgn(target: Assignable, fieldName: FieldName) extends Assignable
case class MapUpdAssgn(target: Assignable, ekey: Expr) extends Assignable

sealed trait Expr
case class BasicExpr(b: Basic) extends Expr
case class VarExpr(name: VarName) extends Expr
case class FieldAccExpr(target: Expr, fieldName: FieldName) extends Expr
case class UnaryExpr(name: OpName, operand : Expr) extends Expr
case class BinaryExpr(left: Expr, name: OpName, right: Expr) extends Expr
case class ConstructorExpr(name: ConsName, args: Seq[Expr]) extends Expr
case class ListExpr(elements: Seq[Expr]) extends Expr
case class SetExpr(elements: Seq[Expr]) extends Expr
case class MapExpr(keyvalues: Seq[(Expr, Expr)]) extends Expr
case class MapLookupExpr(emap: Expr, ekey: Expr) extends Expr
case class MapUpdExpr(emap: Expr, ekey: Expr, eval: Expr) extends Expr
case class FunCallExpr(functionName: VarName, args: Seq[Expr]) extends Expr
case class ReturnExpr(result: Expr) extends Expr
case class AssignExpr(assgn: Assignable, expr : Expr) extends Expr
case class IfExpr(cond: Expr, thenB: Expr, elseB: Expr) extends Expr
case class SwitchExpr(scrutinee: Expr, cases: Seq[Case]) extends Expr
case class VisitExpr(strategy: Strategy, scrutinee: Expr, cases: Seq[Case]) extends Expr
case object BreakExpr extends Expr
case object ContinueExpr extends Expr
case object FailExpr extends Expr
case class LocalBlockExpr(vardefs: Seq[Parameter], exprs: Seq[Expr]) extends Expr
case class ForExpr(enum: Enum, body: Expr) extends Expr
case class WhileExpr(cond: Expr, body: Expr) extends Expr
case class SolveExpr(vars: Seq[VarName], body: Expr) extends Expr
case class ThrowExpr(result: Expr) extends Expr
case class TryCatchExpr(tryB: Expr, catchVar: VarName, catchB: Expr) extends Expr
case class TryFinallyExpr(tryB: Expr, finallyB: Expr) extends Expr
case class EnumExpr(enum: Enum) extends Expr
case class AssertExpr(cond: Expr) extends Expr

case class Case(patt: Patt, action: Expr)

sealed trait Enum
case class MatchAssign(patt: Patt, target: Expr) extends Enum
case class EnumAssign(varname: VarName, target: Expr) extends Enum

sealed trait Strategy
case object TopDown extends Strategy
case object TopDownBreak extends Strategy
case object BottomUp extends Strategy
case object BottomUpBreak extends Strategy
case object Innermost extends Strategy
case object Outermost extends Strategy

sealed trait Patt
case class BasicPatt(b: Basic) extends Patt
case object IgnorePatt extends Patt
case class VarPatt(name: VarName) extends Patt
case class ConstructorPatt(name: ConsName, pats: Seq[Patt]) extends Patt
case class LabelledTypedPatt(typ: Type, labelVar: VarName, patt: Patt) extends Patt
case class ListPatt(spatts: Seq[StarPatt]) extends Patt
case class SetPatt(spatts: Seq[StarPatt]) extends Patt
case class DescendantPatt(patt: Patt) extends Patt

sealed trait StarPatt
case class OrdinaryPatt(p: Patt) extends StarPatt
case class ArbitraryPatt(name: VarName) extends StarPatt

sealed trait BasicType
case object IntType extends BasicType
case object StringType extends BasicType
sealed trait Type
case class BaseType(b: BasicType) extends Type
case class DataType(name: TypeName) extends Type
case class ListType(elementType: Type) extends Type
case class SetType(elementType: Type) extends Type
case class MapType(keyType: Type, valueType: Type) extends Type
case object VoidType extends Type
case object ValueType extends Type
