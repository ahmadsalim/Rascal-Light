package semantics

import semantics.domains.abstracting

import scalaz.syntax.monad._
import semantics.domains.abstracting.Memory.{AMemory, AResult, AValue}
import semantics.domains.abstracting.ValueShape.{ValueShape, fromDataShape}
import semantics.domains.abstracting._
import semantics.domains.common._
import syntax._
import semantics.domains.concrete.{BasicValue, Value}

case class AbstractExecutor(module: Module) {
  val Memory = MemoryOf(module)

  import Memory._
  import Memory.ValueShape._

  private
  def evalVar(acstore: ACStore, x: VarName): AMemories[AValue] = {
    acstore.store match {
      case StoreTop => AMemories[AValue](Set((SuccessResult((Lattice[ValueShape].top, Lattice[Flat[VarName]].top)), acstore)))
      case AbstractStore(store) =>
        if (store.contains(x)) AMemories[AValue](Set((SuccessResult(store(x)), acstore)))
        else AMemories[AValue](Set((ExceptionalResult(Error(UnassignedVarError(x))), acstore)))
    }
  }

  private
  def evalUnaryOp(av: AValue): AResult[AValue] = ???

  private
  def evalUnary(localVars: Map[VarName, Type], acstore: ACStore, name: OpName, operand: Expr): AMemories[AValue] = {
    val mems = evalLocal(localVars, acstore, operand)
    Lattice[AMemories[AValue]].lub(mems.memories.map { case (res, acstore_) =>
      res match {
        case SuccessResult(avl) => AMemories[AValue](Set((SuccessResult(avl), acstore_)))
        case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acstore_)))
      }
    })
  }

  private
  def evalFieldAccess(localVars: Map[VarName, Type], acstore: ACStore, target: Expr, fieldName: FieldName): AMemories[AValue] = ???

  private
  def evalBinary(localVars: Map[VarName, Type], acstore: ACStore, left: Expr, name: OpName, right: Expr): AMemories[AValue] = ???

  private
  def evalConstructor(localVars: Map[VarName, Type], acstore: ACStore, name: ConsName, args: Seq[Expr]): AMemories[AValue] = {
    val argsresmems = evalLocalAll(localVars, acstore, args)
    Lattice[AMemories[AValue]].lub(argsresmems.memories.map { case (argres, acstore_) =>
        argres match {
          case SuccessResult(vals) =>
            val (typ, parameters) = module.constructors(name)
            if (vals.length == parameters.length)
            // TODO Check types: vals.zip(parameters.map(_.typ)).forall((typing.checkType _).typed)
            // TODO Abstract relational constraints via paths
              AMemories(Set[AMemory[AValue]]((SuccessResult((fromDataShape(DataElements[ValueShape](typ,
               Map(name -> vals.map(_._1).toList))), Lattice[Flat[VarName]].top)), acstore_)))
            else AMemories(Set[AMemory[AValue]]((ExceptionalResult(Error(SignatureMismatch(name, vals.toList, parameters.map(_.typ)))), acstore_)))
          case ExceptionalResult(exres) => AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

  private
  def evalList(localVars: Map[VarName, Type], acstore: ACStore, elements: Seq[Expr]): AMemories[AValue] = ???

  private
  def evalSet(localVars: Map[VarName, Type], acstore: ACStore, elements: Seq[Expr]): AMemories[AValue] = ???

  private
  def evalMap(localVars: Map[VarName, Type], acstore: ACStore, keyvalues: Seq[(Expr, Expr)]): AMemories[AValue] = ???

  private
  def evalMapLookup(localVars: Map[VarName, Type], acstore: ACStore, emap: Expr, ekey: Expr): AMemories[AValue] = ???

  private
  def evalMapUpdate(localVars: Map[VarName, Type], acstore: ACStore, emap: Expr, ekey: Expr, eval: Expr): AMemories[AValue] = ???

  private
  def evalFunCall(localVars: Map[VarName, Type], acstore: ACStore, functionName: VarName, args: Seq[Expr]): AMemories[AValue] = ???

  private
  def evalReturn(localVars: Map[VarName, Type], acstore: ACStore, result: Expr): AMemories[AValue] = {
    val resmems = evalLocal(localVars, acstore, result)
    Lattice[AMemories[AValue]].lub(resmems.memories.map { case (res, acstore_) =>
        res match {
          case SuccessResult(vl) =>
            AMemories(Set[AMemory[AValue]]((ExceptionalResult(Return(vl)), acstore_)))
          case ExceptionalResult(exres) =>
            AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

  private
  def evalAssign(localVars: Map[VarName, Type], acstore: ACStore, assgn: Assignable, expr: Expr): AMemories[AValue] = ???

  private
  def evalIf(localVars: Map[VarName, Type], acstore: ACStore, cond: Expr, thenB: Expr, elseB: Expr): AMemories[AValue] = ???

  private
  def evalSwitch(localVars: Map[VarName, Type], acstore: ACStore, scrutinee: Expr, cases: Seq[Case]): AMemories[AValue] = ???


  private
  def evalVisit(localVars: Map[VarName, Type], acstore: ACStore, strategy: Strategy, scrutinee: Expr, cases: Seq[Case]): AMemories[AValue] = ???

  private
  def evalBlock(localVars: Map[VarName, Type], acstore: ACStore, vardefs: Seq[Parameter], exprs: Seq[Expr]): AMemories[AValue] = ???

  private
  def evalFor(localVars: Map[VarName, Type], acstore: ACStore, enum: Enum, body: Expr): AMemories[AValue] = ???

  private
  def evalWhile(localVars: Map[VarName, Type], acstore: ACStore, cond: Expr, body: Expr): AMemories[AValue] = ???

  private
  def evalSolve(localVars: Map[VarName, Type], acstore: ACStore, vars: Seq[VarName], body: Expr): AMemories[AValue] = ???

  private
  def evalThrow(localVars: Map[VarName, Type], acstore: ACStore, result: Expr): AMemories[AValue] = {
    val resmems = evalLocal(localVars, acstore, result)
    Lattice[AMemories[AValue]].lub(resmems.memories.map { case (res, acstore_) =>
      res match {
        case SuccessResult(vl) =>
          AMemories(Set[AMemory[AValue]]((ExceptionalResult(Throw(vl)), acstore_)))
        case ExceptionalResult(exres) =>
          AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
      }
    })
  }


  private
  def evalTryCatch(localVars: Map[VarName, Type], acstore: ACStore, tryB: Expr, catchVar: VarName, catchB: Expr): AMemories[AValue] = ???

  private
  def evalTryFinally(localVars: Map[VarName, Type], acstore: ACStore, tryB: Expr, finallyB: Expr): AMemories[AValue] = ???

  def evalEnumExpr(localVars: Map[VarName, Type], acstore: ACStore, enum: Enum): AMemories[AValue] = ???

  def evalAssert(localVars: Map[VarName, Type], acstore: ACStore, cond: Expr): AMemories[AValue] = ???

  private
  def evalLocalAll(localVars: Map[VarName, Type], acstore: ACStore, args: Seq[Expr]): AMemories[Seq[AValue]] = ???

  private
  def evalLocal(localVars: Map[VarName, Type], acstore: ACStore, expr: Expr): AMemories[AValue] = expr match {
    case BasicExpr(b) =>
      AMemories[AValue](Set((SuccessResult((galois[Value, ValueShape].alpha(Set(BasicValue(b))), Lattice[Flat[VarName]].top)), acstore)))
    case VarExpr(name) => evalVar(acstore, name)
    case FieldAccExpr(target, fieldName) => evalFieldAccess(localVars, acstore, target, fieldName)
    case UnaryExpr(name, operand) => evalUnary(localVars, acstore, name, operand)
    case BinaryExpr(left, name, right) => evalBinary(localVars, acstore, left, name, right)
    case ConstructorExpr(name, args) => evalConstructor(localVars, acstore, name, args)
    case ListExpr(elements) => evalList(localVars, acstore, elements)
    case SetExpr(elements) => evalSet(localVars, acstore, elements)
    case MapExpr(keyvalues) => evalMap(localVars, acstore, keyvalues)
    case MapLookupExpr(emap, ekey) => evalMapLookup(localVars, acstore, emap, ekey)
    case MapUpdExpr(emap, ekey, eval) => evalMapUpdate(localVars, acstore, emap, ekey, eval)
    case FunCallExpr(functionName, args) => evalFunCall(localVars, acstore, functionName, args)
    case ReturnExpr(result) => evalReturn(localVars, acstore, result)
    case AssignExpr(assgn, expr) => evalAssign(localVars, acstore, assgn, expr)
    case IfExpr(cond, thenB, elseB) =>  evalIf(localVars, acstore, cond, thenB, elseB)
    case SwitchExpr(scrutinee, cases) =>  evalSwitch(localVars, acstore, scrutinee, cases)
    case VisitExpr(strategy, scrutinee, cases) => evalVisit(localVars, acstore, strategy, scrutinee, cases)
    case BreakExpr => AMemories[AValue](Set((ExceptionalResult(Break), acstore)))
    case ContinueExpr => AMemories[AValue](Set((ExceptionalResult(Continue), acstore)))
    case FailExpr => AMemories[AValue](Set((ExceptionalResult(Fail), acstore)))
    case LocalBlockExpr(vardefs, exprs) => evalBlock(localVars, acstore, vardefs, exprs)
    case ForExpr(enum, body) => evalFor(localVars, acstore, enum, body)
    case WhileExpr(cond, body) => evalWhile(localVars, acstore, cond, body)
    case SolveExpr(vars, body) => evalSolve(localVars, acstore, vars, body)
    case ThrowExpr(result) => evalThrow(localVars, acstore, result)
    case TryCatchExpr(tryB, catchVar, catchB) => evalTryCatch(localVars, acstore, tryB, catchVar, catchB)
    case TryFinallyExpr(tryB, finallyB) => evalTryFinally(localVars, acstore, tryB, finallyB)
    case EnumExpr(enum) => evalEnumExpr(localVars, acstore, enum)
    case AssertExpr(cond) => evalAssert(localVars, acstore, cond)
  }

  def eval(acstore: ACStore, expr: Expr): AMemories[AValue] = evalLocal(Map.empty, acstore, expr)

}
