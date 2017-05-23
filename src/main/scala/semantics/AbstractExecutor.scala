package semantics

import semantics.domains.abstracting

import scalaz.syntax.monad._
import semantics.domains.abstracting.Memory.{AMemory, AResult, AValue}
import semantics.domains.abstracting.ValueShape.ValueShape
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
  def evalUnaryOp(op: OpName, av: AValue): Set[AResult[AValue]] = {
    val (avs, sym1) = av
    op match {
      case "-" =>
        ValueShape.toSign(avs).fold[Set[AResult[AValue]]] {
          if(ValueShape.isTop(avs))
            Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))),
              SuccessResult((ValueShape.fromSign(SignTop), Lattice[Flat[VarName]].top)))
          else Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
        } {
          case SignBot => Set(SuccessResult((ValueShape.fromSign(SignBot), Lattice[Flat[VarName]].bot)))
          case Neg => Set(SuccessResult((ValueShape.fromSign(Pos), Lattice[Flat[VarName]].top)))
          case NonPos => Set(SuccessResult((ValueShape.fromSign(NonNeg), Lattice[Flat[VarName]].top)))
          case Zero => Set(SuccessResult((ValueShape.fromSign(Zero), Lattice[Flat[VarName]].top)))
          case NonNeg => Set(SuccessResult((ValueShape.fromSign(NonPos), Lattice[Flat[VarName]].top)))
          case Pos => Set(SuccessResult((ValueShape.fromSign(Pos), Lattice[Flat[VarName]].top)))
          case SignTop => Set(SuccessResult((ValueShape.fromSign(SignTop), Lattice[Flat[VarName]].top)))
        }
      case "!" =>
        ValueShape.toDataShape(avs).fold[Set[AResult[AValue]]] {
          if(ValueShape.isTop(avs))
            Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))),
              SuccessResult((ValueShape.fromDataShape(DataAny("Bool")), Lattice[Flat[VarName]].top)))
          else Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
        } {
          case DataBot() => Set(SuccessResult((ValueShape.fromDataShape(DataBot()), Lattice[Flat[VarName]].top)))
          case DataElements("Bool", consShape) =>
            Set(SuccessResult((ValueShape.fromDataShape(DataShape.dataElements("Bool", consShape.map {
              case ("true", List()) => ("false", List())
              case ("false", List()) => ("true", List())
            })), Lattice[Flat[VarName]].top)))
          case DataAny("Bool") =>
            Set(SuccessResult((ValueShape.fromDataShape(DataAny("Bool")), Lattice[Flat[VarName]].top)))
          case DataTop() =>
            Set(SuccessResult((ValueShape.fromDataShape(DataAny("Bool")), Lattice[Flat[VarName]].top)),
              ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
          case _ =>  Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
        }
      case _ => Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
    }
  }

  private
  def evalUnary(localVars: Map[VarName, Type], acstore: ACStore, operator: OpName, operand: Expr): AMemories[AValue] = {
    val mems = evalLocal(localVars, acstore, operand)
    Lattice[AMemories[AValue]].lub(mems.memories.map { case (res, acstore_) =>
      res match {
        case SuccessResult(avl) => AMemories[AValue](evalUnaryOp(operator, avl).map((_, acstore_)))
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
              AMemories(Set[AMemory[AValue]]((SuccessResult((fromDataShape(ValueShape.DataShape.dataElements(typ,
               Map(name -> vals.map(_._1)))), Lattice[Flat[VarName]].top)), acstore_)))
            else AMemories(Set[AMemory[AValue]]((ExceptionalResult(Error(SignatureMismatch(name, vals.toList, parameters.map(_.typ)))), acstore_)))
          case ExceptionalResult(exres) => AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

  private
  def evalList(localVars: Map[VarName, Type], acstore: ACStore, elements: Seq[Expr]): AMemories[AValue] = {
    val eresmems = evalLocalAll(localVars, acstore, elements)
    Lattice[AMemories[AValue]].lub(eresmems.memories.map { case (res, acstore_) =>
        res match {
          case SuccessResult(vals) =>
            AMemories(Set[AMemory[AValue]]((SuccessResult((fromListShape(ListShape.listElements(Lattice[ValueShape].lub(vals.map(_._1).toSet))),Lattice[Flat[VarName]].top)), acstore_)))
          case ExceptionalResult(exres) => AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

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
  def evalLocalAll(localVars: Map[VarName, Type], acstore: ACStore, exprs: Seq[Expr]): AMemories[List[AValue]] = {
    val amemories = exprs.toList.foldLeft[AMemories[List[AValue]]](AMemories(Set((SuccessResult(List()), acstore)))) { (prevmems, e) =>
      AMemories[List[AValue]](prevmems.memories.flatMap[AMemory[List[AValue]], Set[AMemory[List[AValue]]]] { case (prevres, acstore__) =>
          prevres match {
            case SuccessResult(vals) =>
              val newmems = evalLocal(localVars, acstore__, e)
              newmems.memories.map { case (res, acstore_) =>
                res match {
                  case SuccessResult(vl) =>
                    (SuccessResult(vals :+ vl), acstore_)
                  case ExceptionalResult(exres) => (ExceptionalResult(exres), acstore_)
                }
              }
            case ExceptionalResult(exres) => Set[AMemory[List[AValue]]]((ExceptionalResult(exres), acstore__))
          }
      })
    }
    amemories
  }

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
