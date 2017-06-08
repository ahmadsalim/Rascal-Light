package semantics

import semantics.domains.abstracting.{TypeMemories, TypeMemory}
import semantics.domains.abstracting.TypeMemory.{TypeResult, TypeStore}
import semantics.domains.common._
import semantics.domains.concrete.TypeOps._
import TypeMemory._
import syntax._

case class AbstractTypeExecutor(module: Module) {
  private
  val typing = Typing(module)

  private
  def getVar(store: TypeStore, x: VarName): Option[(Boolean, Type)] = store match {
    case FlatBot => None
    case FlatValue(storemap) => storemap.get(x)
    case FlatTop => Some((true, Lattice[Type].top))
  }

  def evalVar(store: TypeStore, x: VarName): TypeMemories[Type] = {
    val unassignedError = Set(TypeMemory[Type](ExceptionalResult(Error(UnassignedVarError(x))), store))
    getVar(store, x).fold(TypeMemories(unassignedError)) {
      case (possUnassigned, typ) =>
        TypeMemories((if (possUnassigned) unassignedError else Set()) ++ Set(TypeMemory(SuccessResult(typ), store)))
    }
  }

  def accessField(tv: Type, fieldName: FieldName): Set[TypeResult[Type]] = tv match {
    case DataType(name) =>
      val conss = module.datatypes(name)
      val fieldTypes = conss.map(cons => module.constructors(cons)._2.find(_.name == fieldName).map(_.typ))
      val successres: Set[TypeResult[Type]] = Set(SuccessResult(Lattice[Type].lub(fieldTypes.flatten.toSet)))
      if (fieldTypes.forall(_.isDefined)) successres
      else Set(ExceptionalResult(Error(FieldError(tv, fieldName)))) ++ successres
    case ValueType =>
      val fieldTypUB =
        Lattice[Type].lub(module.constructors.values.toSet[(TypeName, List[Parameter])].map(_._2)
                                .flatMap(pars => pars.find(_.name == fieldName).map(_.typ))) // Take lub of all possible field types
      Set(ExceptionalResult(Error(FieldError(tv, fieldName)))) ++ Set(SuccessResult(fieldTypUB))
    case _ => Set(ExceptionalResult(Error(FieldError(tv, fieldName))))
  }

  def evalFieldAccess(localVars: Map[VarName, Type], store: TypeStore, target: Expr, fieldName: FieldName): TypeMemories[Type] = {
    val targetmems = evalLocal(localVars, store, target)
    Lattice[TypeMemories[Type]].lub(targetmems.memories.flatMap { case TypeMemory(targetres, store_) =>
      targetres match {
        case SuccessResult(tv) => accessField(tv, fieldName).map(res => TypeMemories[Type](Set(TypeMemory(res, store_))))
        case _ => Set(TypeMemories[Type](Set(TypeMemory(targetres, store_))))
      }
    })
  }

  def evalUnaryOp(op: OpName, vl: Type): Set[TypeResult[Type]] = (op, vl) match {
    case ("-", BaseType(IntType)) => Set(SuccessResult(BaseType(IntType)))
    case ("-", ValueType) =>
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl))))) ++ Set(SuccessResult(BaseType(IntType)))
    case ("!", DataType("bool")) => Set(SuccessResult(DataType("bool")))
    case ("!", ValueType) =>
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl))))) ++ Set(SuccessResult(DataType("bool")))
    case _ => Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl)))))
  }

  def evalUnary(localVars: Map[VarName, Type], store: TypeStore, op: OpName, operand: Expr): TypeMemories[Type] = {
    val mems = evalLocal(localVars, store, operand)
    Lattice[TypeMemories[Type]].lub(mems.memories.flatMap { case TypeMemory(res, store_) =>
        res match {
          case SuccessResult(vl) =>
            evalUnaryOp(op, vl).map(res => TypeMemories(Set(TypeMemory(res, store_))))
          case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
        }
    })
  }

  def evalBinaryOp(lhval: Type, op: OpName, rhval: Type): Set[TypeResult[Type]] = ???
    /*(lhvl, op, rhvl) match {
      case (lhvl, "==", rhvl) =>
        (if (lhvl == rhvl) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (lhvl, "!=", rhvl) =>
        (if (lhvl != rhvl) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (lhvl, "in", ListValue(vs)) =>
        (if (vs.contains(lhvl)) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (lhvl, "in", SetValue(vs)) =>
        (if (vs.contains(lhvl)) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (lhvl, "in", MapValue(vs)) =>
        (if (vs.contains(lhvl)) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (lhvl, "notin", rhvl) => evalBinaryOp(lhvl, "in", rhvl).flatMap(v => evalUnaryOp("!", v))
      case (ConstructorValue("false", Seq()), "&&", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue("false", Seq()).point[Result]
      case (ConstructorValue("true", Seq()), "&&", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue(bnm, Seq()).point[Result]
      case (ConstructorValue("true", Seq()), "||", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue("true", Seq()).point[Result]
      case (ConstructorValue("false", Seq()), "||", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue(bnm, Seq()).point[Result]
      case (MapValue(vs), "delete", rhvl) => MapValue(vs - rhvl).point[Result]
      case (BasicValue(StringLit(s1)), "+", BasicValue(StringLit(s2))) => BasicValue(StringLit(s1 + s2)).point[Result]
      case (BasicValue(IntLit(i1)), "+", BasicValue(IntLit(i2))) => BasicValue(IntLit(i1 + i2)).point[Result]
      case (BasicValue(IntLit(i1)), "-", BasicValue(IntLit(i2))) => BasicValue(IntLit(i1 - i2)).point[Result]
      case (BasicValue(IntLit(i1)), "*", BasicValue(IntLit(i2))) => BasicValue(IntLit(i1 * i2)).point[Result]
      case (BasicValue(IntLit(i1)), "/", BasicValue(IntLit(i2)))  =>
        if (i2 == 0) ExceptionalResult(Throw(ConstructorValue("DivByZero", List())))
        else BasicValue(IntLit(i1 / i2)).point[Result]
      case (BasicValue(IntLit(i1)), "%", BasicValue(IntLit(i2))) =>
        if (i2 <= 0) ExceptionalResult(Throw(ConstructorValue("ModNonPos", List())))
        else BasicValue(IntLit(i1 % i2)).point[Result]
      case _ => ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl))))
    }*/

  def evalBinary(localVars: Map[VarName, Type], store: TypeStore, left: Expr, op: OpName, right: Expr): TypeMemories[Type] = {
    val leftmems = evalLocal(localVars, store, left)
    Lattice[TypeMemories[Type]].lub(leftmems.memories.flatMap { case TypeMemory(lhres, store__) =>
        lhres match {
          case SuccessResult(lhval) =>
            val rightmems = evalLocal(localVars, store__, right)
            rightmems.memories.flatMap { case TypeMemory(rhres, store_) =>
                rhres match {
                  case SuccessResult(rhval) =>
                    evalBinaryOp(lhval, op, rhval).map(res => TypeMemories[Type](Set(TypeMemory(res, store_))))
                  case _ => Set(TypeMemories[Type](Set(TypeMemory(rhres, store_))))
                }
            }
          case _ => Set(TypeMemories[Type](Set(TypeMemory(lhres, store__))))
        }
    })
  }

  def evalConstructor(localVars: Map[VarName, Type], store: TypeStore, name: ConsName, args: Seq[Expr]): TypeMemories[Type] = ???

  def evalList(localVars: Map[VarName, Type], store: TypeStore, elements: Seq[Expr]): TypeMemories[Type] = ???

  def evalSet(localVars: Map[VarName, Type], store: TypeStore, elements: Seq[Expr]): TypeMemories[Type] = ???

  def evalMap(localVars: Map[VarName, Type], store: TypeStore, keyvalues: Seq[(Expr, Expr)]): TypeMemories[Type] = ???

  def evalMapLookup(localVars: Map[VarName, Type], store: TypeStore, emap: Expr, ekey: Expr): TypeMemories[Type] = ???

  def evalMapUpdate(localVars: Map[VarName, Type], store: TypeStore, emap: Expr, ekey: Expr, evl: Expr): TypeMemories[Type] = ???

  def evalFunCall(localVars: Map[VarName, Type], store: TypeStore, functionName: VarName, args: Seq[Expr]): TypeMemories[Type] = ???

  def evalReturn(localVars: Map[VarName, Type], store: TypeStore, evl: Expr): TypeMemories[Type] = ???

  def evalAssign(localVars: Map[VarName, Type], store: TypeStore, assgn: Assignable, targetexpr: Expr): TypeMemories[Type] = ???

  def evalIf(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, thenB: Expr, elseB: Expr): TypeMemories[Type] = ???

  def evalSwitch(localVars: Map[VarName, Type], store: TypeStore, scrutinee: Expr, cases: Seq[Case]): TypeMemories[Type] = ???

  def evalVisit(localVars: Map[VarName, Type], store: TypeStore, strategy: Strategy, scrutinee: Expr, cases: Seq[Case]): TypeMemories[Type] = ???

  def evalBlock(localVars: Map[VarName, Type], store: TypeStore, vardefs: Seq[Parameter], exprs: Seq[Expr]): TypeMemories[Type] = ???

  def evalFor(localVars: Map[VarName, Type], store: TypeStore, enum: Enum, body: Expr): TypeMemories[Type] = ???

  def evalWhile(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, body: Expr): TypeMemories[Type] = ???

  def evalSolve(localVars: Map[VarName, Type], store: TypeStore, vars: Seq[VarName], body: Expr): TypeMemories[Type] = ???

  def evalThrow(localVars: Map[VarName, Type], store: TypeStore, evl: Expr): TypeMemories[Type] = ???

  def evalTryCatch(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, catchVar: VarName, catchB: Expr): TypeMemories[Type] = ???

  def evalTryFinally(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, finallyB: Expr): TypeMemories[Type] = ???

  def evalEnumExpr(localVars: Map[VarName, Type], store: TypeStore, enum: Enum): TypeMemories[Type] = ???

  def evalAssert(localVars: Map[VarName, Type], store: TypeStore, cond: Expr): TypeMemories[Type] = ???

  def evalLocal(localVars: Map[VarName, Type], store: TypeStore, expr: Expr): TypeMemories[Type] = {
    expr match {
      case BasicExpr(b) => TypeMemories(Set(TypeMemory(SuccessResult(BaseType(typing.inferType(b))), store)))
      case VarExpr(x) => evalVar(store, x)
      case FieldAccExpr(target, fieldName) => evalFieldAccess(localVars, store, target, fieldName)
      case UnaryExpr(op, operand) => evalUnary(localVars, store, op, operand)
      case BinaryExpr(left, op, right) => evalBinary(localVars, store, left, op, right)
      case ConstructorExpr(name, args) => evalConstructor(localVars, store, name, args)
      case ListExpr(elements) => evalList(localVars, store, elements)
      case SetExpr(elements) => evalSet(localVars, store, elements)
      case MapExpr(keyvalues) => evalMap(localVars, store, keyvalues)
      case MapLookupExpr(emap, ekey) => evalMapLookup(localVars, store, emap, ekey)
      case MapUpdExpr(emap, ekey, evl) => evalMapUpdate(localVars, store, emap, ekey, evl)
      case FunCallExpr(functionName, args) => evalFunCall(localVars, store, functionName, args)
      case ReturnExpr(evl) => evalReturn(localVars, store, evl)
      case AssignExpr(assgn, targetexpr) => evalAssign(localVars, store, assgn, targetexpr)
      case IfExpr(cond, thenB, elseB) => evalIf(localVars, store, cond, thenB, elseB)
      case SwitchExpr(scrutinee, cases) => evalSwitch(localVars, store, scrutinee, cases)
      case VisitExpr(strategy, scrutinee, cases) => evalVisit(localVars, store, strategy, scrutinee, cases)
      case BreakExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Break), store)))
      case ContinueExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Continue), store)))
      case FailExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Fail), store)))
      case LocalBlockExpr(vardefs, exprs) => evalBlock(localVars, store, vardefs, exprs)
      case ForExpr(enum, body) => evalFor(localVars, store, enum, body)
      case WhileExpr(cond, body) => evalWhile(localVars, store, cond, body)
      case SolveExpr(vars, body) => evalSolve(localVars, store, vars, body)
      case ThrowExpr(evl) => evalThrow(localVars, store, evl)
      case TryCatchExpr(tryB, catchVar, catchB) => evalTryCatch(localVars, store, tryB, catchVar, catchB)
      case TryFinallyExpr(tryB, finallyB) => evalTryFinally(localVars, store, tryB, finallyB)
      case EnumExpr(enum) => evalEnumExpr(localVars, store, enum)
      case AssertExpr(cond) => evalAssert(localVars, store, cond)
    }
  }

  def eval(store: TypeStore, expr: Expr): TypeMemories[Type] = evalLocal(Map.empty, store, expr)
}
