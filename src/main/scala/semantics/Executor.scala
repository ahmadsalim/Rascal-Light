package semantics

import syntax.{Module => _, _}

import scalaz.\/
import scalaz.std.list._
import scalaz.syntax.either._
import scalaz.syntax.foldable._
import scalaz.syntax.monad._

object Executor {
  def evalUnary(op: OpName, vl: Value): Result[Value] = ???

  def evalBinary(lhvl: Value, op: OpName, rhvl: Value): Result[Value] = ???

  def eval(module: Module, store: Store, expr: Expr): (Result[Value], Store) = {
    def evalLocal(localVars: Map[VarName, Type], store: Store, expr: Expr): (Result[Value], Store) =
      expr match {
        case BasicExpr(b) => (BasicValue(b).point[Result], store)
        case VarExpr(x) =>
          if (store.map.contains(x)) (store.map(x).point[Result], store)
          else (ExceptionalResult(Error), store)
        case UnaryExpr(op, operand) =>
          val (res, store_) = evalLocal(localVars, store, operand)
          (res.flatMap(vl => evalUnary(op, vl)), store_)
        case BinaryExpr(left, op, right) =>
          val (lhres, store__) = evalLocal(localVars, store, left)
          lhres match {
            case SuccessResult(lhval) =>
              val (rhres, store_) = evalLocal(localVars, store__, right)
              (rhres.flatMap(rhval => evalBinary(lhval, op, rhval)), store_)
            case _ => (lhres, store__)
          }
        case ConstructorExpr(name, args) => ???
        case ListExpr(elements) => ???
        case SetExpr(elements) => ???
        case MapExpr(keyvalues) => ???
        case LookupExpr(emap, ekey) => ???
        case UpdateExpr(emap, ekey, evl) => ???
        case FunCallExpr(functionName, args) => ???
        case ReturnExpr(result) => ???
        case AssignExpr(name, expr) => ???
        case IfExpr(cond, thenB, elseB) => ???
        case SwitchExpr(scrutinee, cases) => ???
        case VisitExpr(strategy, scrutinee, cases) => ???
        case BreakExpr => (ExceptionalResult(Break), store)
        case ContinueExpr => (ExceptionalResult(Continue), store)
        case FailExpr => (ExceptionalResult(Fail), store)
        case LocalBlockExpr(vardefs, exprs) =>
          val localVars_ = vardefs.toList.foldLeft(localVars) { (lvs, vdef) =>
            lvs.updated(vdef.name, vdef.typ)
          }
          exprs.toList.foldLeft[(Result[Value], Store)]((BottomValue.pure[Result], store)) { (st, e) =>
            val (prevres, store__) = st
            prevres match {
              case SuccessResult(t) => evalLocal(localVars_, store__, e)
              case _ => (prevres, store__)
            }
          }
        case ForExpr(enum, body) => ???
        case WhileExpr(cond, body) => ???
        case SolveExpr(vars, body) => ???
        case ThrowExpr(result) => ???
        case TryCatchExpr(tryB, catchVar, catchB) => ???
        case TryFinallyExpr(tryB, finallyB) => ???
        case EnumExpr(enum) => ???
      }
    evalLocal(Map.empty, store, expr)
  }

  def execute(module: syntax.Module): String \/ (Store, Module) = {
    def alreadyDefined(name: Name, outmod: Module): Boolean = {
      outmod.funs.contains(name) || outmod.globalVars.contains(name) ||
        outmod.datatypes.contains(name) || outmod.constructors.contains(name)
    }
    def alreadyDefinedErrMsg(name: Name) = s"duplicate definition in module of name: $name"
    def constructorTypeSameNameErrMsg(name: Name) = s"constructor $name has the same name as the data type"
    val transr = module.defs.toList.foldLeftM[String \/ ?, (List[(VarName, Expr)], Module)](
      (List.empty, Module(Map.empty, Map.empty, Map.empty, Map.empty))) { (st, df) =>
        val (unevalglobvars, outmod) = st
        df match {
          case GlobalVarDef(typ, name, initialValue) =>
            if (alreadyDefined(name, outmod)) alreadyDefinedErrMsg(name).left
            else ((name, initialValue) :: unevalglobvars,
                    outmod.copy(globalVars = outmod.globalVars.updated(name, typ))).right
          case FunDef(returntype, name, parameters, body) =>
            if (alreadyDefined(name, outmod)) alreadyDefinedErrMsg(name).left
            else (unevalglobvars,
                     outmod.copy(funs = outmod.funs.updated(name, (returntype, parameters.toList, body)))).right
          case DataDef(tyname, constructors) =>
            if (alreadyDefined(tyname, outmod)) alreadyDefinedErrMsg(tyname).left
            else {
              val consmapr = constructors.toList.foldLeftM[String \/ ?, Map[ConsName, (TypeName, List[Parameter])]](
                Map.empty
              ) { (consmap, cdf) =>
                  if (alreadyDefined(cdf.name, outmod)) alreadyDefinedErrMsg(cdf.name).left
                  else if (cdf.name == tyname) constructorTypeSameNameErrMsg(cdf.name).left
                  else consmap.updated(cdf.name, (tyname, cdf.parameters.toList)).right
              }
              consmapr.map { consmap => (unevalglobvars,
                  outmod.copy(datatypes = outmod.datatypes.updated(tyname, constructors.map(_.name).toList),
                              constructors = consmap)) }
            }
        }
    }
    transr.flatMap { case (unevalglobvars, semmod) =>
        unevalglobvars.foldLeftM[String \/ ?, Store](Store(Map.empty)) { (store, unevalglobvar) =>
          val (varname, varexpr) = unevalglobvar
          val (res, store_) = eval(semmod, store, varexpr)
          res match {
            case ExceptionalResult(exres) => s"Evaluation of left-hand side for variable $varname failed with $exres".left
            case SuccessResult(value) => store_.copy(map = store_.map.updated(varname, value)).right
          }
        }.map(store => (store, semmod))
    }
  }
}
