package semantics

import syntax.{Module => _, _}

import scala.collection.immutable.Nil
import scalaz.\/
import scalaz.std.list._
import scalaz.syntax.either._
import scalaz.syntax.foldable._
import scalaz.syntax.monad._

object Executor {
  private
  def evalUnary(op: OpName, vl: Value): Result[Value] = ???

  private
  def evalBinary(lhvl: Value, op: OpName, rhvl: Value): Result[Value] = ???

  def eval(module: Module, store: Store, expr: Expr): (Result[Value], Store) = {
    val typing = Typing(module)

    def evalEach(localVars: Map[VarName, Type], store: Store, envs: List[Map[VarName, Value]], body: Expr): (Result[Unit], Store) = envs match {
      case Nil => (().point[Result], store)
      case env :: envs => ???
    }

    def evalLocalAll(localVars: Map[VarName, Type], store: Store, exprs: Seq[Expr]): (Result[List[Value]], Store) = {
      val (res, store_) = exprs.toList.foldLeft[(Result[List[Value]], Store)]((List().pure[Result], store)) { (st, e) =>
        val (prevres, store__) = st
        prevres match {
          case SuccessResult(vals) =>
            val (res, store_) = evalLocal(localVars, store__, e)
            (res.map(vl => vl :: vals), store_)
          case _ => (prevres, store__)
        }
      }
      (res.map(_.reverse), store_)
    }

    def evalEnum(localVars: Map[VarName, Type], store: Store, enum: Enum): (Result[List[Map[VarName, Value]]], Store) = ???

    def evalLocal(localVars: Map[VarName, Type], store: Store, expr: Expr): (Result[Value], Store) =
      expr match {
        case BasicExpr(b) => (BasicValue(b).pure[Result], store)
        case VarExpr(x) =>
          if (store.map.contains(x)) (store.map(x).pure[Result], store)
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
        case ConstructorExpr(name, args) =>
          val (res, store_) = evalLocalAll(localVars, store, args)
          res match {
            case SuccessResult(vals) =>
              val (_, parameters) = module.constructors(name)
              if (vals.length == parameters.length &&
                   vals.zip(parameters.map(_.typ)).forall((typing.checkType _).tupled))
                (ConstructorValue(name, vals).pure[Result], store_)
              else (ExceptionalResult(Error), store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case ListExpr(elements) =>
          val (res, store_) = evalLocalAll(localVars, store, elements)
          res match {
            case SuccessResult(vals) => (ListValue(vals).pure[Result], store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case SetExpr(elements) =>
          val (res, store_) = evalLocalAll(localVars, store, elements)
          res match {
            case SuccessResult(vals) => (SetValue(vals.toSet).pure[Result], store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case MapExpr(keyvalues) =>
          val (keyres, store__) = evalLocalAll(localVars, store, keyvalues.map(_._1))
          keyres match {
            case SuccessResult(keys) =>
              val (valres, store_) = evalLocalAll(localVars, store__, keyvalues.map(_._2))
              valres match {
                case SuccessResult(vals) =>
                  assert(keys.length == vals.length)
                  (MapValue(keys.zip(vals).toMap).pure[Result], store_)
                case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case LookupExpr(emap, ekey) =>
          val (mapres, store__) = evalLocal(localVars, store, emap)
          mapres match {
            case SuccessResult(mapv) =>
              mapv match {
                case MapValue(vals) =>
                  val (keyres, store_) = evalLocal(localVars, store__, ekey)
                  keyres match {
                    case SuccessResult(keyv) =>
                      if (vals.contains(keyv)) (vals(keyv).pure[Result], store_)
                      else (ExceptionalResult(Throw(ConstructorValue("nokey", Seq(keyv)))), store_)
                    case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
                  }
                case _ => (ExceptionalResult(Error), store__)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case UpdateExpr(emap, ekey, evl) =>
          val (mapres, store___) = evalLocal(localVars, store, emap)
          mapres match {
            case SuccessResult(mapv) =>
              mapv match {
                case MapValue(vals) =>
                  val (keyres, store__) = evalLocal(localVars, store___, ekey)
                  keyres match {
                    case SuccessResult(keyv) =>
                      val (valres, store_) = evalLocal(localVars, store__, evl)
                      valres match {
                        case SuccessResult(valv) => (MapValue(vals.updated(keyv, valv)).pure[Result], store_)
                        case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
                      }
                    case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
                  }
                case _ => (ExceptionalResult(Error), store___)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store___)
          }
        case FunCallExpr(functionName, args) =>
          val (argres, store__) = evalLocalAll(localVars, store, args)
          argres match {
            case SuccessResult(argvals) =>
              val (funresty, funpars, funbody) = module.funs(functionName)
              if (argvals.length == funpars.length &&
                    argvals.zip(funpars.map(_.typ)).forall((typing.checkType _).tupled)) {
                val callstore = Store(module.globalVars.map { case (x, _) => (x, store__.map(x)) } ++
                  funpars.map(_.name).zip(argvals).toMap)
                val (res, resstore) = evalLocal(funpars.map(par => par.name -> par.typ).toMap, callstore, funbody)
                val store_ = Store(module.globalVars.map { case (x, _) => (x, resstore.map(x)) })
                def funcallsuccess(resval: Value): (Result[Value], Store) = {
                  if (typing.checkType(resval, funresty)) (resval.point[Result], store_)
                  else (ExceptionalResult(Error), store_)
                }
                res match {
                  case SuccessResult(resval) => funcallsuccess(resval)
                  case ExceptionalResult(exres) =>
                    exres match {
                      case Return(value) => funcallsuccess(value)
                      case Throw(value) => (ExceptionalResult(Throw(value)), store_)
                      case Break | Continue | Fail | Error => (ExceptionalResult(Error), store_)
                    }
                }
              }
              else (ExceptionalResult(Error), store__)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case ReturnExpr(evl) =>
          val (res, store_) = evalLocal(localVars, store, evl)
          res match {
            case SuccessResult(vl) => (ExceptionalResult(Return(vl)), store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case AssignExpr(name, targetexpr) =>
          val (res, store_) = evalLocal(localVars, store, targetexpr)
          res match {
            case SuccessResult(vl) =>
              val varty = if (localVars.contains(name)) localVars(name) else module.globalVars(name)
              if (typing.checkType(vl, varty)) (vl.pure[Result], store_.copy(map = store_.map.updated(name, vl)))
              else (ExceptionalResult(Error), store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case IfExpr(cond, thenB, elseB) =>
          val (condres, store__) = evalLocal(localVars, store, cond)
          condres match {
            case SuccessResult(condv) =>
              condv match {
                case ConstructorValue("true", Seq()) => evalLocal(localVars, store__, thenB)
                case ConstructorValue("false", Seq()) => evalLocal(localVars, store__, elseB)
                case _ => (ExceptionalResult(Error), store__)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case SwitchExpr(scrutinee, cases) => ???
        case VisitExpr(strategy, scrutinee, cases) => ???
        case BreakExpr => (ExceptionalResult(Break), store)
        case ContinueExpr => (ExceptionalResult(Continue), store)
        case FailExpr => (ExceptionalResult(Fail), store)
        case LocalBlockExpr(vardefs, exprs) =>
          val localVars_ = vardefs.toList.foldLeft(localVars) { (lvs, vdef) =>
            lvs.updated(vdef.name, vdef.typ)
          }
          val (res, store__) = evalLocalAll(localVars_, store, exprs)
          val store_ = store__.copy(store__.map -- vardefs.map(_.name))
          res match {
            case SuccessResult(vals) => (vals.headOption.getOrElse(BottomValue).pure[Result], store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case ForExpr(enum, body) =>
          val (enumres, store__) = evalEnum(localVars, store, enum)
          enumres match {
            case SuccessResult(envs) =>
              val (bodyres, store_) = evalEach(localVars, store__, envs, body)
              (bodyres.map{_ => BottomValue}, store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case WhileExpr(cond, body) => ???
        case SolveExpr(vars, body) => ???
        case ThrowExpr(evl) =>
          val (res, store_) = evalLocal(localVars, store, evl)
          res match {
            case SuccessResult(vl) => (ExceptionalResult(Throw(vl)), store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case TryCatchExpr(tryB, catchVar, catchB) =>
          val (tryres, store__) = evalLocal(localVars, store, tryB)
          tryres match {
            case SuccessResult(tryval) => (tryval.point[Result], store__)
            case ExceptionalResult(exres) =>
              exres match {
                case Throw(value) => evalLocal(localVars, store__.copy(store__.map.updated(catchVar,value)), catchB)
                case _ => (ExceptionalResult(exres), store__)
              }
          }
        case TryFinallyExpr(tryB, finallyB) =>
          val (tryres, store__) = evalLocal(localVars, store, tryB)
          tryres match {
            case SuccessResult(vl) =>
              val (finres, store_) = evalLocal(localVars, store__, finallyB)
              finres match {
                case SuccessResult(_) => (vl.point[Result], store_)
                case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
              }
            case ExceptionalResult(exres) =>
              exres match {
                case Throw(_) =>
                  val (finres, store_) = evalLocal(localVars, store__, finallyB)
                  (finres.map(_ => BottomValue), store_)
                case _ => (ExceptionalResult(exres), store__)
              }
          }
        case EnumExpr(enum) =>
          val (enres, store_) = evalEnum(localVars, store, enum)
          enres match {
            case SuccessResult(envs) =>
              if (envs.isEmpty) (ConstructorValue("false", Seq.empty).point[Result], store_)
              else (ConstructorValue("true", Seq.empty).point[Result], store_.copy(store_.map ++ envs.head))
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
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
      (List.empty, Domains.prelude)) { (st, df) =>
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
        unevalglobvars.reverse.foldLeftM[String \/ ?, Store](Store(Map.empty)) { (store, unevalglobvar) =>
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
