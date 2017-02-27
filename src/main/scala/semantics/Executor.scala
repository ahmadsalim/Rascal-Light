package semantics

import syntax.{Module => _, _}

import scala.collection.immutable.{::, Nil}
import scalaz.\/
import scalaz.std.list._
import scalaz.std.option._
import scalaz.syntax.either._
import scalaz.syntax.foldable._
import scalaz.syntax.monadPlus._

object Executor {
  private
  def evalUnary(op: OpName, vl: Value): Result[Value] = ???

  private
  def evalBinary(lhvl: Value, op: OpName, rhvl: Value): Result[Value] = ???

  private def children(v: Value): List[Value] = v match {
    case ConstructorValue(_, vals) => vals.toList
    case ListValue(vals) => vals
    case SetValue(vals) => vals.toList
    case MapValue(vals) => vals.keySet.toList ++ vals.values.toList
    case _ => List()
  }

  def matchPatt(module: Module, store : Store, tval: Value, patt: Patt): List[Map[VarName, Value]] = {
    val typing = Typing(module)
    def mergePairs(pairs: List[(Map[VarName, Value], Map[VarName, Value])]): List[Map[VarName, Value]] =
      pairs.map { case (env1, env2) =>
        if (env1.keySet.intersect(env2.keySet).forall(x => env1(x) == env2(x))) Some(env1 ++ env2)
        else None
      }.unite
    def merge(envss: List[List[Map[VarName, Value]]]): List[Map[VarName, Value]] =
      envss.foldLeft(List(Map[VarName, Value]())) { (envs, merged) =>
        mergePairs(envs.flatMap(env => merged.map(menv => (env, menv))))
      }
    def matchPattAll(module: Module, store: Store, vals: List[Value], spatts: List[StarPatt],
                     extract: Value => Option[List[Value]],
                     allPartitions: (List[Value]) => List[List[Value]],
                     restPartition: (List[Value], List[Value]) => Option[List[Value]]): List[Map[VarName, Value]] = spatts match {
      case Nil => if (vals.isEmpty) List() else List(Map())
      case sp :: sps =>
        sp match {
          case OrdinaryPatt(p) => vals match {
            case Nil => List()
            case v :: vs =>
              merge(List(matchPatt(module, store, v, p),
                matchPattAll(module, store, vs, sps, extract, allPartitions, restPartition)))
          }
          case ArbitraryPatt(sx) =>
            if (store.map.contains(sx)) {
              extract(store.map(sx)) match {
                case Some(vs) =>
                  restPartition(vs, vals) match {
                    case Some(vs_) => matchPattAll(module, store, vs_, sps, extract, allPartitions, restPartition)
                    case None => List()
                  }
                case None => List()
              }
            }
            else ???
        }
    }
    patt match {
      case BasicPatt(b) => tval match {
        case BasicValue(bv) if b == bv => List(Map())
        case _ => List()
      }
      case VarPatt(x) =>
        if (store.map.contains(x))
          if (store.map(x) == tval) List(Map())
          else List()
        else List(Map(x -> tval))
      case ConstructorPatt(k, pats) =>
        tval match {
          case ConstructorValue(k2, vals) if k == k2 && pats.length == vals.length =>
            merge(pats.toList.zip(vals.toList).map { case (p, v) => matchPatt(module, store, v, p) })
          case _ => List()
        }
      case LabelledTypedPatt(typ, labelVar, inpatt) =>
        if (typing.checkType(tval, typ)) merge(List(List(Map(labelVar -> tval)), matchPatt(module, store, tval, inpatt)))
        else List()
      case ListPatt(spatts) =>
        def extractList(v: Value): Option[List[Value]] = v match {
          case ListValue(vals) => Some(vals)
          case _ => None
        }
        def sublists(vs: List[Value]): List[List[Value]] =
          vs.foldRight(List(List[Value]())) { (x, sxs) =>
            List() :: sxs.map(x :: _)
          }
        tval match {
          case ListValue(vals) => matchPattAll(module, store, vals, spatts.toList, extractList, sublists)
          case _ => List()
        }
      case SetPatt(spatts) =>
        def extractSet(v: Value): Option[List[Value]] = v match {
          case SetValue(vals) => Some(vals.toList)
          case _ => None
        }
        def subsets(vs: List[Value]): List[List[Value]] =
          vs.foldRight(List(List[Value]())) { (x, sxs) =>
            sxs ++ sxs.map(x :: _)
          }
        tval match {
          case SetValue(vals) => matchPattAll(module, store, vals.toList, spatts.toList, extractSet, subsets)
          case _ => List()
        }
      case DescendantPatt(inpatt) => matchPatt(module, store, tval, inpatt) ++
        children(tval).flatMap(cv => matchPatt(module, store, cv, DescendantPatt(inpatt)))
    }
  }

  def eval(module: Module, store: Store, expr: Expr): (Result[Value], Store) = {
    val typing = Typing(module)

    def evalVisit(strategy: Strategy, localVars: Map[VarName, Type], store : Store, scrutineeval: Value, cases: List[Case]): (Result[Value], Store) = ???

    def evalCases(localVars: Map[VarName, Type], store : Store, scrutineeval: Value, cases: List[Case]): (Result[Value], Store) = ???

    def evalEach(localVars: Map[VarName, Type], store: Store, envs: List[Map[VarName, Value]], body: Expr): (Result[Unit], Store) = envs match {
      case Nil => (().point[Result], store)
      case env :: envs_ =>
        val (bodyres, store_) = evalLocal(localVars, store.copy(store.map ++ env), body)
        bodyres match {
          case SuccessResult(vl) =>
            evalEach(localVars, store_, envs_, body)
          case ExceptionalResult(exres) =>
            exres match {
              case Break => (().point[Result], store_)
              case Continue => evalEach(localVars, store_, envs_, body)
              case _ => (ExceptionalResult(exres), store_)
            }
        }
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

    def evalEnum(localVars: Map[VarName, Type], store: Store, enum: Enum): (Result[List[Map[VarName, Value]]], Store) =
      enum match {
        case MatchAssign(patt, target) =>
          val (tres, store_) = evalLocal(localVars, store, target)
          tres match {
            case SuccessResult(tval) => (matchPatt(module, store_, tval, patt).point[Result], store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case EnumAssign(varname, target) =>
          val (tres, store_) = evalLocal(localVars, store, target)
          tres match {
            case SuccessResult(tval) =>
              tval match {
                case ListValue(vals) => (vals.map(vl => Map(varname -> vl)).point[Result], store_)
                case SetValue(vals) => (vals.toList.map(vl => Map(varname -> vl)).point[Result], store_)
                case MapValue(vals) => (vals.keys.toList.map(vl => Map(varname -> vl)).point[Result], store_)
                case _ => (ExceptionalResult(Error), store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
      }

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
        case SwitchExpr(scrutinee, cases) =>
          val (scrres, store__) = evalLocal(localVars, store, scrutinee)
          scrres match {
            case SuccessResult(scrval) =>
              val (caseres, store_) = evalCases(localVars, store__, scrval, cases.toList)
              caseres match {
                case SuccessResult(caseval) => (caseval.point[Result], store_)
                case ExceptionalResult(exres) =>
                  exres match {
                    case Fail => (BottomValue.point[Result], store_)
                    case _ => (ExceptionalResult(exres), store_)
                  }
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case VisitExpr(strategy, scrutinee, cases) =>
          val (scrres, store__) = evalLocal(localVars, store, scrutinee)
          scrres match {
            case SuccessResult(scrval) =>
              val (caseres, store_) = evalVisit(strategy, localVars, store__, scrval, cases.toList)
              caseres match {
                case SuccessResult(caseval) => (caseval.point[Result], store_)
                case ExceptionalResult(exres) =>
                  exres match {
                    case Fail => (BottomValue.point[Result], store_)
                    case _ => (ExceptionalResult(exres), store_)
                  }
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
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
        case WhileExpr(cond, body) =>
          def loopWhile(store: Store): (Result[Unit], Store) = {
            val (condres, store__) = evalLocal(localVars, store, cond)
            condres match {
              case SuccessResult(condval) =>
                condval match {
                  case ConstructorValue("true", Seq()) =>
                    val (condres, store_) = evalLocal(localVars, store__, body)
                    condres match {
                      case SuccessResult(_) =>
                        loopWhile(store_)
                      case ExceptionalResult(exres) =>
                        exres match {
                          case Break => (().point[Result], store_)
                          case Continue => loopWhile(store_)
                          case _ => (ExceptionalResult(exres), store_)
                        }
                    }
                  case ConstructorValue("false", Seq()) => (().point[Result], store__)
                  case _ => (ExceptionalResult(Error), store__)
                }
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
            }
          }
          val (res, store_) = loopWhile(store)
          (res.map(_ => BottomValue), store_)
        case SolveExpr(vars, body) =>
          def loopSolve(store: Store): (Result[Value], Store) = {
            val (bodyres, store_) = evalLocal(localVars, store, body)
            bodyres match {
              case SuccessResult(v) =>
                if (vars.toList.map(store.map).zip(vars.toList.map(store_.map)).forall { case (v1, v2) => v1 == v2 })
                  (SuccessResult(v), store_)
                else loopSolve(store_)
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
            }
          }
          loopSolve(store)
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
