package semantics

import syntax.{Module => _, _}

import scala.collection.immutable.{::, Nil}
import scalaz.\/
import scalaz.std.list._
import scalaz.syntax.either._
import scalaz.syntax.foldable._
import scalaz.syntax.monadPlus._
import fs2.{Pure, Stream}
import semantics.domains._

object Executor {

  private
  def evalUnary(op: OpName, vl: Value): Result[Value] = (op, vl) match {
    case ("-", BasicValue(IntLit(i))) => BasicValue(IntLit(-i)).point[Result]
    case ("!", ConstructorValue("true", Seq())) => ConstructorValue("false", Seq()).point[Result]
    case ("!", ConstructorValue("false", Seq())) => ConstructorValue("true", Seq()).point[Result]
    case _ => ExceptionalResult(Error(InvalidOperationError(op, List(vl))))
  }

  private
  def evalBinary(lhvl: Value, op: OpName, rhvl: Value): Result[Value] =
    (lhvl, op, rhvl) match {
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
      case (lhvl, "notin", rhvl) => evalBinary(lhvl, "in", rhvl).flatMap(v => evalUnary("!", v))
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
      case (BasicValue(IntLit(i1)), "/", BasicValue(IntLit(i2))) if i2 != 0 => BasicValue(IntLit(i1 / i2)).point[Result]
      case (BasicValue(IntLit(i1)), "%", BasicValue(IntLit(i2))) if i2 > 0 => BasicValue(IntLit(i1 % i2)).point[Result]
      case _ => ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl))))
    }

  private
  def ifFail(rs1: Result[Value], v: Value): Result[Value] = rs1 match {
    case ExceptionalResult(Fail) => v.point[Result]
    case _ => rs1
  }

  def matchPatt(module: Module, store : Store, tval: Value, patt: Patt): Stream[Pure, Map[VarName, Value]] = {
    val typing = Typing(module)
    def mergePairs(pairs: Stream[Pure, (Map[VarName, Value], Map[VarName, Value])]): Stream[Pure, Map[VarName, Value]] =
      pairs.map { case (env1, env2) =>
        if (env1.keySet.intersect(env2.keySet).forall(x => env1(x) == env2(x))) Some(env1 ++ env2)
        else None
      }.filter(_.isDefined).map(_.get)
    def merge(envss: List[Stream[Pure, Map[VarName, Value]]]): Stream[Pure, Map[VarName, Value]] =
      envss.foldLeft(Stream(Map[VarName, Value]())) { (envs, merged) =>
        mergePairs(envs.flatMap(env => merged.map(menv => (env, menv))))
      }
    def matchPattAll(module: Module, store: Store, vals: List[Value], spatts: List[StarPatt],
                     extract: Value => Option[List[Value]],
                     construct: List[Value] => Value,
                     allPartitions: (List[Value]) => Stream[Pure, List[Value]],
                     restPartition: (List[Value], List[Value]) => Option[List[Value]]): Stream[Pure, Map[VarName, Value]] = spatts match {
      case Nil => if (vals.isEmpty) Stream() else Stream(Map())
      case sp :: sps =>
        sp match {
          case OrdinaryPatt(p) => vals match {
            case Nil => Stream()
            case v :: vs =>
              merge(List(matchPatt(module, store, v, p),
                matchPattAll(module, store, vs, sps, extract, construct, allPartitions, restPartition)))
          }
          case ArbitraryPatt(sx) =>
            if (store.map.contains(sx)) {
              extract(store.map(sx)) match {
                case Some(vs) =>
                  restPartition(vs, vals) match {
                    case Some(vs_) => matchPattAll(module, store, vs_, sps, extract, construct, allPartitions, restPartition)
                    case None => Stream()
                  }
                case None => Stream()
              }
            }
            else
              allPartitions(vals).flatMap(part =>
                matchPattAll(module, store.copy(store.map.updated(sx, construct(part))),
                  restPartition(part, vals).get, sps, extract, construct, allPartitions, restPartition))
        }
    }
    patt match {
      case IgnorePatt => Stream(Map())
      case BasicPatt(b) => tval match {
        case BasicValue(bv) if b == bv => Stream(Map())
        case _ => Stream()
      }
      case VarPatt(x) =>
        if (store.map.contains(x))
          if (store.map(x) == tval) Stream(Map())
          else Stream()
        else Stream(Map(x -> tval))
      case ConstructorPatt(k, pats) =>
        tval match {
          case ConstructorValue(k2, vals) if k == k2 && pats.length == vals.length =>
            merge(pats.toList.zip(vals.toList).map { case (p, v) => matchPatt(module, store, v, p) })
          case _ => Stream()
        }
      case LabelledTypedPatt(typ, labelVar, inpatt) =>
        if (typing.checkType(tval, typ)) merge(List(Stream(Map(labelVar -> tval)), matchPatt(module, store, tval, inpatt)))
        else Stream()
      case ListPatt(spatts) =>
        def extractList(v: Value): Option[List[Value]] = v match {
          case ListValue(vals) => Some(vals)
          case _ => None
        }
        def restList(svs: List[Value], vs: List[Value]): Option[List[Value]] = {
          if (svs.length <= vs.length && svs.zip(vs).forall { case (v1, v2) => v1 == v2 }) Some(vs.drop(svs.length))
          else None
        }
        def sublists(vs: List[Value]): Stream[Pure, List[Value]] =
          vs.foldRight(Stream(List[Value]())) { (x, sxs) =>
            Stream(List()) append sxs.map(x :: _)
          }
        tval match {
          case ListValue(vals) =>
            matchPattAll(module, store, vals, spatts.toList, extractList, ListValue, sublists, restList)
          case _ => Stream()
        }
      case SetPatt(spatts) =>
        def extractSet(v: Value): Option[List[Value]] = v match {
          case SetValue(vals) => Some(vals.toList)
          case _ => None
        }
        def restSet(svs: List[Value], vs: List[Value]): Option[List[Value]] = {
          val svss = svs.toSet
          val vss = vs.toSet
          if (svss.subsetOf(vss)) Some((vss diff svss).toList)
          else None
        }
        def subsets(vs: List[Value]): Stream[Pure, List[Value]] =
          Stream.emits(vs.toSet.subsets.toList).map(_.toList)
        tval match {
          case SetValue(vals) =>
            matchPattAll(module, store, vals.toList, spatts.toList, extractSet, vs => SetValue(vs.toSet), subsets, restSet)
          case _ => Stream()
        }
      case DescendantPatt(inpatt) => matchPatt(module, store, tval, inpatt) ++
        Stream.emits(tval.children).flatMap(cv => matchPatt(module, store, cv, DescendantPatt(inpatt)))
    }
  }

  def eval(module: Module, store: Store, expr: Expr) = {
    val typing = Typing(module)

    def accessField(tv: Value, fieldName: FieldName): Result[Value] = tv match {
      case ConstructorValue(name, vals) =>
        val (_, pars) = module.constructors(name)
        val index = pars.indexWhere(_.name == fieldName)
        if (index < 0) { ExceptionalResult(Error(FieldError(tv, fieldName))) } else vals(index).point[Result]
      case _ => ExceptionalResult(Error(FieldError(tv, fieldName)))
    }

    def updatePath(ovl: Value, paths: List[AccessPath], tvl: Value): Result[Value] = paths match {
      case Nil => tvl.point[Result]
      case path :: rpaths =>
        path match {
          case MapAccessPath(kvl) =>
            ovl match {
              case MapValue(vals) =>
                if (vals.contains(kvl)) {
                  updatePath(vals(kvl), rpaths, tvl).map(nvl => MapValue(vals.updated(kvl, nvl)))
                }
                else ExceptionalResult(Throw(ConstructorValue("nokey", Seq(kvl))))
              case _ => ExceptionalResult(Error(TypeError(ovl, MapType(typing.inferType(kvl).get, typing.inferType(tvl).get))))
            }
          case FieldAccessPath(fieldName) =>
            ovl match {
              case ConstructorValue(name, vals) =>
                val (_, pars) = module.constructors(name)
                val index = pars.indexWhere(_.name == fieldName)
                if (index < 0) { ExceptionalResult(Error(FieldError(ovl, fieldName))) }
                else {
                  updatePath(vals(index), rpaths, tvl).flatMap { nvl =>
                    if (typing.checkType(nvl, pars(index).typ)) {
                      ConstructorValue(name, vals.updated(index, nvl)).point[Result]
                    } else {
                      ExceptionalResult(Error(TypeError(nvl, pars(index).typ)))
                    }
                  }
                }
              case _ => ExceptionalResult(Error(OtherError)) // TODO Should be type error, but of which type?
            }
        }
    }

    def reconstruct(vl: Value, cvs: List[Value]): Result[Value] = {
      vl match {
        case BasicValue(b) =>
          if (cvs.isEmpty) BasicValue(b).point[Result] else ExceptionalResult(Error(ReconstructError(vl, cvs)))
        case ConstructorValue(name, vals) =>
          val (_, parameters) = module.constructors(name)
          if (cvs.length == parameters.length &&
                cvs.zip(parameters.map(_.typ)).forall((typing.checkType _).tupled)) ConstructorValue(name, cvs).point[Result]
          else ExceptionalResult(Error(ReconstructError(vl, cvs)))
        case ListValue(vals) => ListValue(cvs).point[Result]
        case SetValue(vals) => SetValue(cvs.toSet).point[Result]
        case MapValue(vals) => MapValue(cvs.take(cvs.length/2).zip(cvs.drop(cvs.length/2)).toMap).point[Result]
        case BottomValue =>
          if (cvs.isEmpty) BottomValue.point[Result] else ExceptionalResult(Error(ReconstructError(vl, cvs)))
      }
    }

    def evalTD(localVars: Map[VarName, Type], store: Store, scrutineeval: Value, cases: List[Case], break: Boolean): (Result[Value], Store) = {
      def evalTDAll(vals: List[Value], store: Store): (Result[List[Value]], Store) =
        vals match {
          case Nil => (List().point[Result], store)
          case cvl::cvls =>
            val (cvres, store___) = evalTD(localVars, store, cvl, cases, break)
            ifFail(cvres, cvl) match {
              case SuccessResult(cvl_) =>
                if (break && cvres != ExceptionalResult(Fail)) ((cvl_ :: cvls).point[Result], store___)
                else {
                  val (cvsres, store_) = evalTDAll(cvls, store___)
                  (cvsres.map(cvls_ => cvl_ :: cvls_), store_)
                }
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store___)
            }
        }
      // TODO optimize traversal by checking types
       val (scres, store__) = evalCases(localVars, store, scrutineeval, cases)
       ifFail(scres, scrutineeval) match {
        case SuccessResult(vl) =>
          if (break && scres != ExceptionalResult(Fail)) (vl.point[Result], store__)
          else {
            val (cvres, store_) = evalTDAll(vl.children, store__)
            (cvres.flatMap(cvs => reconstruct(vl, cvs)), store_)
          }
        case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
      }
    }

    def evalBU(localVars: Map[VarName, Type], store: Store, scrutineeval: Value, cases: List[Case], break: Boolean): (Result[Value], Store) = {
      def evalBUAll(vals: List[Value], store: Store): (Boolean, Result[List[Value]], Store) =
        vals match {
          case Nil => (true, List().point[Result], store)
          case cvl::cvls =>
            val (cvres, store___) = evalBU(localVars, store, cvl, cases, break)
            ifFail(cvres, cvl) match {
              case SuccessResult(cvl_) =>
                if (break && cvres != ExceptionalResult(Fail)) (false, (cvl_ :: cvls).point[Result], store___)
                else {
                  val (allfailed, cvsres, store_) = evalBUAll(cvls, store___)
                  (cvres == ExceptionalResult(Fail) && allfailed, cvsres.map(cvls_ => cvl_ :: cvls_), store_)
                }
              case ExceptionalResult(exres) => (false, ExceptionalResult(exres), store___)
            }
        }
      val (allfailed, cvres, store__) = evalBUAll(scrutineeval.children, store)
      cvres match {
        case SuccessResult(cvls) =>
          if (break && allfailed) evalCases(localVars, store__, scrutineeval, cases)
          else reconstruct(scrutineeval, cvls) match {
            case SuccessResult(newval) =>
              val (selfres, store_) =  evalCases(localVars, store__, newval, cases)
              selfres match {
                case ExceptionalResult(Fail) => (SuccessResult(newval), store_)
                case _ => (selfres, store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
      }
    }

    def evalVisit(strategy: Strategy, localVars: Map[VarName, Type], store : Store, scrutineeval: Value, cases: List[Case]): (Result[Value], Store) = {
      val (res, store_) = strategy match {
        case TopDown => evalTD(localVars, store, scrutineeval, cases, break = false)
        case TopDownBreak => evalTD(localVars, store, scrutineeval, cases, break = true)
        case BottomUp => evalBU(localVars, store, scrutineeval, cases, break = false)
        case BottomUpBreak => evalBU(localVars, store, scrutineeval, cases, break = true)
        case Innermost =>
          val (res, store_) = evalBU(localVars, store, scrutineeval, cases, break = false)
          res match {
            case SuccessResult(newval) =>
              if (scrutineeval == newval) (newval.point[Result], store_)
              else evalVisit(Innermost, localVars, store_, newval, cases)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case Outermost =>
          val (res, store_) = evalTD(localVars, store, scrutineeval, cases, break = false)
          res match {
            case SuccessResult(newval) =>
              if (scrutineeval == newval) (newval.point[Result], store_)
              else evalVisit(Outermost, localVars, store_, newval, cases)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
      }
      res match {
        case ExceptionalResult(Fail) => (SuccessResult(scrutineeval), store_)
        case _ => (res, store_)
      }
    }

    def evalCases(localVars: Map[VarName, Type], store : Store, scrutineeval: Value, cases: List[Case]): (Result[Value], Store) = {
      def evalCase(store: Store, action: Expr, envs: Stream[Pure, Map[VarName, Value]]): (Result[Value], Store) =
        envs.head.toList match {
          case Nil => (ExceptionalResult(Fail), store)
          case env :: _ =>
            val (actres, store_) = evalLocal(localVars, store.copy(store.map ++ env), action)
            actres match {
              case ExceptionalResult(Fail) => evalCase(store, action, envs.tail)
              case _ => (actres, store_.copy(store.map -- env.keySet))
            }
        }
      cases match {
        case Nil => (ExceptionalResult(Fail), store)
        case Case(cspatt, csaction) :: css =>
          val envs = matchPatt(module, store, scrutineeval, cspatt)
          val (cres, store_) = evalCase(store, csaction, envs)
          cres match {
            case ExceptionalResult(Fail) => evalCases(localVars, store, scrutineeval, css)
            case _ => (cres, store_)
          }
      }
    }

    def evalEach(localVars: Map[VarName, Type], store: Store, envs: Stream[Pure, Map[VarName, Value]], body: Expr): (Result[Unit], Store) =
      envs.head.toList match {
          case Nil => (().point[Result], store)
          case env :: _ =>
            val (bodyres, store_) = evalLocal(localVars, store.copy(store.map ++ env), body)
            bodyres match {
              case SuccessResult(vl) =>
                evalEach(localVars, store_, envs.tail, body)
              case ExceptionalResult(exres) =>
                exres match {
                  case Break => (().point[Result], store_)
                  case Continue => evalEach(localVars, store_, envs.tail, body)
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

    def evalEnum(localVars: Map[VarName, Type], store: Store, enum: Enum): (Result[Stream[Pure, Map[VarName, Value]]], Store) =
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
                case ListValue(vals) => (Stream.emits(vals.map(vl => Map(varname -> vl))).point[Result], store_)
                case SetValue(vals) => (Stream.emits(vals.toList.map(vl => Map(varname -> vl))).point[Result], store_)
                case MapValue(vals) => (Stream.emits(vals.keys.toList.map(vl => Map(varname -> vl))).point[Result], store_)
                case _ => (ExceptionalResult(Error(NotEnumerableError(tval))), store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
      }

    def evalAssignable(localVars: Map[VarName, Type], store: Store, assgn: Assignable): (Result[DataPath], Store) = {
      assgn match {
        case VarAssgn(name) => (DataPath(name, List()).point[Result], store)
        case FieldAccAssgn(target, fieldName) =>
          val (targetres, store_) = evalAssignable(localVars, store, target)
          (targetres.map {
            case DataPath(vn, accessPaths) => DataPath(vn, accessPaths :+ FieldAccessPath(fieldName))
          }, store_)
        case MapUpdAssgn(target, ekey) =>
          val (targetres, store__) = evalAssignable(localVars, store, target)
          targetres match {
            case SuccessResult(DataPath(vn, accessPaths)) =>
              val (keyres, store_) = evalLocal(localVars, store, ekey)
              (keyres.map(keyv => DataPath(vn, accessPaths :+ MapAccessPath(keyv))), store_)
            case ExceptionalResult(exres) => (targetres, store__)
          }
      }
    }

    def evalLocal(localVars: Map[VarName, Type], store: Store, expr: Expr): (Result[Value], Store) =
      expr match {
        case BasicExpr(b) => (BasicValue(b).pure[Result], store)
        case VarExpr(x) =>
          if (store.map.contains(x)) (store.map(x).pure[Result], store)
          else (ExceptionalResult(Error(UnassignedVarError(x))), store)
        case FieldAccExpr(target, fieldName) =>
          val (targetres, store_) = evalLocal(localVars, store, target)
          targetres match {
            case SuccessResult(tv) => (accessField(tv, fieldName), store_)
            case _ => (targetres, store_)
          }
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
              else (ExceptionalResult(Error(SignatureMismatch(name, vals, parameters.map(_.typ)))), store_)
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
        case MapLookupExpr(emap, ekey) =>
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
                case _ => (ExceptionalResult(Error(TypeError(mapv, MapType(ValueType, ValueType)))), store__)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case MapUpdExpr(emap, ekey, evl) =>
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
                case _ => (ExceptionalResult(Error(TypeError(mapv, MapType(ValueType, ValueType)))), store___)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store___)
          }
        case FunCallExpr(functionName, args) =>
          val (argres, store__) = evalLocalAll(localVars, store, args)
          argres match {
            case SuccessResult(argvals) =>
              val (funresty, funpars, funbody) = module.funs(functionName)
              val argpartyps = argvals.zip(funpars.map(_.typ))
              if (argvals.length == funpars.length &&
                    argpartyps.forall((typing.checkType _).tupled)) {
                val callstore = Store(module.globalVars.map { case (x, _) => (x, store__.map(x)) } ++
                  funpars.map(_.name).zip(argvals).toMap)
                val (res, resstore) = funbody match {
                  case ExprFunBody(exprfunbody) =>
                    evalLocal(funpars.map(par => par.name -> par.typ).toMap, callstore, exprfunbody)
                  case PrimitiveFunBody =>
                    functionName match {
                      case "delete" =>
                        val map = callstore.map("emap")
                        val key = callstore.map("ekey")
                        map match {
                          case MapValue(vals) => (SuccessResult(MapValue(vals - key)), callstore)
                          case _ => (ExceptionalResult(Error(OtherError)), callstore)
                        }
                      case _ => (ExceptionalResult(Error(OtherError)), callstore)
                    }
                }
                val store_ = Store(module.globalVars.map { case (x, _) => (x, resstore.map(x)) } ++ store__.map)
                def funcallsuccess(resval: Value): (Result[Value], Store) = {
                  if (typing.checkType(resval, funresty)) (resval.point[Result], store_)
                  else (ExceptionalResult(Error(TypeError(resval, funresty))), store_)
                }
                res match {
                  case SuccessResult(resval) => funcallsuccess(resval)
                  case ExceptionalResult(exres) =>
                    exres match {
                      case Return(value) => funcallsuccess(value)
                      case Throw(value) => (ExceptionalResult(Throw(value)), store_)
                      case Break | Continue | Fail => (ExceptionalResult(Error(EscapedControlOperator)), store_)
                      case _ => (ExceptionalResult(exres), store_)
                    }
                }
              }
              else (ExceptionalResult(Error(SignatureMismatch(functionName, argvals, funpars.map(_.typ)))), store__)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case ReturnExpr(evl) =>
          val (res, store_) = evalLocal(localVars, store, evl)
          res match {
            case SuccessResult(vl) => (ExceptionalResult(Return(vl)), store_)
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case AssignExpr(assgn, targetexpr) =>
          val (assgnres, store__) = evalAssignable(localVars, store, assgn)
          assgnres match {
            case SuccessResult(path) =>
              val (targetres, store_) = evalLocal(localVars, store__, targetexpr)
              targetres match {
                case SuccessResult(vl) =>
                  val newValue =
                    if (path.accessPaths.isEmpty) {
                      vl.point[Result]
                    } else {
                      store_.map.get(path.varName).fold[Result[Value]](ExceptionalResult(Error(UnassignedVarError(path.varName)))) {
                        ovl => updatePath(ovl, path.accessPaths, vl) }
                    }
                  newValue match {
                    case SuccessResult(nvl) =>
                      val varty = if (localVars.contains(path.varName)) localVars(path.varName) else module.globalVars(path.varName)
                      if (typing.checkType(vl, varty)) {
                        val res = (vl.pure[Result], store_.copy(map = store_.map.updated(path.varName, nvl)))
                        res
                      }
                      else (ExceptionalResult(Error(TypeError(vl, varty))), store_)
                    case _ => (newValue, store_)
                  }
                case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        case IfExpr(cond, thenB, elseB) =>
          val (condres, store__) = evalLocal(localVars, store, cond)
          condres match {
            case SuccessResult(condv) =>
              condv match {
                case ConstructorValue("true", Seq()) => evalLocal(localVars, store__, thenB)
                case ConstructorValue("false", Seq()) => evalLocal(localVars, store__, elseB)
                case _ => (ExceptionalResult(Error(TypeError(condv, DataType("Bool")))), store__)
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
            case SuccessResult(vals) => (vals.lastOption.getOrElse(BottomValue).pure[Result], store_)
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
                  case _ => (ExceptionalResult(Error(TypeError(condval, DataType("Bool")))), store__)
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
              val env = envs.head.toList
              if (env.isEmpty) (ConstructorValue("false", Seq.empty).point[Result], store_)
              else (ConstructorValue("true", Seq.empty).point[Result], store_.copy(store_.map ++ env.head))
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
        case AssertExpr(cond) =>
          val (condres, store_) = evalLocal(localVars, store, cond)
          condres match {
            case SuccessResult(condval) =>
              condval match {
                case ConstructorValue("true", Seq()) => (condres, store_)
                case ConstructorValue("false", Seq()) => (ExceptionalResult(Error(AssertionError(cond))), store_)
                case _ => (ExceptionalResult(Error(TypeError(condval, DataType("Bool")))), store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
          }
      }
    evalLocal(Map.empty, store, expr)
  }

  def execute(module: syntax.Module): String \/ ExecutionResult = {
    def alreadyDefined(name: Name, outmod: Module): Boolean = {
      outmod.funs.contains(name) || outmod.globalVars.contains(name) ||
        outmod.datatypes.contains(name) || outmod.constructors.contains(name)
    }
    def alreadyDefinedErrMsg(name: Name) = s"duplicate definition in module of name: $name"
    def constructorTypeSameNameErrMsg(name: Name) = s"constructor $name has the same name as the data type"
    val transr = module.defs.toList.foldLeftM[String \/ ?, (List[(VarName, Expr)], List[TestDef], Module)](
      (List.empty, List.empty, Domains.prelude)) { (st, df) =>
        val (unevalglobvars, tests, outmod) = st
        df match {
          case GlobalVarDef(typ, name, initialValue) =>
            if (alreadyDefined(name, outmod)) alreadyDefinedErrMsg(name).left
            else ((name, initialValue) :: unevalglobvars, tests,
                    outmod.copy(globalVars = outmod.globalVars.updated(name, typ))).right
          case FunDef(returntype, name, parameters, body) =>
            if (alreadyDefined(name, outmod)) alreadyDefinedErrMsg(name).left
            else (unevalglobvars, tests,
                     outmod.copy(funs = outmod.funs.updated(name, (returntype, parameters.toList, ExprFunBody(body))))).right
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
              consmapr.map { consmap => (unevalglobvars, tests,
                  outmod.copy(datatypes = outmod.datatypes.updated(tyname, constructors.map(_.name).toList),
                              constructors = outmod.constructors ++ consmap)) }
            }
          case td : TestDef => (unevalglobvars, tests :+ td, outmod).right
        }
    }
    transr.flatMap { case (unevalglobvars, tests, semmod) =>
        unevalglobvars.reverse.foldLeftM[String \/ ?, Store](Store(unevalglobvars.toMap.mapValues(_ => BottomValue))) {
          (store, unevalglobvar) =>
            val (varname, varexpr) = unevalglobvar
            val (res, store_) = eval(semmod, store, varexpr)
            res match {
              case ExceptionalResult(exres) => s"Evaluation of left-hand side for variable $varname failed with $exres".left
              case SuccessResult(value) => store_.copy(map = store_.map.updated(varname, value)).right
            }
        }.flatMap { store =>
          tests.foldLeftM[String \/ ?, List[VarName]](List()) { (failed, test) =>
              val (res, store_) = eval(semmod, store, test.body)
              res match {
                case SuccessResult(ConstructorValue("true", Seq()))
                       | ExceptionalResult(Return(ConstructorValue("true", Seq()))) => failed.right
                case SuccessResult(_)
                       | ExceptionalResult(Return(_)) => (failed :+ test.name).right
                case ExceptionalResult(exres) => s"Evaluation of test ${test.name} failed with $exres".left
              }
          }.map(failed => (store, failed))
        }.map { case (store, failed) => ExecutionResult(store, semmod, failed) }
    }
  }
}
