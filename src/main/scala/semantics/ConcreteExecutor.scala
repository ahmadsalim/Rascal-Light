package semantics

import syntax._

import scala.collection.immutable.{::, Nil}
import scalaz.\/
import scalaz.std.list._
import scalaz.syntax.either._
import scalaz.syntax.foldable._
import scalaz.syntax.monadPlus._
import fs2.{Pure, Stream}
import semantics.domains.common._
import semantics.domains.concrete._
import semantics.typing.Typing

case class ConcreteExecutor(module: Module) {

  private
  def evalUnaryOp(op: OpName, vl: Value): Result[Value] = (op, vl) match {
    case ("-", BasicValue(IntLit(i))) => BasicValue(IntLit(-i)).point[Result]
    case ("!", ConstructorValue("true", Seq())) => ConstructorValue("false", Seq()).point[Result]
    case ("!", ConstructorValue("false", Seq())) => ConstructorValue("true", Seq()).point[Result]
    case _ => ExceptionalResult(Error(Set(InvalidOperationError(op, List(vl)))))
  }

  private
  def evalBinaryOp(lhvl: Value, op: OpName, rhvl: Value): Result[Value] =
    (lhvl, op, rhvl) match {
      case (_, "==", _) =>
        (if (lhvl == rhvl) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (_, "!=", _) =>
        (if (lhvl != rhvl) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (_, "in", ListValue(vs)) =>
        (if (vs.contains(lhvl)) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (_, "in", SetValue(vs)) =>
        (if (vs.contains(lhvl)) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (_, "in", MapValue(vs)) =>
        (if (vs.contains(lhvl)) ConstructorValue("true", Seq()) else ConstructorValue("false", Seq())).point[Result]
      case (_, "notin", _) => evalBinaryOp(lhvl, "in", rhvl).flatMap(v => evalUnaryOp("!", v))
      case (ConstructorValue("false", Seq()), "&&", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue("false", Seq()).point[Result]
      case (ConstructorValue("true", Seq()), "&&", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue(bnm, Seq()).point[Result]
      case (ConstructorValue("true", Seq()), "||", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue("true", Seq()).point[Result]
      case (ConstructorValue("false", Seq()), "||", ConstructorValue(bnm, Seq())) if bnm == "true" || bnm == "false" =>
        ConstructorValue(bnm, Seq()).point[Result]
      case (BasicValue(StringLit(s1)), "+", BasicValue(StringLit(s2))) => BasicValue(StringLit(s1 + s2)).point[Result]
      case (BasicValue(IntLit(i1)), "+", BasicValue(IntLit(i2))) => BasicValue(IntLit(i1 + i2)).point[Result]
      case (ListValue(vals1), "+", ListValue(vals2)) => ListValue(vals1 ++ vals2).point[Result]
      case (SetValue(vals1), "+", SetValue(vals2)) => SetValue(vals1 ++ vals2).point[Result]
      case (MapValue(kvs1), "+", MapValue(kvs2)) => MapValue(kvs1 ++ kvs2).point[Result]
      case (BasicValue(IntLit(i1)), "-", BasicValue(IntLit(i2))) => BasicValue(IntLit(i1 - i2)).point[Result]
      case (BasicValue(IntLit(i1)), "*", BasicValue(IntLit(i2))) => BasicValue(IntLit(i1 * i2)).point[Result]
      case (BasicValue(IntLit(i1)), "/", BasicValue(IntLit(i2)))  =>
        if (i2 == 0) ExceptionalResult(Throw(ConstructorValue("divByZero", List())))
        else BasicValue(IntLit(i1 / i2)).point[Result]
      case (BasicValue(IntLit(i1)), "%", BasicValue(IntLit(i2))) =>
        if (i2 <= 0) ExceptionalResult(Throw(ConstructorValue("modNonPos", List())))
        else BasicValue(IntLit(i1 % i2)).point[Result]
      case _ => ExceptionalResult(Error(Set(InvalidOperationError(op, List(lhvl, rhvl)))))
    }

  private
  def ifFail[A](rs1: Result[A], v:A): A = rs1 match {
    case ExceptionalResult(Fail) => v
    case SuccessResult(v_) => v_
    case _ => throw new UnsupportedOperationException(s"ifFail($rs1, $v)")
  }

  private
  def merge(envss: List[Stream[Pure, Map[VarName, Value]]]): Stream[Pure, Map[VarName, Value]] = {
    envss.foldLeft[Stream[Pure, Map[VarName, Value]]](Stream(Map[VarName, Value]())) { (envs, merged) =>
      val pairsEnvs = envs.flatMap(env => merged.map(menv => (env, menv)))
      mergePairs(pairsEnvs)
    }
  }

  private
  def mergePairs(pairs: Stream[Pure, (Map[VarName, Value], Map[VarName, Value])]): Stream[Pure, Map[VarName, Value]] = {
    pairs.flatMap { case (env1, env2) =>
      if (env1.keySet.intersect(env2.keySet).forall(x => env1(x) == env2(x))) Stream(env1 ++ env2)
      else Stream()
    }
  }

  private
  def matchPattAll(store: Store, vals: List[Value], spatts: List[StarPatt],
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
              merge(List(matchPatt(store, v, p),
                matchPattAll(store, vs, sps, extract, construct, allPartitions, restPartition)))
          }
          case ArbitraryPatt(sx) =>
            if (store.map.contains(sx)) {
              extract(store.map(sx)) match {
                case Some(vs) =>
                  restPartition(vs, vals) match {
                    case Some(vs_) => matchPattAll(store, vs_, sps, extract, construct, allPartitions, restPartition)
                    case None => Stream()
                  }
                case None => Stream()
              }
            }
            else
              allPartitions(vals).flatMap(part =>
                matchPattAll(Store(store.map.updated(sx, construct(part))), // Optimization to avoid heavy back-tracking
                  restPartition(part, vals).get, sps, extract, construct, allPartitions, restPartition).map(_.updated(sx, construct(part))))
        }
    }

  private
  def matchPatt(store : Store, tval: Value, patt: Patt): Stream[Pure, Map[VarName, Value]] = {
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
            merge(pats.toList.zip(vals.toList).map { case (p, v) => matchPatt(store, v, p) })
          case _ => Stream()
        }
      case LabelledTypedPatt(typ, labelVar, inpatt) =>
        if (typing.checkType(tval, typ)) {
          val inmatch = matchPatt(store, tval, inpatt)
          merge(List(Stream(Map(labelVar -> tval)), inmatch))
        } else Stream()
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
            matchPattAll(store, vals, spatts.toList, extractList, ListValue, sublists, restList)
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
            matchPattAll(store, vals.toList, spatts.toList, extractSet, vs => SetValue(vs.toSet), subsets, restSet)
          case _ => Stream()
        }
      case NegationPatt(inpatt) =>
        val res = matchPatt(store, tval, inpatt)
        res.head.toList match {
          case Nil => Stream(Map())
          case _ :: _ => Stream()
        }
      case DescendantPatt(inpatt) => matchPatt(store, tval, inpatt) ++
        Stream.emits(tval.children).flatMap(cv => matchPatt(store, cv, DescendantPatt(inpatt)))
    }
  }

  private
  val typing = Typing(module)

  private
  def accessField(tv: Value, fieldName: FieldName): Result[Value] = tv match {
    case ConstructorValue(name, vals) =>
      val (_, pars) = module.constructors(name)
      val index = pars.indexWhere(_.name == fieldName)
      if (index < 0) { ExceptionalResult(Error(Set(FieldError(tv, fieldName)))) } else vals(index).point[Result]
    case _ => ExceptionalResult(Error(Set(FieldError(tv, fieldName))))
  }

  private
  def updatePath(ovl: Value, paths: List[AccessPath[Value]], tvl: Value): Result[Value] = paths match {
    case Nil => tvl.point[Result]
    case path :: rpaths =>
      path match {
        case MapAccessPath(kvl) =>
          ovl match {
            case MapValue(vals) =>
              if (tvl == BottomValue) ExceptionalResult(Error(Set(OtherError)))
              else if (rpaths.isEmpty) {
                SuccessResult(MapValue(vals.updated(kvl, tvl)))
              } else if (vals.contains(kvl)) {
                updatePath(vals(kvl), rpaths, tvl).map(nvl => MapValue(vals.updated(kvl, nvl)))
              } else ExceptionalResult(Throw(ConstructorValue("NoKey", Seq(kvl))))
            case _ => ExceptionalResult(Error(Set(TypeError(ovl, MapType(typing.inferType(kvl), typing.inferType(tvl))))))
          }
        case FieldAccessPath(fieldName) =>
          ovl match {
            case ConstructorValue(name, vals) =>
              if (tvl == BottomValue) ExceptionalResult(Error(Set(OtherError)))
              else {
                val (_, pars) = module.constructors(name)
                val index = pars.indexWhere(_.name == fieldName)
                if (index < 0) {
                  ExceptionalResult(Error(Set(FieldError(ovl, fieldName))))
                }
                else {
                  updatePath(vals(index), rpaths, tvl).flatMap { nvl =>
                    if (typing.checkType(nvl, pars(index).typ)) {
                      ConstructorValue(name, vals.updated(index, nvl)).point[Result]
                    } else {
                      ExceptionalResult(Error(Set(TypeError(nvl, pars(index).typ))))
                    }
                  }
                }
              }
            case _ => ExceptionalResult(Error(Set(FieldError(ovl, fieldName))))
          }
      }
  }

  private
  def reconstruct(vl: Value, cvs: List[Value]): Result[Value] = {
    vl match {
      case BasicValue(b) =>
        if (cvs.isEmpty) BasicValue(b).point[Result]
        else ExceptionalResult(Error(Set(ReconstructError(vl, cvs))))
      case ConstructorValue(name, _) =>
        val (_, parameters) = module.constructors(name)
        if (cvs.length == parameters.length &&
              !cvs.contains(BottomValue) &&
                cvs.zip(parameters.map(_.typ)).forall((typing.checkType _).tupled)) ConstructorValue(name, cvs).point[Result]
        else ExceptionalResult(Error(Set(ReconstructError(vl, cvs))))
      case ListValue(_) =>
        if (!cvs.contains(BottomValue)) ListValue(cvs).point[Result]
        else ExceptionalResult(Error(Set(ReconstructError(vl, cvs))))
      case SetValue(_) =>
        if (!cvs.contains(BottomValue)) SetValue(cvs.toSet).point[Result]
        else ExceptionalResult(Error(Set(ReconstructError(vl, cvs))))
      case MapValue(_) =>
        val (nkeys, nvals) = cvs.splitAt(cvs.length/2)
        if (!cvs.contains(BottomValue)) MapValue(nkeys.zip(nvals).toMap).point[Result]
        else ExceptionalResult(Error(Set(ReconstructError(vl, cvs))))
      case BottomValue =>
        if (cvs.isEmpty) BottomValue.point[Result] else ExceptionalResult(Error(Set(ReconstructError(vl, cvs))))
    }
  }

  def combineVals(cvres: Result[Value], cvsres: Result[List[Value]], cvl: Value, cvls: List[Value]): Result[List[Value]] = {
    if (cvres == ExceptionalResult(Fail) &&
         cvsres == ExceptionalResult(Fail)) ExceptionalResult(Fail)
    else {
      SuccessResult(ifFail(cvres, cvl) :: ifFail(cvsres, cvls))
    }
  }

  private
  def evalTD(localVars: Map[VarName, Type], store: Store, scrutineeval: Value, cases: List[Case], break: Boolean): (Result[Value], Store) = {
    def evalTDAll(vals: List[Value], store: Store): (Result[List[Value]], Store) =
      vals match {
        case Nil => (ExceptionalResult(Fail), store)
        case cvl::cvls =>
          val (cvres, store__) = evalTD(localVars, store, cvl, cases, break)
          def evalRest = {
            val (cvsres, store_) = evalTDAll(cvls, store__)
            cvsres match {
              case SuccessResult(_) | ExceptionalResult(Fail) => (combineVals(cvres, cvsres, cvl, cvls), store_)
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
            }
          }
          cvres match {
            case SuccessResult(cvl_) =>
              if (break) (SuccessResult(cvl_ :: cvls), store__)
              else evalRest
            case ExceptionalResult(Fail) => evalRest
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
      }
    // TODO optimize traversal by checking types
     val (scres, store__) = evalCases(localVars, store, scrutineeval, cases)
     def evalRest(scres: Result[Value], vl: Value) = {
       val value = ifFail(scres, vl)
       val (cvsres, store_) = evalTDAll(value.children, store__)
       cvsres match {
         case SuccessResult(cvs) => (reconstruct(vl, cvs), store_)
         case ExceptionalResult(Fail) => (scres, store_)
         case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
       }
     }
     scres match {
      case SuccessResult(vl) =>
        if (break) (SuccessResult(vl), store__)
        else evalRest(scres, vl)
      case ExceptionalResult(Fail) => evalRest(scres, scrutineeval)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
     }
   }

  private
  def evalBU(localVars: Map[VarName, Type], store: Store, scrutineeval: Value, cases: List[Case], break: Boolean): (Result[Value], Store) = {
    def evalBUAll(vals: List[Value], store: Store): (Result[List[Value]], Store) =
      vals match {
        case Nil => (ExceptionalResult(Fail), store)
        case cvl::cvls =>
          val (cvres, store__) = evalBU(localVars, store, cvl, cases, break)
          def evalRest = {
            val (cvsres, store_) = evalBUAll(cvls, store__)
            cvsres match {
              case SuccessResult(_) | ExceptionalResult(Fail) => (combineVals(cvres, cvsres, cvl, cvls), store_)
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
            }
          }
          cvres match {
            case SuccessResult(cvl_) =>
              if (break) (SuccessResult(cvl_ :: cvls), store__)
              else evalRest
            case ExceptionalResult(Fail) => evalRest
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
      }
    val (cvsres, store__) = evalBUAll(scrutineeval.children, store)
    cvsres match {
      case SuccessResult(cvls) =>
        if (break) {
          (reconstruct(scrutineeval, cvls), store__)
        } else {
          reconstruct(scrutineeval, cvls) match {
            case SuccessResult(cvl2) =>
              val (cvres2, store_) = evalCases(localVars, store__, cvl2, cases)
              cvres2 match {
                case SuccessResult(_) | ExceptionalResult(Fail) => (SuccessResult(ifFail(cvres2, cvl2)), store_)
                case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
              }
            case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
          }
        }
      case ExceptionalResult(Fail) => evalCases(localVars, store__, scrutineeval, cases)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private
  def evalVisitStrategy(strategy: Strategy, localVars: Map[VarName, Type], store : Store, scrutineeval: Value, cases: List[Case]): (Result[Value], Store) = {
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
            else evalVisitStrategy(Innermost, localVars, store_, newval, cases)
          case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
        }
      case Outermost =>
        val (res, store_) = evalTD(localVars, store, scrutineeval, cases, break = false)
        res match {
          case SuccessResult(newval) =>
            if (scrutineeval == newval) (newval.point[Result], store_)
            else evalVisitStrategy(Outermost, localVars, store_, newval, cases)
          case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
        }
    }
    res match {
      case ExceptionalResult(Fail) => (SuccessResult(scrutineeval), store_)
      case _ => (res, store_)
    }
  }

  private
  def evalCases(localVars: Map[VarName, Type], store : Store, scrutineeval: Value, cases: List[Case]): (Result[Value], Store) = {
    def evalCase(store: Store, action: Expr, envs: Stream[Pure, Map[VarName, Value]]): (Result[Value], Store) =
      envs.head.toList match {
        case Nil => (ExceptionalResult(Fail), store)
        case env :: _ =>
          val (actres, store_) = evalLocal(localVars, Store(store.map ++ env), action)
          actres match {
            case ExceptionalResult(Fail) => evalCase(store, action, envs.tail)
            case _ => (actres, Store(store_.map -- env.keySet))
          }
      }
    cases match {
      case Nil => (ExceptionalResult(Fail), store)
      case Case(cspatt, csaction) :: css =>
        val envs = matchPatt(store, scrutineeval, cspatt)
        val (cres, store_) = evalCase(store, csaction, envs)
        cres match {
          case ExceptionalResult(Fail) => evalCases(localVars, store, scrutineeval, css)
          case _ => (cres, store_)
        }
    }
  }

  private
  def evalEach(localVars: Map[VarName, Type], store: Store, envs: Stream[Pure, Map[VarName, Value]], body: Expr): (Result[Unit], Store) =
    envs.head.toList match {
      case Nil => (().point[Result], store)
      case env :: _ =>
        val (bodyres, store__) = evalLocal(localVars, Store(store.map ++ env), body)
        val store_ = Store(store__.map -- env.keySet)
        bodyres match {
          case SuccessResult(_) =>
            evalEach(localVars, store_, envs.tail, body)
          case ExceptionalResult(exres) =>
            exres match {
              case Break => (().point[Result], store_)
              case Continue => evalEach(localVars, store_, envs.tail, body)
              case _ => (ExceptionalResult(exres), store_)
            }
        }
    }

  private
  def evalLocalAll(localVars: Map[VarName, Type], store: Store, exprs: Seq[Expr]): (Result[List[Value]], Store) = {
    exprs.toList.foldLeft[(Result[List[Value]], Store)]((List().pure[Result], store)) { (st, e) =>
      val (prevres, store__) = st
      prevres match {
        case SuccessResult(vals) =>
          val (res, store_) = evalLocal(localVars, store__, e)
          (res.map(vl => vals :+ vl), store_)
        case _ => (prevres, store__)
      }
    }
  }

  private
  def evalGenerator(localVars: Map[VarName, Type], store: Store, gen: Generator): (Result[Stream[Pure, Map[VarName, Value]]], Store) =
    gen match {
      case MatchAssign(patt, target) =>
        val (tres, store_) = evalLocal(localVars, store, target)
        tres match {
          case SuccessResult(tval) => (matchPatt(store_, tval, patt).point[Result], store_)
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
              case _ => (ExceptionalResult(Error(Set(NotEnumerableError(tval)))), store_)
            }
          case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
        }
    }

  private
  def evalAssignable(localVars: Map[VarName, Type], store: Store, assgn: Assignable): (Result[DataPath[Value]], Store) = {
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
          case ExceptionalResult(_) => (targetres, store__)
        }
    }
  }

  private def evalAssert(localVars: Map[VarName, Type], store: Store, cond: Expr) = {
    val (condres, store_) = evalLocal(localVars, store, cond)
    condres match {
      case SuccessResult(condval) =>
        condval match {
          case ConstructorValue("true", Seq()) => (condres, store_)
          case ConstructorValue("false", Seq()) => (ExceptionalResult(Error(Set(AssertionError(cond)))), store_)
          case _ => (ExceptionalResult(Error(Set(TypeError(condval, DataType("Bool"))))), store_)
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalTryFinally(localVars: Map[VarName, Type], store: Store, tryB: Expr, finallyB: Expr) = {
    val (tryres, store__) = evalLocal(localVars, store, tryB)
    val (finres, store_) = evalLocal(localVars, store__, finallyB)
    finres match {
      case SuccessResult(_) => (tryres, store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalTryCatch(localVars: Map[VarName, Type], store: Store, tryB: Expr, catchVar: VarName, catchB: Expr) = {
    val (tryres, store__) = evalLocal(localVars, store, tryB)
    tryres match {
      case SuccessResult(tryval) => (tryval.point[Result], store__)
      case ExceptionalResult(exres) =>
        exres match {
          case Throw(value) =>
            val (res, store_) = evalLocal(localVars, Store(store__.map.updated(catchVar, value)), catchB)
            (res, Store(store_.map - catchVar))
          case _ => (ExceptionalResult(exres), store__)
        }
    }
  }

  private def evalThrow(localVars: Map[VarName, Type], store: Store, evl: Expr) = {
    val (res, store_) = evalLocal(localVars, store, evl)
    res match {
      case SuccessResult(vl) => (ExceptionalResult(Throw(vl)), store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalSolve(localVars: Map[VarName, Type], store: Store, vars: Seq[VarName], body: Expr) = {
    def loopSolve(store: Store): (Result[Value], Store) = {
      val (bodyres, store_) = evalLocal(localVars, store, body)
      bodyres match {
        case SuccessResult(v) =>
          val posNonDefinedPrevVar = vars.find(!store.map.contains(_))
          val posNonDefinedNewVar = vars.find(!store_.map.contains(_))
          if (posNonDefinedPrevVar.isDefined)
            (ExceptionalResult(Error(Set(UnassignedVarError(posNonDefinedPrevVar.get)))), store_)
          else if (posNonDefinedNewVar.isDefined)
            (ExceptionalResult(Error(Set(UnassignedVarError(posNonDefinedNewVar.get)))), store_)
          else {
            if (vars.toList.map(store.map).zip(vars.toList.map(store_.map)).forall { case (v1, v2) => v1 == v2 })
              (SuccessResult(v), store_)
            else loopSolve(store_)
          }
        case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
      }
    }
    loopSolve(store)
  }

  private def evalWhile(localVars: Map[VarName, Type], store: Store, cond: Expr, body: Expr) = {
    def loopWhile(store: Store): (Result[Unit], Store) = {
      val (condres, store__) = evalLocal(localVars, store, cond)
      condres match {
        case SuccessResult(condval) =>
          condval match {
            case ConstructorValue("true", Seq()) =>
              val (bodyres, store_) = evalLocal(localVars, store__, body)
              bodyres match {
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
            case _ => (ExceptionalResult(Error(Set(TypeError(condval, DataType("Bool"))))), store__)
          }
        case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
      }
    }
    val (res, store_) = loopWhile(store)
    (res.map(_ => BottomValue), store_)
  }

  private def evalFor(localVars: Map[VarName, Type], store: Store, gen: Generator, body: Expr) = {
    val (genres, store__) = evalGenerator(localVars, store, gen)
    genres match {
      case SuccessResult(envs) =>
        val (bodyres, store_) = evalEach(localVars, store__, envs, body)
        (bodyres.map { _ => BottomValue }, store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalBlock(localVars: Map[VarName, Type], store: Store, vardefs: Seq[Parameter], exprs: Seq[Expr]) = {
    val localVars_ = localVars ++ vardefs.map(par => par.name -> par.typ)
    val (res, store__) = evalLocalAll(localVars_, store, exprs)
    val store_ = Store(store__.map -- vardefs.map(_.name))
    res match {
      case SuccessResult(vals) => (vals.lastOption.getOrElse(BottomValue).pure[Result], store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalVisit(localVars: Map[VarName, Type], store: Store, strategy: Strategy, scrutinee: Expr, cases: Seq[Case]) = {
    val (scrres, store__) = evalLocal(localVars, store, scrutinee)
    scrres match {
      case SuccessResult(scrval) =>
        val (caseres, store_) = evalVisitStrategy(strategy, localVars, store__, scrval, cases.toList)
        caseres match {
          case SuccessResult(caseval) => (caseval.point[Result], store_)
          case ExceptionalResult(exres) =>
            exres match {
              case Fail => (scrval.point[Result], store_)
              case _ => (ExceptionalResult(exres), store_)
            }
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalSwitch(localVars: Map[VarName, Type], store: Store, scrutinee: Expr, cases: Seq[Case]) = {
    val (scrres, store__) = evalLocal(localVars, store, scrutinee)
    scrres match {
      case SuccessResult(scrval) =>
        val (caseres, store_) = evalCases(localVars, store__, scrval, cases.toList)
        caseres match {
          case SuccessResult(caseval) =>
            (caseval.point[Result], store_)
          case ExceptionalResult(exres) =>
            exres match {
              case Fail => (BottomValue.point[Result], store_)
              case _ => (ExceptionalResult(exres), store_)
            }
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalIf(localVars: Map[VarName, Type], store: Store, cond: Expr, thenB: Expr, elseB: Expr) = {
    val (condres, store__) = evalLocal(localVars, store, cond)
    condres match {
      case SuccessResult(condv) =>
        condv match {
          case ConstructorValue("true", Seq()) => evalLocal(localVars, store__, thenB)
          case ConstructorValue("false", Seq()) => evalLocal(localVars, store__, elseB)
          case _ => (ExceptionalResult(Error(Set(TypeError(condv, DataType("Bool"))))), store__)
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalAssign(localVars: Map[VarName, Type], store: Store, assgn: Assignable, targetexpr: Expr) = {
    val (assgnres, store__) = evalAssignable(localVars, store, assgn)
    assgnres match {
      case SuccessResult(path) =>
        val (targetres, store_) = evalLocal(localVars, store__, targetexpr)
        targetres match {
          case SuccessResult(vl) =>
            val newValue =
              if (path.accessPaths.isEmpty) {
                vl.point[Result]
              } else store_.map.get(path.varName).fold[Result[Value]](ExceptionalResult(Error(Set(UnassignedVarError(path.varName))))) {
                ovl => updatePath(ovl, path.accessPaths, vl)
              }
            newValue match {
              case SuccessResult(nvl) =>
                val varty = if (localVars.contains(path.varName)) localVars(path.varName) else module.globalVars(path.varName)
                if (typing.checkType(nvl, varty)) {
                  (nvl.pure[Result], Store(store_.map.updated(path.varName, nvl)))
                }
                else (ExceptionalResult(Error(Set(TypeError(nvl, varty)))), store_)
              case _ => (newValue, store_)
            }
          case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalReturn(localVars: Map[VarName, Type], store: Store, evl: Expr) = {
    val (res, store_) = evalLocal(localVars, store, evl)
    res match {
      case SuccessResult(vl) => (ExceptionalResult(Return(vl)), store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalFunCall(localVars: Map[VarName, Type], store: Store, functionName: VarName, args: Seq[Expr]) = {
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
                    case _ => (ExceptionalResult(Error(Set(OtherError))), callstore)
                  }
                case "toString" =>
                  val arg = callstore.map("earg")
                  (SuccessResult(BasicValue(StringLit(arg.toString))), callstore) // TO DO - Use pretty printing instead
                case _ => (ExceptionalResult(Error(Set(OtherError))), callstore)
              }
          }
          val store_ = Store(module.globalVars.map { case (x, _) => (x, resstore.map(x)) } ++ store__.map)

          def funcallsuccess(resval: Value): (Result[Value], Store) = {
            if (typing.checkType(resval, funresty)) (resval.point[Result], store_)
            else (ExceptionalResult(Error(Set(TypeError(resval, funresty)))), store_)
          }

          res match {
            case SuccessResult(resval) => funcallsuccess(resval)
            case ExceptionalResult(exres) =>
              exres match {
                case Return(value) => funcallsuccess(value)
                case Throw(value) => (ExceptionalResult(Throw(value)), store_)
                case Break | Continue | Fail => (ExceptionalResult(Error(Set(EscapedControlOperator))), store_)
                case _ => (ExceptionalResult(exres), store_)
              }
          }
        }
        else (ExceptionalResult(Error(Set(SignatureMismatch(functionName, argvals, funpars.map(_.typ))))), store__)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalMapUpdate(localVars: Map[VarName, Type], store: Store, emap: Expr, ekey: Expr, evl: Expr) = {
    val (mapres, store___) = evalLocal(localVars, store, emap)
    mapres match {
      case SuccessResult(mapv) =>
        mapv match {
          case MapValue(vals) =>
            val (keyres, store__) = evalLocal(localVars, store___, ekey)
            keyres match {
              case SuccessResult(keyv) =>
                if (keyv == BottomValue) (ExceptionalResult(Error(Set(OtherError))), store__)
                else {
                  val (valres, store_) = evalLocal(localVars, store__, evl)
                  valres match {
                    case SuccessResult(valv) =>
                      if (valv == BottomValue) (ExceptionalResult(Error(Set(OtherError))), store_)
                      else (MapValue(vals.updated(keyv, valv)).pure[Result], store_)
                    case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
                  }
                }
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
            }
          case _ => (ExceptionalResult(Error(Set(TypeError(mapv, MapType(ValueType, ValueType))))), store___)
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store___)
    }
  }

  private def evalMapLookup(localVars: Map[VarName, Type], store: Store, emap: Expr, ekey: Expr) = {
    val (mapres, store__) = evalLocal(localVars, store, emap)
    mapres match {
      case SuccessResult(mapv) =>
        mapv match {
          case MapValue(vals) =>
            val (keyres, store_) = evalLocal(localVars, store__, ekey)
            keyres match {
              case SuccessResult(keyv) =>
                if (vals.contains(keyv)) (vals(keyv).pure[Result], store_)
                else (ExceptionalResult(Throw(ConstructorValue("NoKey", Seq(keyv)))), store_)
              case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
            }
          case _ => (ExceptionalResult(Error(Set(TypeError(mapv, MapType(ValueType, ValueType))))), store__)
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalMap(localVars: Map[VarName, Type], store: Store, keyvalues: Seq[(Expr, Expr)]) = {
    val (keyres, store__) = evalLocalAll(localVars, store, keyvalues.map(_._1))
    keyres match {
      case SuccessResult(keys) =>
        val (valres, store_) = evalLocalAll(localVars, store__, keyvalues.map(_._2))
        valres match {
          case SuccessResult(vals) =>
            assert(keys.length == vals.length)
            if (!keys.contains(BottomValue) && !vals.contains(BottomValue)) (MapValue(keys.zip(vals).toMap).pure[Result], store_)
            else (ExceptionalResult(Error(Set(OtherError))), store_)
          case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
        }
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store__)
    }
  }

  private def evalSet(localVars: Map[VarName, Type], store: Store, elements: Seq[Expr]) = {
    val (res, store_) = evalLocalAll(localVars, store, elements)
    res match {
      case SuccessResult(vals) =>
        if (!vals.contains(BottomValue)) (SetValue(vals.toSet).pure[Result], store_)
        else (ExceptionalResult(Error(Set(OtherError))), store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalList(localVars: Map[VarName, Type], store: Store, elements: Seq[Expr]) = {
    val (res, store_) = evalLocalAll(localVars, store, elements)
    res match {
      case SuccessResult(vals) =>
        if (!vals.contains(BottomValue)) (ListValue(vals).pure[Result], store_)
        else (ExceptionalResult(Error(Set(OtherError))), store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalConstructor(localVars: Map[VarName, Type], store: Store, name: ConsName, args: Seq[Expr]) = {
    val (argsres, store_) = evalLocalAll(localVars, store, args)
    argsres match {
      case SuccessResult(vals) =>
        val (_, parameters) = module.constructors(name)
        if (vals.length == parameters.length &&
          !vals.contains(BottomValue) &&
          vals.zip(parameters.map(_.typ)).forall((typing.checkType _).tupled))
          (ConstructorValue(name, vals).pure[Result], store_)
        else (ExceptionalResult(Error(Set(SignatureMismatch(name, vals, parameters.map(_.typ))))), store_)
      case ExceptionalResult(exres) => (ExceptionalResult(exres), store_)
    }
  }

  private def evalBinary(localVars: Map[VarName, Type], store: Store, left: Expr, op: OpName, right: Expr) = {
    val (lhres, store__) = evalLocal(localVars, store, left)
    lhres match {
      case SuccessResult(lhval) =>
        val (rhres, store_) = evalLocal(localVars, store__, right)
        (rhres.flatMap(rhval => evalBinaryOp(lhval, op, rhval)), store_)
      case _ => (lhres, store__)
    }
  }

  private def evalUnary(localVars: Map[VarName, Type], store: Store, op: OpName, operand: Expr) = {
    val (res, store_) = evalLocal(localVars, store, operand)
    (res.flatMap(vl => evalUnaryOp(op, vl)), store_)
  }

  private def evalFieldAccess(localVars: Map[VarName, Type], store: Store, target: Expr, fieldName: FieldName) = {
    val (targetres, store_) = evalLocal(localVars, store, target)
    targetres match {
      case SuccessResult(tv) => (accessField(tv, fieldName), store_)
      case _ => (targetres, store_)
    }
  }

  private def evalVar(store: Store, x: VarName) = {
    if (store.map.contains(x)) (store.map(x).pure[Result], store)
    else (ExceptionalResult(Error(Set(UnassignedVarError(x)))), store)
  }

  private
  def evalLocal(localVars: Map[VarName, Type], store: Store, expr: Expr): (Result[Value], Store) = {
    expr match {
      case BasicExpr(b) => (BasicValue(b).pure[Result], store)
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
      case BreakExpr => (ExceptionalResult(Break), store)
      case ContinueExpr => (ExceptionalResult(Continue), store)
      case FailExpr => (ExceptionalResult(Fail), store)
      case LocalBlockExpr(vardefs, exprs) => evalBlock(localVars, store, vardefs, exprs)
      case ForExpr(enum, body) => evalFor(localVars, store, enum, body)
      case WhileExpr(cond, body) => evalWhile(localVars, store, cond, body)
      case SolveExpr(vars, body) => evalSolve(localVars, store, vars, body)
      case ThrowExpr(evl) => evalThrow(localVars, store, evl)
      case TryCatchExpr(tryB, catchVar, catchB) => evalTryCatch(localVars, store, tryB, catchVar, catchB)
      case TryFinallyExpr(tryB, finallyB) => evalTryFinally(localVars, store, tryB, finallyB)
      case AssertExpr(cond) => evalAssert(localVars, store, cond)
    }
  }

  def eval(store: Store, expr: Expr): (Result[Value], Store) = evalLocal(Map.empty, store, expr)
}

object ConcreteExecutor {
  private
  def evaluateGlobalVariables(executor: ConcreteExecutor, globVars: List[(VarName, Expr)]) = {
    val initStore = Store(globVars.toMap.mapValues(_ => BottomValue))
    globVars.reverse.foldLeftM[String \/ ?, Store](initStore) {
      (store, unevalglobvar) =>
        val (varname, varexpr) = unevalglobvar
        val (res, store_) = executor.eval(store, varexpr)
        res match {
          case ExceptionalResult(exres) => s"Evaluation of left-hand side for variable $varname failed with $exres".left
          case SuccessResult(value) => Store(map = store_.map.updated(varname, value)).right
        }
    }
  }

  private
  def executeTests(executor: ConcreteExecutor, tests: List[TestDef], store: Store) = {
    tests.foldLeftM[String \/ ?, List[VarName]](List()) { (failed, test) =>
      val (res, _) = executor.eval(store, test.body)
      res match {
        case SuccessResult(ConstructorValue("true", Seq()))
             | ExceptionalResult(Return(ConstructorValue("true", Seq()))) => failed.right
        case SuccessResult(_)
             | ExceptionalResult(Return(_)) => (failed :+ test.name).right
        case ExceptionalResult(exres) => s"Evaluation of test ${test.name} failed with $exres".left
      }
    }.map(failed => (store, failed))
  }

  def execute(module: syntax.ModuleDef): String \/ ExecutionResult = {
    for (transr <- ModuleTranslator.translateModule(module);
         executor = ConcreteExecutor(transr.semmod);
         store <- evaluateGlobalVariables(executor, transr.globalVarDefs);
         testr <- executeTests(executor, transr.tests, store);
         (store_, failed) = testr
    ) yield ExecutionResult(store_, transr.semmod, failed)
  }
}