package semantics

import java.lang.ThreadLocal
import java.time.{Duration, Instant}

import com.typesafe.scalalogging.StrictLogging
import org.slf4j.LoggerFactory
import semantics.domains.abstracting.IntegerW._
import semantics.domains.abstracting.Intervals.Positive.{Lattice => PosLattice}
import semantics.domains.abstracting.Intervals.Unbounded.{Lattice => UnboundedLattice}
import semantics.domains.abstracting.RefinementChildren.{getCons, getNil, makeCons, makeNil}
import semantics.domains.abstracting.TypeStore.TypeResult
import semantics.domains.abstracting._
import semantics.domains.common.Unit._
import semantics.domains.common._
import semantics.domains.concrete.TypeOps._
import semantics.typing.AbstractTyping
import syntax._
import util.Memoization._

import scala.annotation.tailrec
import scala.reflect.ClassTag
import scalaz.\/
import scalaz.std.list._
import scalaz.std.option._
import scalaz.syntax.either._
import scalaz.syntax.traverse._

// TODO: Convert lub(...flatMap) to map(...lub)
case class AbstractRefinementTypeExecutor(module: Module, initialRefinements: Refinements,
                                          memoWidening: MemoWidening, refinedMatching: Boolean) extends StrictLogging {
  private
  val memocacheSize = 10000

  private
  val atyping = AbstractTyping(module)

  private
  val refinements: Refinements = initialRefinements

  private
  val typememoriesops = TypeMemoriesOps(module, refinements)

  private
  val _memoMissesCount = ThreadLocal.withInitial[Int](() => 0)

  private
  val _memoHitsCount = ThreadLocal.withInitial[Int](() => 0)

  private
  val _memoWideningCount = ThreadLocal.withInitial[Int](() => 0)

  def memoMissesCount: Int = _memoMissesCount.get

  def memoHitsCount: Int = _memoHitsCount.get

  def memoWideningCount: Int = _memoWideningCount.get

  def resetMemoCounters(): Unit = {
    _memoMissesCount.set(0)
    _memoHitsCount.set(0)
    _memoWideningCount.set(0)
  }

  import typememoriesops._
  import refinementtypeops._
  import typestoreops._

  private
  type FunMemo = Map[(VarName, List[Type]), ((List[VoideableRefinementType], TypeStore), TypeMemories[VoideableRefinementType, Unit])]

  private
  type VMemo = Map[Any, ((VoideableRefinementType, TypeStore), TypeMemories[VoideableRefinementType, VoideableRefinementType])]

  private
  type VMemoAll = Map[RefinementChildren[RefinementType], (TypeStore, TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]])]

  private
  def ifFail[T](res: TypeResult[T,T]): T = res match {
    case SuccessResult(typ_) => typ_
    case ExceptionalResult(Fail(typ)) => typ
    case _ => throw new UnsupportedOperationException(s"ifFail($res)")
  }

  private
  def safeReconstruct(scrtyp: VoideableRefinementType,
                      cvtys: RefinementChildren[VoideableRefinementType]): VoideableRefinementType = {
    reconstruct(scrtyp, cvtys).head match {
      case SuccessResult(t) => t
      case ExceptionalResult(_) => throw new Exception("safeReconstruct")
    }
  }

  private
  def reconstruct(scrtyp: VoideableRefinementType,
                  cvtchildren: RefinementChildren[VoideableRefinementType]): Set[TypeResult[VoideableRefinementType, Nothing]] = {
    scrtyp.refinementType match {
      case BaseRefinementType(b) =>
        cvtchildren match {
          case FixedSeqChildren(cvtys) =>
            if (cvtys.isEmpty) Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(b))))
            else Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, cvtys)))))
          case _ => throw new UnsupportedOperationException()
        }
      case DataRefinementType(dataname, refinenameo) =>
        cvtchildren match {
          case FixedSeqChildren(cvtys) =>
            val constructors = refinenameo.fold(module.datatypes(dataname).toSet)(refinename => refinements.definitions.apply(refinename).conss.keySet)
            val consres = constructors.foldLeft[Set[TypeResult[Map[ConsName, List[RefinementType]], Nothing]]](Set(SuccessResult(Map.empty)))
              { (prevres, cons) =>
                prevres.flatMap[TypeResult[Map[ConsName, List[RefinementType]], Nothing], Set[TypeResult[Map[ConsName, List[RefinementType]], Nothing]]] {
                  case SuccessResult(consmap) =>
                    val (_, parameters) = module.constructors(cons)
                    val zipped = cvtys.zip(parameters.map(_.typ))
                    val posSuc: Set[TypeResult[Map[ConsName, List[RefinementType]], Nothing]] =
                      if (cvtys.length == parameters.length &&
                        zipped.forall { case (vrty, ty) => atyping.checkType(vrty.refinementType, ty).contains(true) }) {
                        // TODO Update shapes to be at most as precise as the target type
                        Set(SuccessResult(consmap.updated(cons, cvtys.map(_.refinementType))))
                      } else Set()
                    val posEx: Set[TypeResult[Map[ConsName, List[RefinementType]], Nothing]] =
                      if (cvtys.length != parameters.length ||
                          zipped.exists { case (vrty, ty) => atyping.checkType(vrty.refinementType, ty).contains(false) } ||
                          cvtys.exists(_.possiblyVoid))
                        Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, cvtys)))))
                      else Set()
                    posEx ++ posSuc
                  case ExceptionalResult(exres) => Set(ExceptionalResult(exres))
                }
            }
            consres.map {
              case SuccessResult(consmap) =>
                val newRn = refinements.newRefinement(dataname)
                val newrnopt = addRefinement(dataname, newRn, consmap)
                SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType(dataname, newrnopt)))
              case ExceptionalResult(exres) => ExceptionalResult(exres)
            }
          case _ => throw new UnsupportedOperationException()
        }
      case ListRefinementType(_,_) =>
        cvtchildren match {
          case ArbitrarySeqChildren(childty, size) =>
            val exRes =
              if (childty.possiblyVoid)
                Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, List(childty))))))
              else Set()
            val succRes =
              Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, ListRefinementType(childty.refinementType, size))))
            exRes ++ succRes
          case _ => throw new UnsupportedOperationException()
        }
      case SetRefinementType(_,_) =>
        cvtchildren match {
          case ArbitrarySeqChildren(childty, size) =>
            val exRes =
              if (childty.possiblyVoid)
                Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, List(childty))))))
              else Set()
            val newSize = Lattice[Intervals.Positive.Interval].lub(Intervals.Positive.singleton(0), size)
            val succRes = Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, SetRefinementType(childty.refinementType, newSize))))
            exRes ++ succRes
          case _ => throw new UnsupportedOperationException()
        }
      case MapRefinementType(_, _, size) =>
        cvtchildren match {
          case FixedSeqChildren(cvtys) =>
            val exRes =
              if (cvtys.exists(_.possiblyVoid)) Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, cvtys)))))
              else Set()
            val (nktys, nvtys) = cvtys.map(_.refinementType).splitAt(cvtys.length / 2)
            val newKeyType = Lattice[RefinementType].lubs(nktys.toSet)
            val newValType = Lattice[RefinementType].lubs( nvtys.toSet)
            val sucRes = Set(SuccessResult(VoideableRefinementType(scrtyp.possiblyVoid, MapRefinementType(newKeyType, newValType, size))))
            exRes ++ sucRes
          case _ =>
            // TODO Fix so it works with more precise sequence of children
            /*
            case ArbitrarySeqChildren(childty, size) =>
              val exRes =
                if (childty.possiblyVoid)
                  Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, List(childty))))))
                else Set()
              val newSize = Lattice[Intervals.Positive.Interval].lub(Intervals.Positive.singleton(0),
                Intervals.Positive./(size, Intervals.Positive.singleton(2)))
              // We lose a bit of precision here since we combine the sequences
              val succRes = Set(SuccessResult(VoideableRefinementType(possiblyVoid = false,
                                   MapRefinementType(childty.refinementType, childty.refinementType, newSize))))
              exRes ++ succRes
            */
            throw new UnsupportedOperationException()
        }
      case NoRefinementType =>
        cvtchildren match {
          case FixedSeqChildren(cvtys) =>
            if (scrtyp.possiblyVoid && cvtys.isEmpty) Set(SuccessResult(VoideableRefinementType(scrtyp.possiblyVoid, NoRefinementType)))
            else Set()
          case _ => throw new UnsupportedOperationException()
        }
      case ValueRefinementType =>
        Set(ExceptionalResult(Error(Set(ReconstructError(scrtyp, List())))), SuccessResult(VoideableRefinementType(scrtyp.possiblyVoid, ValueRefinementType)))
    }
  }

  private
  def refineEq(vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): Option[VoideableRefinementType] = {
    val vrtyglb = Lattice[VoideableRefinementType].glb(vrty1, vrty2)
    if (Lattice[VoideableRefinementType].isBot(vrtyglb)) None
    else Some(vrtyglb)
  }

  def refineNeq(vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): Option[(VoideableRefinementType, VoideableRefinementType)] = {
    (vrty1.refinementType, vrty2.refinementType) match {
      case (DataRefinementType(dn1, _), DataRefinementType(dn2, _)) if dn1 == dn2 =>
        val drglb = Lattice[RefinementType].glb(vrty1.refinementType, vrty2.refinementType)
        if (Lattice[RefinementType].isBot(drglb)) None
        else {
          val drnegglb = refinementtypeops.negate(drglb)
          val vrty1r = vrty1.copy(refinementType = Lattice[RefinementType].glb(vrty1.refinementType, drnegglb))
          val vrty2r = vrty2.copy(refinementType = Lattice[RefinementType].glb(vrty2.refinementType, drnegglb))
          Some((vrty1r, vrty2r))
        }
      case _ => Some((vrty1, vrty2)) // Currently there is no way to refine inequality for the rest of the domains
    }
  }

  // Use Set instead of Stream for nicer equality, and easier structural traversal when having alternatives
  def mergePairs(pairs: Set[(Map[VarName, VoideableRefinementType], Map[VarName, VoideableRefinementType])]): Set[Set[Map[VarName, VoideableRefinementType]]] = {
    // TODO Seems to lose the laziness, but I am still unsure how to recover that
    val merged = pairs.toList.traverse[List, Map[VarName, VoideableRefinementType]] { case (env1, env2) =>
      val commonVars = env1.keySet.intersect(env2.keySet)
      val refinedEqCommon = commonVars.toList.foldLeftM[Option, Map[VarName, VoideableRefinementType]](Map.empty[VarName, VoideableRefinementType]) { (commonVarVals, x) =>
        refineEq(env1(x), env2(x)).map { xval => commonVarVals.updated(x, xval) }
      }
      refinedEqCommon.fold[List[Map[VarName, VoideableRefinementType]]](List()) { commonVarVals =>
        List(env1 ++ env2 ++ commonVarVals)
      }
    }
    merged.map(_.toSet).toSet
  }

  def merge(envss: List[Set[Map[VarName, VoideableRefinementType]]]): Set[Set[Map[VarName, VoideableRefinementType]]] = {
    envss.foldLeft[Set[Set[Map[VarName, VoideableRefinementType]]]](Set(Set(Map()))) { (envsset, merged) =>
      envsset.flatMap { envs =>
        val pairsEnvs = envs.flatMap { env => merged.map(menv => (env, menv)) }
        mergePairs(pairsEnvs)
      }
    }
  }

  def matchPattAll[RT <: RefinementType : ClassTag](store: TypeStore, scrtyp: RefinementType, size: Intervals.Positive.Interval, spatts: List[StarPatt],
                   construct: (RefinementType, Intervals.Positive.Interval) => RT,
                   destruct: RT => (RefinementType, Intervals.Positive.Interval)): Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] = {
    if (Lattice[Intervals.Positive.Interval].isBot(size)) Set()
    else spatts match {
      // No refinements on store and scrutinee possible on empty list pattern on failure, and if succesful we can be more specific about the element type
      case Nil =>
        val errMatch: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])]  =
          if (IntegerW.<(0, size.ub))
            Set((store, construct(scrtyp, Intervals.Positive.makeInterval(IntegerW.max(1, size.lb), size.ub)), Set()))
          else Set()
        val succMatch: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] =
          if (Intervals.Positive.contains(size, 0))
            Set((store, construct(NoRefinementType, Intervals.Positive.singleton(0)), Set(Map())))
          else Set()
        errMatch ++ succMatch
      case sp :: sps =>
        sp match {
          case OrdinaryPatt(p) =>
            // If the concrete list happens to be empty, NoRefinementType is the most precise sound abstraction we can give of the elements on failure
            val errMatch: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] =
              if (Intervals.Positive.contains(size, 0))
                Set((store, construct(NoRefinementType, Intervals.Positive.singleton(0)), Set[Map[VarName, VoideableRefinementType]]()))
              else Set()
            val succMatch: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] =
              if (IntegerW.<(0, size.ub))
                matchPatt(store, VoideableRefinementType(possiblyVoid = false, scrtyp), p).flatMap { case (refinestore, vrefinescrtyp, envp) =>
                  // Use the same scrtyp (and not the refined one) since refinement of individual elements in collection does not affect other elements
                  matchPattAll(refinestore, scrtyp, Intervals.Positive.-(size, Intervals.Positive.singleton(1)), sps, construct, destruct).flatMap { case (refinestore2, refinescrtyp2, envps) =>
                    val mergeres = merge(List[Set[Map[VarName, VoideableRefinementType]]](envp, envps))
                    mergeres.map { mergedenvs =>
                      val (innerscrtyp2, refinesize) = destruct(refinescrtyp2)
                      val scrtyplub = Lattice[RefinementType].lub(vrefinescrtyp.refinementType, innerscrtyp2)
                      (refinestore2, construct(scrtyplub, Intervals.Positive.+(refinesize, Intervals.Positive.singleton(1))), mergedenvs)
                    }
                  }
                }
              else Set()
            errMatch ++ succMatch
          case ArbitraryPatt(sx) =>
            def bindVar: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] = {
              val bindRes: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] =
                matchPattAll(dropVars(store, Set(sx)), scrtyp, Intervals.Positive.makeInterval(0, size.ub), sps, construct, destruct).flatMap { case (refinestore, _, envps) =>
                  merge(List(Set(Map(sx -> VoideableRefinementType(possiblyVoid = false, construct(scrtyp, Intervals.Positive.makeInterval(0, size.ub))))),envps)).flatMap { mergeenv =>
                   Set((refinestore, construct(scrtyp, size), mergeenv))
                  }
                }
              val exhRes: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] = Set((dropVars(store, Set(sx)), construct(scrtyp, size), Set()))
              bindRes ++ exhRes
            }
            getVar(store, sx).fold(bindVar) { vsxtyp =>
              // When things are inequal we fail, and there is little refinement we can do in the general case
              // TODO investigate specific refinements for disequality
              val posBind: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] = if (vsxtyp.possiblyVoid) bindVar else Set()
              val posSucc: Set[(TypeStore, RT, Set[Map[syntax.VarName, VoideableRefinementType]])] = {
                val refined = refineEq(vsxtyp, VoideableRefinementType(possiblyVoid = false, construct(scrtyp, size)))
                refined.fold(Set[(TypeStore, RT, Set[Map[VarName, VoideableRefinementType]])]()) { vrteq =>
                  // Refine the store given that the patterns were equal
                  val refinestore = setVar(store, sx, vrteq)
                  val (_, eqsize) = destruct(implicitly[ClassTag[RT]].unapply(vrteq.refinementType).get)
                  val restsize = Intervals.Positive.makeInterval(IntegerW.-(size.lb, eqsize.ub), IntegerW.-(size.ub, eqsize.lb))
                  matchPattAll(refinestore, scrtyp, restsize, sps, construct, destruct).map { case (refinestore2, refinescrtyp, envp) =>
                    // We merge refinements of elements
                    val (innerscrtyp, _) = destruct(refinescrtyp)
                    val scrtyplub = Lattice[RefinementType].lub(vrteq.refinementType, innerscrtyp)
                    (refinestore2, construct(scrtyplub, size), envp)
                  }
                }
              }
              posBind ++ posSucc
            }
        }
    }
  }

  private
  type MatchPattRes = (TypeStore, VoideableRefinementType, Set[(Map[syntax.VarName, VoideableRefinementType])])

  // TODO Consider merging succesful and failing environments for optimization
  def matchPatt(store: TypeStore, scrvrtyp: VoideableRefinementType, cspatt: Patt): Set[MatchPattRes] = {
    val matchress: Set[MatchPattRes] = cspatt match {
      case BasicPatt(b) =>
        b match {
          case IntLit(i) => scrvrtyp.refinementType match {
            case BaseRefinementType(IntRefinementType(ival)) =>
              val included =
                if (Intervals.Unbounded.contains(ival, i))
                  Set[MatchPattRes]((store, VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Intervals.Unbounded.singleton(i)))), Set(Map())))
                else Set[MatchPattRes]()
              val excludeIval = Intervals.Unbounded.exclude(ival, i)
              val excluded =
                if (Lattice[Intervals.Unbounded.Interval].isBot(excludeIval)) Set[MatchPattRes]()
                else Set[MatchPattRes]((store, VoideableRefinementType(scrvrtyp.possiblyVoid, BaseRefinementType(IntRefinementType(excludeIval))), Set()))
              included ++ excluded
            case ValueRefinementType =>
              Set((store, scrvrtyp, Set()),
                (store, VoideableRefinementType(possiblyVoid = false,
                  BaseRefinementType(IntRefinementType(Intervals.Unbounded.singleton(i)))), Set(Map())))
            case _ => Set((store, scrvrtyp, Set()))
          }
          case StringLit(_) => scrvrtyp.refinementType match {
            case BaseRefinementType(StringRefinementType) | ValueRefinementType =>
              Set((store, scrvrtyp, Set()),
                (store, VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType)), Set(Map())))
            case _ => Set((store, scrvrtyp, Set()))
          }
        }
      case IgnorePatt => Set((store, scrvrtyp, Set(Map())))
      case VarPatt(name) =>
        def bindVar = Set((store, scrvrtyp, Set(Map(name -> scrvrtyp))))
        getVar(store, name).fold[Set[MatchPattRes]](bindVar) { xvrtyp =>
          val refineeqres = refineEq(scrvrtyp, VoideableRefinementType(possiblyVoid = false, xvrtyp.refinementType))
          val refineneqres = refineNeq(scrvrtyp, VoideableRefinementType(possiblyVoid = false, xvrtyp.refinementType))
          val posBind: Set[MatchPattRes] = if (xvrtyp.possiblyVoid) bindVar else Set()
          posBind ++
            Set[MatchPattRes](refineneqres.fold((store, scrvrtyp, Set[Map[VarName, VoideableRefinementType]]())) { case (nscrvrtyp, nxvrtyp) =>
              (setVar(store, name, nxvrtyp), nscrvrtyp, Set[Map[VarName, VoideableRefinementType]]())
            }) ++
              refineeqres.fold[Set[MatchPattRes]](Set()) { vrteq =>
                Set((setVar(store, name, vrteq), vrteq, Set(Map())))
              }
        }
      case ConstructorPatt(pattconsname, chpatts) =>
        val voidRes: Set[MatchPattRes] =
          if (scrvrtyp.possiblyVoid)
            Set((store, VoideableRefinementType(possiblyVoid = true, NoRefinementType), Set()))
          else Set()
        val dataRes: Set[MatchPattRes] = {
          val (dt, _) = module.constructors(pattconsname)
          val negGenMatch: Set[MatchPattRes] = Set((store, VoideableRefinementType(possiblyVoid = false, scrvrtyp.refinementType), Set()))
          def matchOn(rno: Option[Refinement]): Set[MatchPattRes] = {
            val refinementdef = rno.fold(dataTypeDefToRefinementDef(dt, typememoriesops.datatypes(dt)))(refinements.definitions)
            val failCons = refinementdef.conss - pattconsname
            val failRes: Set[MatchPattRes] =
              if (failCons.isEmpty) Set()
              else {
                val newRn = refinements.newRefinement(dt)
                val nrno = addRefinement(dt, newRn, failCons)
                Set((store, VoideableRefinementType(possiblyVoid = false, DataRefinementType(dt, nrno)), Set()))
              }
            val sucRes: Set[MatchPattRes] = {
              refinementdef.conss.get(pattconsname).fold(Set[MatchPattRes]()) { chvrtys =>
                val chrefres = chpatts.toList.zip(chvrtys).foldLeftM[List, (TypeStore, List[RefinementType], Set[Map[VarName, VoideableRefinementType]])]((store, List.empty, Set(Map[VarName, VoideableRefinementType]()))) {
                  case (st, (chpatt, chrty)) =>
                    val (prevrefinestore, prevrefinechrtys, prevenvs) = st
                    matchPatt(prevrefinestore, VoideableRefinementType(possiblyVoid = false, chrty), chpatt).toList.flatMap {
                      case (refinestore, refinechrty, chenvs) =>
                        val merged = merge(List(prevenvs, chenvs))
                        merged.map { menvss =>
                          (refinestore, prevrefinechrtys :+ refinechrty.refinementType, menvss)
                        }.toList
                    }
                }.toSet
                chrefres.map { case (refinestore, refinechrtys, chenvs) =>
                  val newRn = refinements.newRefinement(dt)
                  val nrno = addRefinement(dt, newRn, Map(pattconsname -> refinechrtys))
                  (refinestore, VoideableRefinementType(possiblyVoid = false, DataRefinementType(dt, nrno)), chenvs)
                }
              }
            }
            failRes ++ sucRes
          }
          scrvrtyp.refinementType match {
            case DataRefinementType(dn, rno) if dn == dt => matchOn(rno)
            case ValueRefinementType => negGenMatch ++ matchOn(None)
            case _ => negGenMatch
          }
        }
        voidRes ++ dataRes
      case LabelledTypedPatt(typ, labelVar, patt) =>
        val posEx: Set[MatchPattRes] =
          if (atyping.checkType(scrvrtyp.refinementType, typ).contains(false))
            Set((store, scrvrtyp, Set()))
          else Set()
        val posSuc: Set[MatchPattRes] = if (atyping.checkType(scrvrtyp.refinementType, typ).contains(true)) {
          val inmatchs = matchPatt(store, scrvrtyp, patt)
          inmatchs.flatMap { case (refinestore, refinescrvrtyp, inmatch) =>
            merge(List(Set(Map(labelVar -> scrvrtyp)), inmatch)).map { menvs => (refinestore, refinescrvrtyp, menvs) }
          }
        } else Set()
        posEx ++ posSuc
      case ListPatt(spatts) =>
        val voidRes: Set[MatchPattRes] =
          if (scrvrtyp.possiblyVoid)
            Set((store, VoideableRefinementType(possiblyVoid = true, NoRefinementType), Set()))
          else Set()
        val listRes: Set[MatchPattRes] = scrvrtyp.refinementType match {
          case ListRefinementType(elementType, length) =>
            matchPattAll[ListRefinementType](store, elementType, length, spatts.toList, ListRefinementType, lrt => (lrt.elementType, lrt.length)).map {
              case (refinestore, rty, envs) =>
                (refinestore, VoideableRefinementType(possiblyVoid = false, rty), envs)
            }
          case ValueRefinementType => Set[MatchPattRes]((store, scrvrtyp, Set())) ++
            matchPattAll[ListRefinementType](store, ValueRefinementType, Lattice[Intervals.Positive.Interval].top, spatts.toList, ListRefinementType, lrt => (lrt.elementType, lrt.length)).map {
              case (refinestore, rty, envs) =>
                (refinestore, VoideableRefinementType(possiblyVoid = false, rty), envs)
            }
          case _ =>
            Set((store, VoideableRefinementType(possiblyVoid = false, scrvrtyp.refinementType), Set()))
        }
        voidRes ++ listRes
      case SetPatt(spatts) =>
        val voidRes: Set[MatchPattRes] =
          if (scrvrtyp.possiblyVoid)
            Set((store, VoideableRefinementType(possiblyVoid = true, NoRefinementType), Set()))
          else Set()
        val setRes: Set[MatchPattRes] = scrvrtyp.refinementType match {
          case SetRefinementType(elementType, cardinality) =>
            matchPattAll[SetRefinementType](store, elementType, cardinality, spatts.toList, SetRefinementType, srt => (srt.elementType, srt.cardinality)).map {
              case (refinestore, rty, envs) =>
                (refinestore, VoideableRefinementType(possiblyVoid = false, rty), envs)
            }
          case ValueRefinementType => Set[MatchPattRes]((store, scrvrtyp, Set())) ++
            matchPattAll[SetRefinementType](store, ValueRefinementType, Lattice[Intervals.Positive.Interval].top, spatts.toList, SetRefinementType, srt => (srt.elementType, srt.cardinality)).map {
              case (refinestore, rty, envs) =>
                (refinestore, VoideableRefinementType(possiblyVoid = false, rty), envs)
            }
          case _ =>
            Set((store, VoideableRefinementType(possiblyVoid = false, scrvrtyp.refinementType), Set()))
        }
        voidRes ++ setRes
      case NegationPatt(patt) =>
        matchPatt(store, scrvrtyp, patt).map[MatchPattRes, Set[MatchPattRes]] { case (_, _, envs) =>
          // TODO Consider calculating better negations for refinements of stores and input
          // Drop local refinements since they are invalid
          if (envs.isEmpty) (store, scrvrtyp, Set(Map()))
          else (store, scrvrtyp, Set())
        }
      case DescendantPatt(patt) =>
        lazy val memoFix: (TypeStore, VoideableRefinementType,  Map[VoideableRefinementType, Set[MatchPattRes]]) => Set[MatchPattRes] =
          memoized[TypeStore, VoideableRefinementType,  Map[VoideableRefinementType, Set[MatchPattRes]], Set[MatchPattRes]](memocacheSize) { (store, vrtyp, memo) =>
            def go(prevres: Set[MatchPattRes]): Set[MatchPattRes] = {
              val newres = matchPatt(store, vrtyp, patt).flatMap { case (refinestore, refinevrtyp, selfenvs) =>
                val childrenres = children(refinevrtyp)
                childrenres.flatMap { case (_, refchildren) =>
                  refchildren match {
                    case FixedSeqChildren(chrtyps) =>
                      chrtyps.flatMap { chrtyp =>
                        val chrtyres = memoFix(refinestore, VoideableRefinementType(possiblyVoid = false, chrtyp), memo.updated(vrtyp, prevres))
                        chrtyres.map { case (nrefinestore, _, cenvss) =>
                          // TODO Think about refinement with descendants (does it require reconstruction?)
                          (nrefinestore, vrtyp, selfenvs.flatMap { senv =>  cenvss.map { cenv => senv ++ cenv } })
                        }
                      }
                    case ArbitrarySeqChildren(_, _) => throw new UnsupportedOperationException()
                  }
                }
              }
              // TODO Check whether the widening (on the output) here is correct
              if (newres == prevres) newres
              else go(prevres union newres)
            }
            memo.getOrElse(vrtyp, go(Set()))
        }
        memoFix(store, scrvrtyp, Map())
    }
    matchress.groupBy(_._3).toSet[(Set[Map[VarName, VoideableRefinementType]], Set[MatchPattRes])].map { case (envs, matchres) =>
      val allrefinestores = matchres.map(_._1)
      val refinestorelub = Lattice[TypeStore].lubs(allrefinestores)
      val allrefinetyps = matchres.map(_._2)
      val refinetypslub = Lattice[VoideableRefinementType].lubs(allrefinetyps)
      (refinestorelub, refinetypslub, envs)
    }
  }

  def evalVar(store: TypeStore, x: VarName): TypeMemories[VoideableRefinementType, Unit] = {
    val unassignedError = Set(TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(UnassignedVarError(x)))), store))
    getVar(store, x).fold(TypeMemories[VoideableRefinementType, Unit](unassignedError)) {
      case VoideableRefinementType(possUnassigned, rtyp) =>
        val posErr =
          if (possUnassigned) unassignedError
          else Set[TypeMemory[VoideableRefinementType, Unit]]()
        TypeMemories(posErr ++
          Set(TypeMemory[VoideableRefinementType, Unit](SuccessResult(VoideableRefinementType(possiblyVoid = false, rtyp)), store)))
    }
  }

  private
  def unflatMems[A](flatMems: TypeMemories[Flat[A], Unit]): TypeMemories[A, Unit] = {
    TypeMemories(flatMems.memories.map {
      case TypeMemory(res, st) =>
        TypeMemory(res match {
          case SuccessResult(t) => SuccessResult(Flat.unflat(t))
          case ExceptionalResult(exres) => ExceptionalResult(exres)
        }, st)
    })
  }

  def accessField(vrty: VoideableRefinementType, fieldName: FieldName): Set[TypeResult[VoideableRefinementType, Unit]] = {
    val voidRes: Set[TypeResult[VoideableRefinementType, Unit]] =
      if (vrty.possiblyVoid)
        Set(ExceptionalResult(Error(Set(FieldError(VoideableRefinementType(possiblyVoid = true, NoRefinementType), fieldName)))))
      else Set()
    val typRes: Set[TypeResult[VoideableRefinementType, Unit]] = vrty.refinementType match {
      case DataRefinementType(dn, rno) =>
        val refinementdef = rno.fold(dataTypeDefToRefinementDef(dn, typememoriesops.datatypes(dn)))(refinements.definitions)
        val fieldRes: Set[TypeResult[VoideableRefinementType, Unit]] = refinementdef.conss.map { case (cons, chrtys) =>
          val (_, pars) = module.constructors(cons)
          val index = pars.indexWhere(_.name == fieldName)
          if (index < 0) { ExceptionalResult(Error(Set(FieldError(vrty, fieldName)))) }
          else SuccessResult[VoideableRefinementType](VoideableRefinementType(possiblyVoid = false, chrtys(index)))
        }.toSet
        fieldRes
      case ValueRefinementType =>
        val fieldTypUB = Lattice[Type].lubs(module.constructors.values.toSet[(TypeName, List[Parameter])].map(_._2)
                                              .flatMap(pars => pars.find(_.name == fieldName).map(_.typ)))
          // Take lub of all possible field types
        Set(ExceptionalResult(Error(Set(FieldError(vrty, fieldName)))),
          SuccessResult(VoideableRefinementType(possiblyVoid = false, typeToRefinement(fieldTypUB))))
      case _ => Set(ExceptionalResult(Error(Set(FieldError(vrty, fieldName)))))
    }
    voidRes ++ typRes
  }

  def evalFieldAccess(localVars: Map[VarName, Type], store: TypeStore, target: Expr, fieldName: FieldName, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val targetmems = evalLocal(localVars, store, target, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(targetmems.memories.map { case TypeMemory(targetres, store_) =>
      targetres match {
        case SuccessResult(tv) =>
          Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(accessField(tv, fieldName).map(res =>
            TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(res, store_)))))
        case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(targetres, store_)))
      }
    })
  }

  def evalUnaryOp(op: OpName, vrtyp: VoideableRefinementType): Set[TypeResult[VoideableRefinementType, Unit]] = {
    if (Lattice[VoideableRefinementType].isBot(vrtyp)) Set()
    else {
      val errRes: Set[TypeResult[VoideableRefinementType, Unit]] = Set(ExceptionalResult(Error(Set(InvalidOperationError(op, List(vrtyp))))))
      val voidRes = if (vrtyp.possiblyVoid) errRes else Set[TypeResult[VoideableRefinementType, Unit]]()
      val rtyp = vrtyp.refinementType
      val typRes = (op, rtyp) match {
        case ("-", BaseRefinementType(IntRefinementType(ival))) =>
            Set(SuccessResult(VoideableRefinementType(possiblyVoid = false,
                              BaseRefinementType(IntRefinementType(Intervals.Unbounded.-(Intervals.Unbounded.singleton(0), ival))))))
        case ("-", ValueRefinementType)   =>
          errRes ++
            Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
        case ("!", DataRefinementType("Bool", rno)) =>
          rno.fold(Set[TypeResult[VoideableRefinementType, Unit]](SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", None))))) { rn =>
            refinements.definitions(rn).conss.toSet[(ConsName, List[RefinementType])].flatMap {
              case ("true", List()) =>
                val newRn = refinements.newRefinement("Bool")
                val newrhs = Map("false" -> List())
                val nrno = addRefinement("Bool", newRn, newrhs)
                Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", nrno))))
              case ("false", List()) =>
                val newRn = refinements.newRefinement("Bool")
                val newrhs = Map("true" -> List())
                val nrno = addRefinement("Bool", newRn, newrhs)
                Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", nrno))))
              case _ => throw NonNormalFormMemories
            }
          }
        case ("!", ValueRefinementType) =>
          errRes ++ Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", None))))
        case _ => errRes
      }
      voidRes ++ typRes
    }
  }

  def evalUnary(localVars: Map[VarName, Type], store: TypeStore, op: OpName, operand: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val mems = evalLocal(localVars, store, operand, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(mems.memories.map { case TypeMemory(res, store_) =>
        res match {
          case SuccessResult(vl) =>
            Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(evalUnaryOp(op, vl).map{ ures =>
              TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ures, store_)))
            })
          case ExceptionalResult(exres) =>
            TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_)))
        }
    })
  }


  def evalBinaryOp(lhvrtyp: VoideableRefinementType, op: OpName, rhvrtyp: VoideableRefinementType): Set[TypeResult[VoideableRefinementType, Unit]] = {
    val invOp = ExceptionalResult(Error(Set(InvalidOperationError(op, List(lhvrtyp, rhvrtyp)))))

    def boolToRefinement(b: Boolean): VoideableRefinementType = {
      val boolcons = if (b) "true" else "false"
      val newRn = refinements.newRefinement("Bool")
      val newrhs = Map(boolcons -> List[RefinementType]())
      val nrno = addRefinement("Bool", newRn, newrhs)
      VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", nrno))
    }

    def valEq(eqt: Boolean, lhvrtyp: VoideableRefinementType, rhvrtyp: VoideableRefinementType) = {
      val possiblyEq = refineEq(lhvrtyp, rhvrtyp).fold(Set[TypeResult[VoideableRefinementType, Unit]]()) { _ =>
        Set(SuccessResult(boolToRefinement(eqt)))
      }
      val possiblyNeq = refineNeq(lhvrtyp, rhvrtyp).fold(Set[TypeResult[VoideableRefinementType, Unit]]()) { _ =>
        Set(SuccessResult(boolToRefinement(!eqt)))
      }
      possiblyEq ++ possiblyNeq
    }

    def valIn(lrtyp: RefinementType, irtyp: RefinementType, size: Intervals.Positive.Interval) =
      refineEq(VoideableRefinementType(possiblyVoid = false, lrtyp), VoideableRefinementType(possiblyVoid = false, irtyp)).fold(Set(SuccessResult(boolToRefinement(false)))) {
        _ =>
          if (IntegerW.<=(size.ub,0)) Set(SuccessResult(boolToRefinement(false)))
          else Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", None))))
      }

    def boolAnd(lrno: Option[Refinement], rnro: Option[Refinement]): Set[TypeResult[VoideableRefinementType, Unit]] = {
      val lrefinedef = lrno.fold(dataTypeDefToRefinementDef("Bool", typememoriesops.datatypes("Bool")))(refinements.definitions)
      lrefinedef.conss.keySet.flatMap {
        case "true" =>
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", rnro))))
        case "false" =>
          val newRn = refinements.newRefinement("bool")
          val newrhs = Map("false" -> List[RefinementType]())
          val newrno = addRefinement("Bool", newRn, newrhs)
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", newrno))))
        case _ => throw NonNormalFormMemories
      }
    }

    def boolOr(lrno: Option[Refinement], rnro: Option[Refinement]): Set[TypeResult[VoideableRefinementType, Unit]] =  {
      val lrefinedef = lrno.fold(dataTypeDefToRefinementDef("Bool", typememoriesops.datatypes("Bool")))(refinements.definitions)
      lrefinedef.conss.keySet.flatMap {
        case "false" =>
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", rnro))))
        case "true" =>
          val newRn = refinements.newRefinement("bool")
          val newrhs = Map("true" -> List[RefinementType]())
          val newrno = addRefinement("Bool", newRn, newrhs)
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType("Bool", newrno))))
        case _ => throw NonNormalFormMemories
      }
    }

    if (Set(lhvrtyp, rhvrtyp).exists(Lattice[VoideableRefinementType].isBot)) Set()
    else (lhvrtyp.refinementType, op, rhvrtyp.refinementType) match {
      case (_, "==", _) => valEq(eqt = true, lhvrtyp, rhvrtyp)
      case (_, "!=", _) => valEq(eqt = false, lhvrtyp, rhvrtyp)
      case (_, "in", ListRefinementType(invrtyp, length)) =>
        (if (rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++ valIn(lhvrtyp.refinementType, invrtyp, length)
      case (_, "in", SetRefinementType(invrtyp, cardinality)) =>
        (if (rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++ valIn(lhvrtyp.refinementType, invrtyp, cardinality)
      case (_, "in", MapRefinementType(keyvrtyp, _, size)) =>
        (if (rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++ valIn(lhvrtyp.refinementType, keyvrtyp, size)
      case (_, "in", ValueRefinementType) =>
        Set(invOp) ++ valIn(lhvrtyp.refinementType, ValueRefinementType, Lattice[Intervals.Positive.Interval].top)
      case (_, "notin", _) => evalBinaryOp(lhvrtyp, "in", rhvrtyp).flatMap {
        case SuccessResult(ty) => evalUnaryOp("!", ty)
        case ExceptionalResult(exres) =>
          Set[TypeResult[VoideableRefinementType, Unit]](ExceptionalResult(exres))
      }
      case (DataRefinementType("Bool", lrno), "&&", DataRefinementType("Bool", rnro)) =>
        (if (rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++ boolAnd(lrno, rnro)
      case (ValueRefinementType, "&&", DataRefinementType("Bool", rnro)) =>
        Set(invOp) ++ boolAnd(None, rnro)
      case (DataRefinementType("Bool", lrno), "&&", ValueRefinementType) =>
        Set(invOp) ++ boolAnd(lrno, None)
      case (ValueRefinementType, "&&", ValueRefinementType) =>
        Set(invOp) ++ boolAnd(None, None)
      case (ValueRefinementType, "||", DataRefinementType("Bool", rnro)) =>
        (if (rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++ boolOr(None, rnro)
      case (DataRefinementType("Bool", lrno), "||", ValueRefinementType) =>
        Set(invOp) ++ boolOr(lrno, None)
      case (ValueRefinementType, "||", ValueRefinementType) =>
        Set(invOp) ++ boolOr(None, None)
      case (ListRefinementType(rty1, length1), "+", ListRefinementType(rty2, length2)) =>
        val tylub = Lattice[RefinementType].lub(rty1, rty2)
        Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, ListRefinementType(tylub, Intervals.Positive.+(length1, length2)))))
      case (ListRefinementType(_,_), "+", ValueRefinementType) | (ValueRefinementType, "+", ListRefinementType(_,_)) =>
        Set(invOp) ++ Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, ListRefinementType(ValueRefinementType, Lattice[Intervals.Positive.Interval].top))))
      case (SetRefinementType(rty1, cardinality1), "+", SetRefinementType(rty2, cardinality2)) =>
        val tylub = Lattice[RefinementType].lub(rty1, rty2)
        Set(SuccessResult(VoideableRefinementType(possiblyVoid = false,
          SetRefinementType(tylub, Intervals.Positive.makeInterval(IntegerW.max(cardinality1.lb, cardinality2.lb), IntegerW.+(cardinality1.ub, cardinality2.ub))))))
      case (SetRefinementType(_,_), "+", ValueRefinementType) | (ValueRefinementType, "+",SetRefinementType(_,_)) =>
        Set(invOp) ++ Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, SetRefinementType(ValueRefinementType, Lattice[Intervals.Positive.Interval].top))))
      case (MapRefinementType(krty1, vrty1, size1), "+", MapRefinementType(krty2, vrty2, size2)) =>
        val krtylub = Lattice[RefinementType].lub(krty1, krty2)
        val vrtylub = Lattice[RefinementType].lub(vrty1, vrty2)
        Set(SuccessResult(VoideableRefinementType(possiblyVoid = false,
          MapRefinementType(krtylub, vrtylub, Intervals.Positive.makeInterval(IntegerW.max(size1.lb, size2.lb), IntegerW.+(size1.ub, size2.ub))))))
      case (MapRefinementType(_,_,_), "+", ValueRefinementType) |
           (ValueRefinementType, "+", MapRefinementType(_,_,_)) =>
        Set(invOp) ++
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false,
                             MapRefinementType(ValueRefinementType, ValueRefinementType, Lattice[Intervals.Positive.Interval].top))))
      case (BaseRefinementType(StringRefinementType), "+", BaseRefinementType(StringRefinementType)) =>
        (if (lhvrtyp.possiblyVoid || rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType))))
      case (BaseRefinementType(IntRefinementType(ival1)), "+", BaseRefinementType(IntRefinementType(ival2))) =>
        (if (lhvrtyp.possiblyVoid || rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Intervals.Unbounded.+(ival1, ival2))))))
      case (BaseRefinementType(StringRefinementType), "+", ValueRefinementType) | (ValueRefinementType, "+", BaseRefinementType(StringRefinementType)) =>
        Set(invOp, SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType))))
      case (BaseRefinementType(IntRefinementType(_)), "+", ValueRefinementType) | (ValueRefinementType, "+", BaseRefinementType(IntRefinementType(_))) =>
        Set(invOp, SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
      case (ValueRefinementType, "+", ValueRefinementType) =>
        Set(invOp,
          SuccessResult(VoideableRefinementType(possiblyVoid = false, ValueRefinementType)))
      case (BaseRefinementType(IntRefinementType(ival1)), "-", BaseRefinementType(IntRefinementType(ival2))) =>
        (if (lhvrtyp.possiblyVoid || rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Intervals.Unbounded.-(ival1, ival2))))))
      case (ValueRefinementType | BaseRefinementType(IntRefinementType(_)), "-",  ValueRefinementType | BaseRefinementType(IntRefinementType(_))) =>
        Set(invOp, SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
      case (BaseRefinementType(IntRefinementType(ival1)), "*", BaseRefinementType(IntRefinementType(ival2))) =>
        (if (lhvrtyp.possiblyVoid || rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Intervals.Unbounded.*(ival1, ival2))))))
      case (ValueRefinementType | BaseRefinementType(IntRefinementType(_)), "*", ValueRefinementType | BaseRefinementType(IntRefinementType(_))) =>
        Set(invOp, SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
      case (BaseRefinementType(IntRefinementType(ival1)), "/", BaseRefinementType(IntRefinementType(ival2))) =>
        val exres =
          if (Intervals.Unbounded.contains(ival2, 0))
            Set(ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false, DataRefinementType("DivByZero", None)))))
          else Set()
        val divval = Intervals.Unbounded./(ival1, ival2)
        val succres =
          if (!Lattice[Intervals.Unbounded.Interval].isBot(divval))
            Set(SuccessResult(VoideableRefinementType(possiblyVoid = false,
              BaseRefinementType(IntRefinementType(divval)))))
          else Set()
        Set(invOp) ++ exres ++ succres
      case (ValueRefinementType, "/", BaseRefinementType(IntRefinementType(ival2))) =>
        val exres =
          if (Intervals.Unbounded.contains(ival2, 0))
            Set(ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false, DataRefinementType("DivByZero", None)))))
          else Set()
        Set(invOp) ++ exres ++
          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
      case (ValueRefinementType | BaseRefinementType(IntRefinementType(_)), "/", ValueRefinementType) =>
        Set(invOp,
          ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false, DataRefinementType("DivByZero", None)))),
          SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
      case (BaseRefinementType(IntRefinementType(ival1)), "%", BaseRefinementType(IntRefinementType(ival2))) =>
        val exres =
          if (IntegerW.<=(ival2.lb,0))
            Set(ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false, DataRefinementType("ModNonPos", None)))))
          else Set()
        val ival2pos = Intervals.Unbounded.makeInterval(1, ival2.ub)
        val modval = Intervals.Unbounded.%(ival1, ival2pos)
        val succres =
          if (!Lattice[Intervals.Unbounded.Interval].isBot(modval))
              Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(modval)))))
          else Set()
        (if (lhvrtyp.possiblyVoid || rhvrtyp.possiblyVoid) Set(invOp) else Set()) ++ exres ++ succres
      case (ValueRefinementType | BaseRefinementType(IntRefinementType(_)), "%", ValueRefinementType | BaseRefinementType(IntRefinementType(_))) =>
        Set(invOp,
          ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false, DataRefinementType("ModNonPos", None)))),
          SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(IntRefinementType(Lattice[Intervals.Unbounded.Interval].top)))))
      case _ => Set(invOp)
    }
  }

  def evalBinary(localVars: Map[VarName, Type], store: TypeStore, left: Expr, op: OpName, right: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val leftmems = evalLocal(localVars, store, left, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(leftmems.memories.map { case TypeMemory(lhres, store__) =>
        lhres match {
          case SuccessResult(lhval) =>
            val rightmems = evalLocal(localVars, store__, right, funMemo)
            Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(rightmems.memories.map { case TypeMemory(rhres, store_) =>
                rhres match {
                  case SuccessResult(rhval) =>
                    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(evalBinaryOp(lhval, op, rhval).map { res =>
                      TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(res, store_)))
                    })
                  case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(rhres, store_)))
                }
            })
          case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(lhres, store__)))
        }
    })
  }

  def evalConstructor(localVars: Map[VarName, Type], store: TypeStore, consname: ConsName, args: Seq[Expr], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val argmems = evalLocalAll(localVars, store, args, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(argmems.memories.map {
      case TypeMemory(argres, store_) =>
        argres match {
          case SuccessResult(vrtys) =>
            val (tyname, parameters) = module.constructors(consname)
            val tysparszipped = vrtys.zip(parameters.map(_.typ))
            val posEx: Set[TypeMemory[VoideableRefinementType, Unit]] =
              if (vrtys.length != parameters.length ||
                tysparszipped.exists { case (vrty, party) => vrty.possiblyVoid || atyping.checkType(vrty.refinementType, party).contains(false) })
                Set(TypeMemory(ExceptionalResult(Error(Set(SignatureMismatch(consname, vrtys, parameters.map(_.typ))))), store_))
              else Set()
            val posSuc: Set[TypeMemory[VoideableRefinementType, Unit]] =
              if (vrtys.length == parameters.length &&
                  tysparszipped.forall { case (vrty, party) => atyping.checkType(vrty.refinementType, party).contains(true) }) {
                val newRn = refinements.newRefinement(tyname)
                val newrhs = Map(consname -> vrtys.map(_.refinementType))
                val nrno = addRefinement(tyname, newRn, newrhs)
                Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType(tyname, nrno))), store_))
              } else Set()
            TypeMemories(posEx ++ posSuc)
          case ExceptionalResult(exres) =>
            TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_)))
        }
    })
  }

  def evalList(localVars: Map[VarName, Type], store: TypeStore, elements: Seq[Expr], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val elmems = evalLocalAll(localVars, store, elements, funMemo)
    TypeMemories(elmems.memories.flatMap[TypeMemory[VoideableRefinementType, Unit], Set[TypeMemory[VoideableRefinementType, Unit]]] { case TypeMemory(res, store_) =>
      res match {
        case SuccessResult(vrtys) =>
          val posEx: Set[TypeMemory[VoideableRefinementType, Unit]] =
            if (vrtys.exists(_.possiblyVoid)) Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store))
            else Set()
          val posSuc: Set[TypeMemory[VoideableRefinementType, Unit]] = {
            Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false,
              makeList(vrtys.map(_.refinementType)))), store))
          }
          posEx ++ posSuc
        case ExceptionalResult(exres) => Set(TypeMemory(ExceptionalResult(exres), store_))
      }
    })
  }


  def evalSet(localVars: Map[VarName, Type], store: TypeStore, elements: Seq[Expr], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val elmems = evalLocalAll(localVars, store, elements, funMemo)
    TypeMemories(elmems.memories.flatMap[TypeMemory[VoideableRefinementType, Unit], Set[TypeMemory[VoideableRefinementType, Unit]]] { case TypeMemory(res, store_) =>
      res match {
        case SuccessResult(vrtys) =>
          val posEx: Set[TypeMemory[VoideableRefinementType, Unit]] =
            if (vrtys.exists(_.possiblyVoid)) Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store))
            else Set()
          val posSuc: Set[TypeMemory[VoideableRefinementType, Unit]] = {
            Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false,
              makeSet(vrtys.map(_.refinementType)))), store))
          }
          posEx ++ posSuc
        case ExceptionalResult(exres) => Set(TypeMemory(ExceptionalResult(exres), store_))
      }
    })
  }

  def evalMap(localVars: Map[VarName, Type], store: TypeStore, keyvalues: Seq[(Expr, Expr)], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val keyexprs = keyvalues.map(_._1)
    val valexprs = keyvalues.map(_._2)
    val keymems = evalLocalAll(localVars, store, keyexprs, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(keymems.memories.map[TypeMemories[VoideableRefinementType, Unit], Set[TypeMemories[VoideableRefinementType, Unit]]] {
      case TypeMemory(keyres, store__) =>
        keyres match {
          case SuccessResult(keyvrtys) =>
            val valmems = evalLocalAll(localVars, store__, valexprs, funMemo)
            TypeMemories[VoideableRefinementType, Unit](valmems.memories.flatMap { case TypeMemory(valres, store_) =>
              valres match {
                case SuccessResult(valvrtys) =>
                  val posEx: Set[TypeMemory[VoideableRefinementType, Unit]] =
                    if (keyvrtys.exists(_.possiblyVoid) || valvrtys.exists(_.possiblyVoid))
                      Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store))
                    else Set()
                  val posSuc: Set[TypeMemory[VoideableRefinementType, Unit]] = {
                    Set(TypeMemory(SuccessResult(
                      VoideableRefinementType(possiblyVoid = false,
                        makeMap(keyvrtys.map(_.refinementType), valvrtys.map(_.refinementType)))), store_))
                  }
                  posEx ++ posSuc
                case ExceptionalResult(exres) =>
                  Set(TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(exres), store_))
              }
            })
          case ExceptionalResult(exres) => TypeMemories(Set(TypeMemory(ExceptionalResult(exres), store__)))
        }
    })
  }

  def evalMapLookup(localVars: Map[VarName, Type], store: TypeStore, emap: Expr, ekey: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val mapmems = evalLocal(localVars, store, emap, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(mapmems.memories.flatMap { case TypeMemory(mapres, store__) =>
      mapres match {
        case SuccessResult(mapty) =>
          val errRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(TypeError(mapty, MapType(ValueType, ValueType))))), store__)
          def lookupOnMap(keyType: RefinementType, valueType: RefinementType, size: Intervals.Positive.Interval): Set[TypeMemories[VoideableRefinementType, Unit]] = {
            val keymems = evalLocal(localVars, store__, ekey, funMemo)
            keymems.memories.flatMap[TypeMemories[VoideableRefinementType, Unit], Set[TypeMemories[VoideableRefinementType, Unit]]] { case TypeMemory(keyres, store_) =>
                keyres match {
                  case SuccessResult(actualVRKeyType) =>
                    val keyTypeEqO = refineEq(actualVRKeyType, VoideableRefinementType(possiblyVoid = false, keyType))
                    val posEx: Set[TypeMemories[VoideableRefinementType, Unit]] = keyTypeEqO.fold(
                      Set(TypeMemories[VoideableRefinementType, Unit](
                        Set(TypeMemory(ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false,
                          DataRefinementType("NoKey", None)))), store_)))))(_ => Set[TypeMemories[VoideableRefinementType, Unit]]())
                    val posSuc: Set[TypeMemories[VoideableRefinementType, Unit]] = keyTypeEqO.fold(Set[TypeMemories[VoideableRefinementType, Unit]]()) { _ =>
                      if (IntegerW.<=(size.ub, 0)) Set()
                      else Set(TypeMemories(Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false, valueType)), store_))))
                    }
                    posEx ++ posSuc
                  case ExceptionalResult(exres) =>
                    Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
                }
            }
          }
          val voidRes: Set[TypeMemories[VoideableRefinementType, Unit]] = if (mapty.possiblyVoid) Set(TypeMemories(Set(errRes))) else Set()
          val tyRes: Set[TypeMemories[VoideableRefinementType, Unit]] = mapty.refinementType match {
            case MapRefinementType(keyType, valueType, size) => lookupOnMap(keyType, valueType, size)
            case ValueRefinementType =>
              Set(TypeMemories[VoideableRefinementType, Unit](Set(errRes))) ++ lookupOnMap(ValueRefinementType, ValueRefinementType, Lattice[Intervals.Positive.Interval].top)
            case _ =>
              Set(TypeMemories[VoideableRefinementType, Unit](Set(errRes)))
          }
          voidRes ++ tyRes
        case ExceptionalResult(exres) =>
          Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
      }
    })
  }

  def evalMapUpdate(localVars: Map[VarName, Type], store: TypeStore, emap: Expr, ekey: Expr, evl: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val mapmems = evalLocal(localVars, store, emap, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(mapmems.memories.flatMap { case TypeMemory(mapres, store___) =>
      mapres match {
        case SuccessResult(mapty) =>
          def updateOnMap(keyType: RefinementType, valueType: RefinementType, size: Intervals.Positive.Interval): Set[TypeMemories[VoideableRefinementType, Unit]] = {
            val keymems = evalLocal(localVars, store___, ekey, funMemo)
            keymems.memories.flatMap { case TypeMemory(keyres, store__) =>
              keyres match {
                case SuccessResult(keyvrt) =>
                  val keyVoidRes: Set[TypeMemories[VoideableRefinementType, Unit]] =
                    if (keyvrt.possiblyVoid)
                      Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store__))))
                    else Set()
                  val keyTypeRes: Set[TypeMemories[VoideableRefinementType, Unit]] = {
                    val valmems = evalLocal(localVars, store__, evl, funMemo)
                    valmems.memories.flatMap { case TypeMemory(valres, store_) =>
                      valres match {
                        case SuccessResult(valvrt) =>
                          val valVoidRes: Set[TypeMemories[VoideableRefinementType, Unit]] =
                            if (valvrt.possiblyVoid)
                              Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store__))))
                            else Set()
                          val valTypeRes: Set[TypeMemories[VoideableRefinementType, Unit]] = {
                            val keylub = Lattice[RefinementType].lub(keyvrt.refinementType, keyType)
                            val vallub = Lattice[RefinementType].lub(valvrt.refinementType, valueType)
                            Set(TypeMemories[VoideableRefinementType, Unit](
                              Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false,
                                MapRefinementType(keylub, vallub, Intervals.Positive.makeInterval(size.lb, IntegerW.+(size.ub, 1))))), store_))))
                          }
                          valVoidRes ++ valTypeRes
                        case ExceptionalResult(exres) =>
                          Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
                      }
                    }
                  }
                  keyVoidRes ++ keyTypeRes
                case ExceptionalResult(exres) =>
                  Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
              }
            }
          }
          val errRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(TypeError(mapty, MapType(ValueType, ValueType))))), store___)
          val voidRes: Set[TypeMemories[VoideableRefinementType, Unit]] = if (mapty.possiblyVoid) Set(TypeMemories(Set(errRes))) else Set()
          val typRes: Set[TypeMemories[VoideableRefinementType, Unit]] = mapty.refinementType match {
            case MapRefinementType(keyType, valueType, size) => updateOnMap(keyType, valueType, size)
            case ValueRefinementType => Set(TypeMemories[VoideableRefinementType, Unit](Set(errRes))) ++ updateOnMap(ValueRefinementType, ValueRefinementType, Lattice[Intervals.Positive.Interval].top)
            case _ => Set(TypeMemories(Set(errRes)))
          }
          voidRes ++ typRes
        case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store___))))
      }
    })
  }

  /*
  A memoization strategy must be chosen such that it satifies two conditions:
  1: The result is sound
  2: The procedure terminates

  In order to satisfy (1) we must ensure that the resulting output on recursion is always larger than the result from the provided
   input, and to satisfy (2) we must choose a way to conflate the traces based on input.

   Conflating traces of input can happen according to the following strategies:
   S1: Conflate all recursions to the same syntactic judgement
   S2: Conflate recursions to the same syntactic judgement according to some partitioning
   S3: Conflate recursions to the same or larger previous input (works if the input domain is finite)

   S1 is too unprecise in practice, so S2-S4 are preferable.

   In both the cases S1 and S2, we need to widen the current input with the closest previous input to the same judgment in order to get a sound result (otherwise
   the recursion is potentially not monotone).

   If the input domain is not finite, one could also do a further abstraction to the input to a new finite domain and use strategy S3, but this might also lose precision.
   */
  lazy val evalFunCall:
    (Map[VarName, Type], TypeStore, VarName, Seq[Expr], FunMemo) => TypeMemories[VoideableRefinementType, Unit] =
   memoized[Map[VarName, Type], TypeStore, VarName, Seq[Expr], FunMemo,TypeMemories[VoideableRefinementType, Unit]](memocacheSize) {
     (localVars, store, functionName, args, funMemo) =>
      def memoFix(argtys: List[VoideableRefinementType], store: TypeStore): TypeMemories[VoideableRefinementType, Unit] = {
        val (funresty, funpars, funbody) = module.funs(functionName)
        val argpartyps = argtys.zip(funpars.map(_.typ))
        def go(argtys: List[VoideableRefinementType], callstore: TypeStore, prevRes: TypeMemories[VoideableRefinementType, Unit], reccount: Int): TypeMemories[VoideableRefinementType, Unit] = {
          if (functionName == "compile")
            logger.debug(
              s"""
                 | call: $functionName(${argtys.mkString(", ")})
                 | store: ${TypeStore.pretty(callstore)}
               """.stripMargin)
          val memoKey = functionName -> argtys.map(at => atyping.inferType(at.refinementType))
          val newFunMemo: FunMemo = funMemo.updated(memoKey, ((argtys, callstore), prevRes))
          val newRes = funbody match {
            case ExprFunBody(exprfunbody) =>
              evalLocal(funpars.map(par => par.name -> par.typ).toMap, callstore, exprfunbody, newFunMemo)
            case PrimitiveFunBody =>
              functionName match {
                case "delete" =>
                  val mapvrty = getVar(callstore, "emap").get
                  val keyvrty = getVar(callstore, "ekey").get
                  val errRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(OtherError))), callstore)
                  val voidRes =
                    if (mapvrty.possiblyVoid || keyvrty.possiblyVoid) Set(errRes)
                    else Set[TypeMemory[VoideableRefinementType, Unit]]()
                  val typRes = {
                    mapvrty.refinementType match {
                      case MapRefinementType(kty, vty, size) =>
                        Set(TypeMemory[VoideableRefinementType, Unit](SuccessResult(VoideableRefinementType(possiblyVoid = false,
                          MapRefinementType(kty, vty, Intervals.Positive.makeInterval(IntegerW.-(size.lb, 1), size.ub)))), callstore))
                      case _ => Set(errRes)
                    }
                  }
                  TypeMemories(voidRes ++ typRes)
                case "toString" =>
                  val _ = getVar(callstore, "earg").get
                  TypeMemories[VoideableRefinementType, Unit](
                    Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType))), callstore)))
                case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), callstore)))
              }
          }
          if (Lattice[TypeMemories[VoideableRefinementType, Unit]].<=(newRes, prevRes))
            newRes
          else {
            val widened = Lattice[TypeMemories[VoideableRefinementType, Unit]].widen(prevRes, newRes)
            go(argtys, callstore, widened, reccount = reccount + 1)
          }
        }
        val posEx: TypeMemories[VoideableRefinementType, Unit] = {
          val errRes = TypeMemory[VoideableRefinementType, Unit](
            ExceptionalResult(Error(Set(SignatureMismatch(functionName, argtys, funpars.map(_.typ))))), store)
          if (argtys.lengthCompare(funpars.length) != 0 ||
            argpartyps.exists { case (avrty, party) => atyping.checkType(avrty.refinementType, party).contains(false) })
            TypeMemories[VoideableRefinementType, Unit](Set(errRes))
          else Lattice[TypeMemories[VoideableRefinementType, Unit]].bot
        }
        val posSuc: TypeMemories[VoideableRefinementType, Unit] = {
          if (argtys.lengthCompare(funpars.length) == 0 &&
              argpartyps.forall { case (avrty, party) => atyping.checkType(avrty.refinementType, party).contains(true) }) {
            val callstore = TypeStoreV(module.globalVars.map { case (x, _) => x -> getVar(store, x).get } ++
                              funpars.map(_.name).zip(argtys).toMap)
            funMemo.get(functionName -> argtys.map(at => atyping.inferType(at.refinementType)))
              .fold {
                _memoMissesCount.set(_memoMissesCount.get + 1)
                if (functionName == "compile")
                  logger.debug(
                    s"""
                       | miss
                     """.stripMargin)
                go(argtys, callstore, Lattice[TypeMemories[VoideableRefinementType, Unit]].bot, reccount = 0)
              } { case ((prevargtys, prevstore), prevres) =>
              val paapairs = prevargtys.zip(argtys)
              val allLess = paapairs.forall { case (praty, aty) => Lattice[VoideableRefinementType].<=(aty, praty) }
              val storeLess = Lattice[TypeStore].<=(callstore, prevstore)
              val memores =
                if (allLess && storeLess) {
                  _memoHitsCount.set(_memoHitsCount.get + 1)
                  if (functionName == "compile")
                    logger.debug(
                      s"""
                        | hit
                        | mem: ${TypeMemories.pretty(prevres)}
                        | result: $prevres
                      """.stripMargin)
                 prevres
                }
                else {
                  // Widen current input with previous input (strategy S2)
                  _memoWideningCount.set(_memoWideningCount.get + 1)
                  val newargtys = paapairs.foldLeft(List[VoideableRefinementType]()) { (prevargtys, paap) =>
                    val (praty, aty) = paap
                    val paapwid = Lattice[VoideableRefinementType].widen(praty, aty)
                    prevargtys :+ paapwid
                  }
                  val newstore = Lattice[TypeStore].widen(prevstore, callstore)
                  if (functionName == "compile")
                    logger.debug(s"""
                       | widen
                       | widened args: ${newargtys.mkString(", ")}
                       | wiedened store: ${TypeStore.pretty(newstore)}
                     """.stripMargin)
                  go(newargtys, newstore, Lattice[TypeMemories[VoideableRefinementType, Unit]].bot, reccount = 0)
                }
              memores
            }
          }
          else Lattice[TypeMemories[VoideableRefinementType, Unit]].bot
        }
        val callres = Lattice[TypeMemories[VoideableRefinementType, Unit]].lub(posEx, posSuc)
        Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(callres.memories.map { case TypeMemory(res, resstore) =>
          val store_ = joinStores(store, TypeStoreV(module.globalVars.map { case (x, _) => x -> getVar(resstore, x).get }))

          def funcallsuccess(resvrtyp: VoideableRefinementType): TypeMemories[VoideableRefinementType, Unit] = {
            val errRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(TypeError(resvrtyp, funresty)))), store_)
            val posEx =
              if (atyping.checkType(resvrtyp.refinementType, funresty).contains(false)) TypeMemories[VoideableRefinementType, Unit](Set(errRes))
              else Lattice[TypeMemories[VoideableRefinementType, Unit]].bot
            val posSuc =
              if (atyping.checkType(resvrtyp.refinementType, funresty).contains(true)) {
                TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(resvrtyp), store_)))
              } else Lattice[TypeMemories[VoideableRefinementType, Unit]].bot
            Lattice[TypeMemories[VoideableRefinementType, Unit]].lub(posEx, posSuc)
          }

          res match {
            case SuccessResult(restyp) => funcallsuccess(restyp)
            case ExceptionalResult(exres) =>
              exres match {
                case Return(restyp) => funcallsuccess(restyp)
                case Break | Continue | Fail(_) =>
                  TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Error(Set(EscapedControlOperator))), store_)))
                case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_)))
              }
          }
        })
    }
    val argmems = evalLocalAll(localVars, store, args, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(argmems.memories.map { case TypeMemory(argres, store__) =>
      argres match {
        case SuccessResult(argtys) =>
          memoFix(argtys, store__)
        case ExceptionalResult(exres) => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__)))
      }
    })
  }

  def evalReturn(localVars: Map[VarName, Type], store: TypeStore, evl: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val valmems = evalLocal(localVars, store, evl, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(valmems.memories.flatMap { case TypeMemory(valres, store_) =>
      valres match {
        case SuccessResult(valty) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Return(valty)), store_))))
        case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
      }
    })
  }

  def evalAssignable(localVars: Map[VarName, Type], store: TypeStore, assgn: Assignable, funMemo: FunMemo): TypeMemories[DataPath[VoideableRefinementType], Unit] = {
    assgn match {
      case VarAssgn(name) => TypeMemories(Set(TypeMemory(SuccessResult(DataPath(name, List())),store)))
      case FieldAccAssgn(target, fieldName) =>
        val targetmems = evalAssignable(localVars, store, target, funMemo)
        val flatmems = Lattice[TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit]].lubs(
          targetmems.memories.flatMap[TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit], Set[TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit]]] {
          case TypeMemory(targetres, store_) =>
            targetres match {
              case SuccessResult(DataPath(vn, accessPaths)) =>
                Set(TypeMemories(Set(TypeMemory(SuccessResult(FlatValue(DataPath(vn, accessPaths :+ FieldAccessPath(fieldName)))), store_))))
              case ExceptionalResult(exres) =>
                Set(TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
            }
        })
        unflatMems(flatmems)
      case MapUpdAssgn(target, ekey) =>
        val targetmems = evalAssignable(localVars, store, target, funMemo)
        val flatmems = Lattice[TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit]].lubs(
          targetmems.memories.flatMap[TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit], Set[TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit]]] {
          case TypeMemory(targetres, store__) =>
            targetres match {
              case SuccessResult(DataPath(vn, accessPaths)) =>
                val keymems = evalLocal(localVars, store__, ekey, funMemo)
                Set(TypeMemories(keymems.memories.map { case TypeMemory(keyres, store_) =>
                  keyres match {
                    case SuccessResult(keyt) =>
                      TypeMemory[Flat[DataPath[VoideableRefinementType]], Unit](SuccessResult(FlatValue(DataPath(vn, accessPaths :+ MapAccessPath(keyt)))), store_)
                    case ExceptionalResult(exres) => TypeMemory[Flat[DataPath[VoideableRefinementType]], Unit](ExceptionalResult(exres), store_)
                  }
                }))
              case ExceptionalResult(exres) =>
                Set(TypeMemories[Flat[DataPath[VoideableRefinementType]], Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
            }
        })
        unflatMems(flatmems)
    }
  }

  def updatePath(rotyp: RefinementType, paths: List[AccessPath[VoideableRefinementType]], vrttyp: VoideableRefinementType): Set[TypeResult[VoideableRefinementType, Unit]] = paths match {
    case Nil => Set(SuccessResult(vrttyp))
    case path :: rpaths =>
      path match {
        case MapAccessPath(vrktyp) =>
          def updateOnMap(keyType: RefinementType, valueType: RefinementType, size: Intervals.Positive.Interval): Set[TypeResult[VoideableRefinementType, Unit]] = {
            if (rpaths.isEmpty) {
              val keytlub = Lattice[RefinementType].lub(keyType, vrktyp.refinementType)
              val vtlub = Lattice[RefinementType].lub(valueType, vrttyp.refinementType)
              Set[TypeResult[VoideableRefinementType, Unit]](
                SuccessResult(VoideableRefinementType(possiblyVoid = false, MapRefinementType(keytlub, vtlub, size))))
            } else {
              val exRes: Set[TypeResult[VoideableRefinementType, Unit]] =
                Set(ExceptionalResult(Throw(VoideableRefinementType(possiblyVoid = false, DataRefinementType("NoKey", None)))))
              val keyeqres = refineEq(vrktyp, VoideableRefinementType(possiblyVoid = false, keyType))
              keyeqres.fold(exRes) { _ =>
                exRes ++ updatePath(valueType, rpaths, vrttyp).flatMap {
                  case SuccessResult(nvaltyp) =>
                    // We only support weak updates on maps
                    val valtylub =
                      Lattice[VoideableRefinementType].lub(VoideableRefinementType(possiblyVoid = false, valueType), nvaltyp)
                    Set[TypeResult[VoideableRefinementType, Unit]](
                      SuccessResult(VoideableRefinementType(possiblyVoid = false, MapRefinementType(keyType, valtylub.refinementType, size))))
                  case ExceptionalResult(exres) =>
                    Set[TypeResult[VoideableRefinementType, Unit]](ExceptionalResult(exres))
                }
              }
            }
          }
          val exRes: TypeResult[VoideableRefinementType, Unit] =
            ExceptionalResult(Error(Set(TypeError(rotyp, MapType(atyping.inferType(vrktyp.refinementType), atyping.inferType(vrttyp.refinementType))))))
          val voidRes: Set[TypeResult[VoideableRefinementType, Unit]] =
              if (vrttyp.possiblyVoid) Set(ExceptionalResult(Error(Set(OtherError)))) else Set()
          val typRes: Set[TypeResult[VoideableRefinementType, Unit]] = {
            rotyp match {
              case MapRefinementType(keyType, valueType, size) => updateOnMap(keyType, valueType, size) // map update preserves size
              case ValueRefinementType => Set(exRes) ++ updateOnMap(ValueRefinementType, ValueRefinementType, Lattice[Intervals.Positive.Interval].top)
              case _ => Set(exRes)
            }
          }
          voidRes ++ typRes
        case FieldAccessPath(fieldName) =>
          def updateFieldOnType(dtname: TypeName, refinenameopt: Option[Refinement]): Set[TypeResult[VoideableRefinementType, Unit]] = {
            val refinementDef = refinenameopt.fold(dataTypeDefToRefinementDef(dtname, typememoriesops.datatypes(dtname)))(refinements.definitions)
            refinementDef.conss.toSet[(ConsName, List[RefinementType])].flatMap[TypeResult[VoideableRefinementType, Unit], Set[TypeResult[VoideableRefinementType, Unit]]] { case (cons, chrtys) =>
              val (_, pars) = module.constructors(cons)
              val index = pars.indexWhere(_.name == fieldName)
              if (index < 0) { Set(ExceptionalResult(Error(Set(FieldError(rotyp, fieldName))))) }
              else {
                updatePath(chrtys(index), rpaths, vrttyp).flatMap[TypeResult[VoideableRefinementType, Unit], Set[TypeResult[VoideableRefinementType, Unit]]] {
                  case SuccessResult(ntyp) =>
                    val posEx: Set[TypeResult[VoideableRefinementType, Unit]] = {
                      if (atyping.checkType(ntyp.refinementType, pars(index).typ).contains(false))
                        Set(ExceptionalResult(Error(Set(TypeError(ntyp, pars(index).typ)))))
                      else Set()
                    }
                    val posSuc: Set[TypeResult[VoideableRefinementType, Unit]] = {
                      if (atyping.checkType(ntyp.refinementType, pars(index).typ).contains(true)) {
                        val voidRes: Set[TypeResult[VoideableRefinementType, Unit]] =
                          if (ntyp.possiblyVoid) Set(ExceptionalResult(Error(Set(OtherError)))) else Set()
                        val newRn = refinements.newRefinement(dtname)
                        val newrhs = Map(cons -> chrtys.updated(index, ntyp.refinementType))
                        val nrno = addRefinement(dtname, newRn, newrhs)
                        val posRes: Set[TypeResult[VoideableRefinementType, Unit]] =
                          Set(SuccessResult(VoideableRefinementType(possiblyVoid = false, DataRefinementType(dtname, nrno))))
                        voidRes ++ posRes
                      } else Set()
                    }
                    posEx ++ posSuc
                  case ExceptionalResult(exres) => Set(ExceptionalResult(exres))
                }
              }
            }
          }
          val exRes: TypeResult[VoideableRefinementType, Unit] = ExceptionalResult(Error(Set(FieldError(rotyp, fieldName))))
          val voidRes: Set[TypeResult[VoideableRefinementType, Unit]] =
              if (vrttyp.possiblyVoid) Set(ExceptionalResult(Error(Set(OtherError)))) else Set()
          val tyRes: Set[TypeResult[VoideableRefinementType, Unit]] = {
            rotyp match {
              case DataRefinementType(dn, rno) => updateFieldOnType(dn, rno)
              case ValueRefinementType =>
                Set(ExceptionalResult(Error(Set(FieldError(rotyp, fieldName))))) ++ module.datatypes.keySet.filter { dt =>
                  module.datatypes(dt).exists { cons =>
                    val (_, pars) = module.constructors(cons)
                    pars.exists(_.name == fieldName)
                  }
                }.flatMap(dn => updateFieldOnType(dn, None))
              case _ => Set(exRes)
            }
          }
          voidRes ++ tyRes
      }
  }

  def evalAssign(localVars: Map[VarName, Type], store: TypeStore, assgn: Assignable, targetexpr: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val assignablemems = evalAssignable(localVars, store, assgn, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(assignablemems.memories.flatMap { case TypeMemory(assgnres, store__) =>
        assgnres match {
          case SuccessResult(path) =>
            val targetmems = evalLocal(localVars, store__, targetexpr, funMemo)
            Set(Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(targetmems.memories.flatMap{ case TypeMemory(targetres, store_) =>
              targetres match {
                case SuccessResult(typ) =>
                  val newTypRes: Set[TypeResult[VoideableRefinementType, Unit]] =
                    if (path.accessPaths.isEmpty) {
                      Set(SuccessResult(typ))
                    } else {
                      getVar(store_, path.varName).fold[Set[TypeResult[VoideableRefinementType, Unit]]](
                        Set(ExceptionalResult(Error(Set(UnassignedVarError(path.varName)))))
                      ) {
                        case VoideableRefinementType(possUnassigned, otyp) =>
                          (if (possUnassigned)
                            Set(ExceptionalResult(Error(Set(UnassignedVarError(path.varName)))))
                          else Set()) ++ updatePath(otyp, path.accessPaths, typ)
                      }
                    }
                  newTypRes.flatMap {
                    case SuccessResult(newvrt) =>
                      // TODO provide internal error instead of exception from math lookup of unknown field
                      val staticVarTy = if (localVars.contains(path.varName)) localVars(path.varName) else module.globalVars(path.varName)
                      val exRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(TypeError(newvrt, staticVarTy)))), store_)
                      val posEx: Set[TypeMemories[VoideableRefinementType, Unit]] =
                        if (atyping.checkType(newvrt.refinementType, staticVarTy).contains(false)) Set(TypeMemories(Set(exRes)))
                        else Set()
                      val posSuc: Set[TypeMemories[VoideableRefinementType, Unit]] =
                        if (atyping.checkType(newvrt.refinementType, staticVarTy).contains(true)) {
                          Set(TypeMemories(Set(TypeMemory(SuccessResult(newvrt), setVar(store_, path.varName, newvrt)))))
                        } else Set()
                      posEx ++ posSuc
                    case ExceptionalResult(exres) =>
                      Set(TypeMemories(Set(TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(exres), store_))))
                  }
                case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
              }
            }))
          case ExceptionalResult(exres) =>
            Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
        }
    })
  }

  def evalIf(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, thenB: Expr, elseB: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val condmems = evalLocal(localVars, store, cond, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(condmems.memories.flatMap { case TypeMemory(condres, store__) =>
      condres match {
        case SuccessResult(condvrty) =>
          val exRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(TypeError(condvrty, DataType("Bool"))))), store__)
          def sucRes(refinenameopt: Option[Refinement]): TypeMemories[VoideableRefinementType, Unit] = {
            val refinementDef = refinenameopt.fold(dataTypeDefToRefinementDef("Bool",typememoriesops.datatypes("Bool")))(refinements.definitions)
            Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(refinementDef.conss.keySet.map {
              case "true" => evalLocal(localVars, store__, thenB, funMemo)
              case "false" => evalLocal(localVars, store__, elseB, funMemo)
              case _ => throw NonNormalFormMemories
            })
          }
          val voidRes: Set[TypeMemories[VoideableRefinementType, Unit]] =
            if (condvrty.possiblyVoid) Set(TypeMemories(Set(exRes))) else Set()
          val tyRes: Set[TypeMemories[VoideableRefinementType, Unit]] = {
            condvrty.refinementType match {
              case DataRefinementType("Bool", rno) => Set(sucRes(rno))
              case ValueRefinementType => Set(TypeMemories(Set(exRes)), sucRes(None))
              case _ => Set(TypeMemories(Set(exRes)))
            }
          }
          voidRes ++ tyRes
        case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store))))
      }
    })
  }

  def evalCases(localVars: Map[VarName, Type], store: TypeStore, scrtyp: VoideableRefinementType, cases: List[Case], funMemo: FunMemo): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
    def evalCase(store: TypeStore, action: Expr, envs: Set[Map[VarName, VoideableRefinementType]]): TypeMemories[VoideableRefinementType, Unit] = {
      envs.headOption.fold(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Fail(())), store)))) { env =>
        val joinedstore = joinStores(store, TypeStoreV(env))
        val actmems = evalLocal(localVars, joinedstore, action, funMemo)
        val actress = actmems.memories.map { case TypeMemory(actres, store_) =>
          actres match {
            case ExceptionalResult(Fail(())) => evalCase(store, action, envs.tail)
            case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(actres, dropVars(store_, env.keySet))))
          }
        }
        Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(actress)
      }
    }
    val casesres: TypeMemories[VoideableRefinementType, VoideableRefinementType] = cases match {
      case Nil => TypeMemories(Set(TypeMemory(ExceptionalResult(Fail(scrtyp)), store)))
      case Case(cspatt, csaction) :: css =>
        val envss = matchPatt(store, scrtyp, cspatt)
        val resmems = envss.map { case (refinestore, refinescrtyp, envs) =>
          val newstore = if (refinedMatching) refinestore else store
          val newscrtyp = if (refinedMatching) refinescrtyp else scrtyp
          val casemems: TypeMemories[VoideableRefinementType, Unit] = evalCase(newstore, csaction, envs)
          val resmems = casemems.memories.map { case TypeMemory(cres, store_) =>
            cres match {
              case ExceptionalResult(Fail(())) => evalCases(localVars, newstore, newscrtyp, css, funMemo)
              case _ => TypeMemories[VoideableRefinementType, VoideableRefinementType](
                Set(TypeMemory(cres.asInstanceOf[TypeResult[VoideableRefinementType, Nothing]], store_)))// Cast should be safe
            }
          }
          Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(resmems)
        }
        val resmemslub = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(resmems)
        resmemslub
    }
    casesres
  }

  def evalSwitch(localVars: Map[VarName, Type], store: TypeStore, scrutinee: Expr, cases: Seq[Case], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val scrmems = evalLocal(localVars, store, scrutinee, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(scrmems.memories.flatMap { case TypeMemory(scrres, store__) =>
        scrres match {
          case SuccessResult(scrval) =>
            val casemems = evalCases(localVars, store__, scrval, cases.toList, funMemo)
            Set(Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(casemems.memories.map { case TypeMemory(caseres, store_) =>
                caseres match {
                  case SuccessResult(caseval) =>
                    TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(caseval), store_)))
                  case ExceptionalResult(exres) =>
                    exres match {
                      case Fail(_) =>
                        TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store_)))
                      case _ => TypeMemories[VoideableRefinementType, Unit](
                        Set(TypeMemory(ExceptionalResult(exres).asInstanceOf[TypeResult[Nothing, Nothing]], store_))) // Cast should be safe
                    }
                }
            }))
          case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
        }
    })
  }

  def memoVisitKey(rtyp: VoideableRefinementType): Any = {
    memoWidening match {
      case SimpleWidening => ()
      case TypeWidening => atyping.inferType(rtyp.refinementType)
      case ConstructorWidening(depth) => cutAt(rtyp.refinementType, depth)
    }
  }

  def combineVals(ctyres: TypeResult[VoideableRefinementType, VoideableRefinementType],
                  ctysres: TypeResult[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]): TypeResult[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
    ctyres match {
      case ExceptionalResult(Fail(cty)) =>
        ctysres match {
          case ExceptionalResult(Fail(ctys)) => ExceptionalResult(Fail(RefinementChildren.makeCons(cty, ctys)))
          case SuccessResult(ctys2) => SuccessResult(RefinementChildren.makeCons(cty, ctys2))
          case _ => throw new UnsupportedOperationException
        }
      case SuccessResult(cty2) =>
        ctysres match {
          case ExceptionalResult(Fail(ctys)) => SuccessResult(RefinementChildren.makeCons(cty2, ctys))
          case SuccessResult(ctys2) => SuccessResult(RefinementChildren.makeCons(cty2, ctys2))
          case _ => throw new UnsupportedOperationException
        }
      case _ =>  throw new UnsupportedOperationException
    }
  }

  private
  def evalTDAll(localVars: Map[VarName, Type], break: Boolean, cases: List[Case], funMemo: FunMemo, cs: RefinementChildren[RefinementType], store: TypeStore, memo: VMemo): TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
    def memoFixAll(cs: RefinementChildren[RefinementType], store: TypeStore, memoall: VMemoAll): TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
      @tailrec
      def go(cs: RefinementChildren[RefinementType], store: TypeStore, prevRes: TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]): TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
        val nilRes: Option[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]] = {
          if (getNil(cs))
            Some(TypeMemories(Set(TypeMemory(ExceptionalResult(Fail(makeNil(cs).map(VoideableRefinementType(possiblyVoid = false, _)))), store))))
          else None
        }
        val consRes: Option[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]] = {
          getCons(cs).map { case (crty, crtys) =>
            val ctymems = evalTDMemoFix(localVars, break, cases, funMemo, VoideableRefinementType(possiblyVoid = false, crty), store, memo)
            val resmems = Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].lubs(ctymems.memories.map {
              case TypeMemory(ctyres, store__) =>
                def evalRest: TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
                  Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].lubs {
                    val newmemoall = if (!cs.isFixed) memoall.updated(cs, (store, prevRes)) else memoall
                    val ctysmems = memoFixAll(crtys, store__, newmemoall)
                    ctysmems.memories.map { case TypeMemory(ctysres, store_) =>
                      ctysres match {
                        case SuccessResult(_) | ExceptionalResult(Fail(_)) =>
                          val combineres = combineVals(ctyres, ctysres)
                          TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(combineres, store_)))
                        case ExceptionalResult(exres) =>
                          TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(ExceptionalResult(exres), store_)))
                      }
                    }
                  }
                }
                ctyres match {
                  case SuccessResult(cty_) =>
                    if (break)
                      TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](
                        Set(TypeMemory(SuccessResult(makeCons(cty_, crtys.map(VoideableRefinementType(possiblyVoid = false, _)))), store__)))
                    else evalRest
                  case ExceptionalResult(Fail(_)) => evalRest
                  case ExceptionalResult(exres) =>
                    TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](
                      Set(TypeMemory(ExceptionalResult(exres).asInstanceOf[TypeResult[Nothing, Nothing]], store__)))
                }
            })
            resmems
          }
        }
        val newRes = Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].lubs(nilRes.toSet ++ consRes.toSet)
        if (!cs.isFixed) {
          if (Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].<=(newRes, prevRes)) newRes
          else {
            val widened = Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].widen(prevRes, newRes)
            go(cs, store, widened)
          }
        } else {
          newRes
        }
      }
      memoall.get(cs).fold(go(cs, store, Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].bot)) {
        case (prevstore, prevres) =>
          if (Lattice[TypeStore].<=(store, prevstore)) prevres
          else {
            val storewid = Lattice[TypeStore].widen(prevstore, store)
            go(cs, storewid, Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].bot)
          }
      }
    }
    memoFixAll(cs, store, Map())
  }

  @tailrec
  private final
  def evalTDMemoFixGo(localVars: Map[VarName, Type], break: Boolean, cases: List[Case], funMemo: FunMemo, scrtyp: VoideableRefinementType, store: TypeStore, prevRes: TypeMemories[VoideableRefinementType, VoideableRefinementType], memo: VMemo): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
    val scmems = evalCases(localVars, store, scrtyp, cases, funMemo)
    val newRes = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(scmems.memories.map { case TypeMemory(scres, store__) =>
      def evalRest(scres: TypeResult[VoideableRefinementType, VoideableRefinementType]): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
        val ty = ifFail(scres)
        val res = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(children(ty).map { case (nnrtyp, ctys) =>
          val chres = evalTDAll(localVars, break, cases, funMemo, ctys, store__, memo.updated(memoVisitKey(scrtyp), ((scrtyp, store), prevRes)))
          Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(chres.memories.map { case TypeMemory(ctysres, store_) =>
            ctysres match {
              case SuccessResult(ctys2) =>
                TypeMemories[VoideableRefinementType, VoideableRefinementType](
                  reconstruct(nnrtyp, ctys2).map(TypeMemory[VoideableRefinementType, VoideableRefinementType](_, store_)))
              case ExceptionalResult(Fail(failrestys)) =>
                val newscres = scres match {
                  case SuccessResult(_) => SuccessResult(safeReconstruct(nnrtyp, failrestys))
                  case ExceptionalResult(Fail(_)) => ExceptionalResult(Fail(safeReconstruct(nnrtyp, failrestys)))
                  case ExceptionalResult(exres) => ExceptionalResult(exres)
                }
                TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(newscres, store_)))
              case ExceptionalResult(exres) =>
                TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(ExceptionalResult(exres).asInstanceOf[TypeResult[Nothing, Nothing]], store_)))
            }
          })
        })
        res
      }
      scres match {
        case SuccessResult(ty) =>
          if (break)
            TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(SuccessResult(ty), store__)))
          else evalRest(scres)
        case ExceptionalResult(Fail(_)) => evalRest(scres)
        case ExceptionalResult(exres) =>
          TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(ExceptionalResult(exres), store__)))
      }
    })
    if (Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].<=(newRes, prevRes)) newRes
    else {
      val widened = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].widen(prevRes, newRes)
      evalTDMemoFixGo(localVars, break, cases, funMemo, scrtyp, store, widened, memo)
    }
  }

  private
  lazy val evalTDMemoFix: (Map[VarName, Type], Boolean, List[Case], FunMemo, VoideableRefinementType, TypeStore, VMemo) => TypeMemories[VoideableRefinementType, VoideableRefinementType] =
    memoized[Map[VarName, Type], Boolean, List[Case], FunMemo, VoideableRefinementType, TypeStore, VMemo, TypeMemories[VoideableRefinementType, VoideableRefinementType]](memocacheSize) { (localVars, break, cases, funMemo, scrtyp, store, memo) =>
      memo.get(memoVisitKey(scrtyp)).fold {
        _memoMissesCount.set(_memoMissesCount.get + 1)
        evalTDMemoFixGo(localVars, break, cases, funMemo, scrtyp, store, Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].bot, memo)
      } { case ((prevscrtyp, prevstore), prevres) =>
        if (Lattice[VoideableRefinementType].<=(scrtyp, prevscrtyp)) {
          _memoHitsCount.set(_memoHitsCount.get + 1)
          prevres
        }
        else {
          val scrtypwid = Lattice[VoideableRefinementType].widen(prevscrtyp, scrtyp)
          val storewid = Lattice[TypeStore].widen(prevstore, store)
          _memoWideningCount.set(_memoWideningCount.get + 1)
          evalTDMemoFixGo(localVars, break, cases, funMemo, scrtypwid, storewid, Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].bot, memo)
      }
    }
  }

  def evalTD(localVars: Map[VarName, Type], store: TypeStore, scrtyp: VoideableRefinementType, cases: List[Case], break: Boolean, funMemo: FunMemo): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
    evalTDMemoFix(localVars, break, cases, funMemo, scrtyp, store, Map())
  }

  private
  def evalBUAll(localVars: Map[VarName, Type], break: Boolean, cases: List[Case], funMemo: FunMemo, cs: RefinementChildren[RefinementType], store: TypeStore, memo: VMemo): TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
    def memoFixAll(cs: RefinementChildren[RefinementType], store: TypeStore, memoall: VMemoAll): TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
      @tailrec
      def go(cs: RefinementChildren[RefinementType], store: TypeStore, prevRes: TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]): TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
        val nilRes: Option[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]] = {
          if (getNil(cs))
            Some(TypeMemories(Set(TypeMemory(
              ExceptionalResult(Fail(makeNil(cs).map(VoideableRefinementType(possiblyVoid = false, _)))), store))))
          else None
        }
        val consRes: Option[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]] = {
          getCons(cs).map { case (crty, crtys) =>
            val crtymems = evalBUMemoFix(localVars, break, cases, funMemo, store, VoideableRefinementType(possiblyVoid = false, crty), memo)
            val resmems = Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].lubs(crtymems.memories.map {
              case TypeMemory(crtyres, store__) =>
                def evalRest:
                TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]] = {
                  val newmemoall = if (!cs.isFixed) memoall.updated(cs, (store, prevRes)) else memoall
                  val chres = memoFixAll(crtys, store__, newmemoall)
                  Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].lubs(chres.memories.map {
                    case TypeMemory(crtysres, store_) =>
                      crtysres match {
                        case SuccessResult(_) =>
                          val combineres = combineVals(crtyres, crtysres)
                          TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(combineres, store_)))
                        case ExceptionalResult(Fail(_)) =>
                          val combineres = combineVals(crtyres, crtysres)
                          TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(combineres, store_)))
                        case ExceptionalResult(exres) =>
                          TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(ExceptionalResult(exres), store_)))
                      }
                  })
                }

                crtyres match {
                  case SuccessResult(crty_) =>
                    if (break)
                      TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(
                        SuccessResult(makeCons(crty_, crtys.map(VoideableRefinementType(possiblyVoid = false, _)))), store__)))
                    else evalRest
                  case ExceptionalResult(Fail(_)) => evalRest
                  case ExceptionalResult(exres) =>
                    TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]](Set(TypeMemory(ExceptionalResult(exres).asInstanceOf[TypeResult[Nothing, Nothing]], store__)))
                }
            })
            resmems
          }
        }
        val newRes = Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].lubs(nilRes.toSet ++ consRes.toSet)
        if (!cs.isFixed) {
          if (Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].<=(newRes, prevRes)) newRes
          else {
            val widened = Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].widen(prevRes, newRes)
            go(cs, store, widened)
          }
        } else newRes
      }
      memoall.get(cs).fold(go(cs, store, Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].bot)) {
        case (prevstore, prevres) =>
          if (Lattice[TypeStore].<=(store, prevstore)) prevres
          else {
            val storewid = Lattice[TypeStore].widen(prevstore, store)
            go(cs, storewid, Lattice[TypeMemories[RefinementChildren[VoideableRefinementType], RefinementChildren[VoideableRefinementType]]].bot)
          }
      }
    }
    memoFixAll(cs, store, Map())
  }

  @tailrec
  private final
  def evalBUMemoFixGo(localVars: Map[VarName, Type], break: Boolean, cases: List[Case], funMemo: FunMemo, scrtyp: VoideableRefinementType, store: TypeStore, prevRes: TypeMemories[VoideableRefinementType, VoideableRefinementType], memo: VMemo): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
    val newRes = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(children(scrtyp).map {
      case (nnrtyp, crtys) =>
        val chrmems = evalBUAll(localVars, break, cases, funMemo, crtys, store, memo.updated(memoVisitKey(scrtyp), ((scrtyp, store), prevRes)))
        Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(chrmems.memories.map {
          case TypeMemory(crtyres, store__) =>
            crtyres match {
              case SuccessResult(crtys2) =>
                if (break) {
                  TypeMemories[VoideableRefinementType, VoideableRefinementType](
                    reconstruct(nnrtyp, crtys2).map(TypeMemory[VoideableRefinementType, VoideableRefinementType](_, store__)))
                } else {
                  Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(reconstruct(nnrtyp, crtys2).map {
                    case SuccessResult(rty) =>
                      val rtyresmems = evalCases(localVars, store__, rty, cases, funMemo)
                      Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(rtyresmems.memories.map {
                        case TypeMemory(rtyres, store_) =>
                          rtyres match {
                            case SuccessResult(vfres) =>
                              TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(SuccessResult(vfres), store_)))
                            case ExceptionalResult(Fail(failresty)) =>
                              TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(SuccessResult(failresty), store_)))
                            case ExceptionalResult(exres) =>
                              TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(ExceptionalResult(exres), store_)))
                          }
                      })
                    case ExceptionalResult(exres) =>
                      TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(ExceptionalResult(exres), store__)))
                  })
                }
              case ExceptionalResult(Fail(failrestys)) =>
                evalCases(localVars, store__, safeReconstruct(nnrtyp, failrestys), cases, funMemo)
              case ExceptionalResult(exres) =>
                TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(ExceptionalResult(exres).asInstanceOf[TypeResult[Nothing, Nothing]], store__)))
            }
        })
    })
    if (Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].<=(newRes, prevRes)) newRes
    else {
      val widened = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].widen(prevRes, newRes)
      evalBUMemoFixGo(localVars, break, cases, funMemo, scrtyp, store, widened, memo)
    }
  }

  private
  lazy val evalBUMemoFix: (Map[VarName, Type], Boolean, List[Case], FunMemo, TypeStore, VoideableRefinementType, VMemo) => TypeMemories[VoideableRefinementType, VoideableRefinementType] =
    memoized[Map[VarName, Type], Boolean, List[Case], FunMemo, TypeStore, VoideableRefinementType, VMemo, TypeMemories[VoideableRefinementType, VoideableRefinementType]] (memocacheSize) { (localVars, break, cases, funMemo, store, scrtyp, memo) =>
      memo.get(memoVisitKey(scrtyp)).fold{
        _memoMissesCount.set(_memoMissesCount.get + 1)
        evalBUMemoFixGo(localVars, break, cases, funMemo, scrtyp, store, Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].bot, memo)
      } { case ((prevscrtyp, prevstore), prevres) =>
        if (Lattice[VoideableRefinementType].<=(scrtyp, prevscrtyp)) {
          _memoHitsCount.set(_memoHitsCount.get + 1)
          prevres
        }
        else {
          val scrtypwid = Lattice[VoideableRefinementType].widen(prevscrtyp, scrtyp)
          val storewid = Lattice[TypeStore].widen(prevstore, store)
          _memoWideningCount.set(_memoWideningCount.get + 1)
          evalBUMemoFixGo(localVars, break, cases, funMemo, scrtypwid, storewid, Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].bot, memo)
        }
      }
    }

  def evalBU(localVars: Map[VarName, Type], store: TypeStore, scrtyp: VoideableRefinementType, cases: List[Case], break: Boolean, funMemo: FunMemo): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
    evalBUMemoFix(localVars, break, cases, funMemo, store, scrtyp, Map())
  }

  def evalVisitStrategy(strategy: Strategy, localVars: Map[VarName, Type], store: TypeStore, scrtyp: VoideableRefinementType, cases: List[Case], funMemo: FunMemo): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
    def loop(store: TypeStore, scrtyp: VoideableRefinementType, evalIn : (Map[VarName, Type], TypeStore, VoideableRefinementType, List[Case], Boolean, FunMemo) => TypeMemories[VoideableRefinementType, VoideableRefinementType]): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
      def memoFix(store: TypeStore, scryp: VoideableRefinementType, memo: Map[TypeStore, TypeMemories[VoideableRefinementType, VoideableRefinementType]]): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
        def go(prevRes: TypeMemories[VoideableRefinementType, VoideableRefinementType]): TypeMemories[VoideableRefinementType, VoideableRefinementType] = {
          val resmems = evalIn(localVars, store, scrtyp, cases, /* break = */ false, funMemo)
          val newRes = Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lubs(resmems.memories.map { case TypeMemory(res, store_) =>
            res match {
              case SuccessResult(resty) =>
                val eqres = refineEq(scrtyp, resty)
                val widenedstore = Lattice[TypeStore].lub(store, store_)
                // TODO Check if not equal as well
                eqres.fold[TypeMemories[VoideableRefinementType, VoideableRefinementType]](memoFix(widenedstore, resty, memo.updated(store, prevRes))) { reseq =>
                  Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].lub(
                    TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(SuccessResult(reseq), store_))),
                    memoFix(widenedstore, resty, memo.updated(store, prevRes)))
                }
              case ExceptionalResult(exres) => TypeMemories[VoideableRefinementType, VoideableRefinementType](Set(TypeMemory(ExceptionalResult(exres), store_)))
            }
          })
          if (Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].<=(newRes, prevRes)) newRes
          else go(Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].widen(prevRes, newRes))
        }
        memo.getOrElse(store, go(Lattice[TypeMemories[VoideableRefinementType, VoideableRefinementType]].bot))
      }
      memoFix(store, scrtyp, Map())
    }
    strategy match {
      case TopDown => evalTD(localVars, store, scrtyp, cases, break = false, funMemo)
      case TopDownBreak => evalTD(localVars, store, scrtyp, cases, break = true, funMemo)
      case BottomUp => evalBU(localVars, store, scrtyp, cases, break = false, funMemo)
      case BottomUpBreak => evalBU(localVars, store, scrtyp, cases, break = true, funMemo)
      case Innermost =>
        loop(store, scrtyp, evalBU)
      case Outermost =>
        loop(store, scrtyp, evalTD)
    }
  }

  def evalVisit(localVars: Map[VarName, Type], store: TypeStore, strategy: Strategy, scrutinee: Expr, cases: Seq[Case], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val scrmems = evalLocal(localVars, store, scrutinee, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(scrmems.memories.map { case TypeMemory(scrres, store__) =>
      scrres match {
        case SuccessResult(scrtyp) =>
          val casemems = evalVisitStrategy(strategy, localVars, store__, scrtyp, cases.toList, funMemo)
          Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(casemems.memories.map { case TypeMemory(caseres, store_) =>
              caseres match {
                case SuccessResult(casetyp) => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(casetyp), store_)))
                case ExceptionalResult(exres) =>
                  exres match {
                    case Fail(failresty) => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(failresty), store_)))
                    case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres).asInstanceOf[TypeResult[Nothing, Nothing]], store_)))
                  }
              }
          })
        case ExceptionalResult(exres) => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__)))
      }
    })
  }

  def evalBlock(localVars: Map[VarName, Type], store: TypeStore, vardefs: Seq[Parameter], exprs: Seq[Expr], funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val localVars_ = localVars ++ vardefs.map(par => par.name -> par.typ)
    val resmems = evalLocalAll(localVars_, store, exprs, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(resmems.memories.map[TypeMemories[VoideableRefinementType, Unit], Set[TypeMemories[VoideableRefinementType, Unit]]] { case TypeMemory(res, store__) =>
        val store_ = dropVars(store__, vardefs.map(_.name).toSet)
        res match {
          case SuccessResult(typs) =>
            TypeMemories(Set(TypeMemory(SuccessResult(typs.lastOption.getOrElse(VoideableRefinementType(possiblyVoid = true, NoRefinementType))), store_)))
          case ExceptionalResult(exres) => TypeMemories(Set(TypeMemory(ExceptionalResult(exres), store_)))
        }
    })
  }

  def evalGenerator(localVars: Map[VarName, Type], store: TypeStore, gen: Generator, funMemo: FunMemo): TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit] = {
    gen match {
      case MatchAssign(patt, target) =>
        val tmems = evalLocal(localVars, store, target, funMemo)
        import Powerset._
        Lattice[TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit]].lubs(tmems.memories.flatMap { case TypeMemory(tres, store_) =>
          tres match {
            case SuccessResult(ttyp) =>
              matchPatt(store_, ttyp, patt).map { case (refinestore, _, envs) =>
                TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit](Set(TypeMemory(SuccessResult(Set(envs)), refinestore)))
              }
            case ExceptionalResult(exres) =>
              Set(TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
          }
        })
      case EnumAssign(varname, target) =>
        val tmems = evalLocal(localVars, store, target, funMemo)
        import Powerset._
        Lattice[TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit]].lubs(
          tmems.memories.flatMap[TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit], Set[TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit]]] {
            case TypeMemory(tres, store_) =>
              tres match {
                case SuccessResult(vrttyp) =>
                  val exRes: TypeMemory[Set[Set[Map[VarName, VoideableRefinementType]]], Unit] =
                    TypeMemory(ExceptionalResult(Error(Set(NotEnumerableError(vrttyp)))), store_)
                  val voidRes: Set[TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit]] =
                    if (vrttyp.possiblyVoid) Set(TypeMemories(Set(exRes))) else Set()
                  val tyRes: Set[TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit]] = {
                    // TODO Take length of pattern matching environments into account
                    vrttyp.refinementType match {
                      case ListRefinementType(elementType, _) =>
                        Set(TypeMemories(Set(TypeMemory(SuccessResult(Set(Set(Map(varname -> VoideableRefinementType(possiblyVoid = false, elementType))))), store_))))
                      case SetRefinementType(elementType, _) =>
                        Set(TypeMemories(Set(TypeMemory(SuccessResult(Set(Set(Map(varname -> VoideableRefinementType(possiblyVoid = false, elementType))))), store_))))
                      case MapRefinementType(keyType, _, _) =>
                        Set(TypeMemories(Set(TypeMemory(SuccessResult(Set(Set(Map(varname -> VoideableRefinementType(possiblyVoid = false, keyType))))), store_))))
                      case  ValueRefinementType =>
                        Set(TypeMemories(Set(exRes,
                          TypeMemory(SuccessResult(Set(Set(Map(varname -> VoideableRefinementType(possiblyVoid = false, ValueRefinementType))))), store_))))
                      case _ =>
                        Set(TypeMemories(Set(exRes)))
                    }
                  }
                  voidRes ++ tyRes
                case ExceptionalResult(exres) =>
                  Set(TypeMemories[Set[Set[Map[VarName, VoideableRefinementType]]], Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
              }
        })
    }
  }

  def evalEach(localVars: Map[VarName, Type], store: TypeStore, envss: Set[Set[Map[VarName, VoideableRefinementType]]], body: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    def evalOnEnv(envs: Set[Map[VarName, VoideableRefinementType]]): TypeMemories[VoideableRefinementType, Unit] = {
      // TODO Find a way to have the go fixedpoint calculation outside the inner memoization/regular tree calculation
      def memoFix(store: TypeStore, memo: Map[TypeStore, TypeMemories[VoideableRefinementType, Unit]]): TypeMemories[VoideableRefinementType, Unit] = {
        def go(prevRes: TypeMemories[VoideableRefinementType, Unit]): TypeMemories[VoideableRefinementType, Unit] = {
          val itermems: TypeMemories[VoideableRefinementType, Unit] = {
            // We overapproximate order, cardinality and content, so we have to try all possible combinations in parallel
            val bodymems = Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(envs.map { env =>
              val joinedStore = joinStores(store, TypeStoreV(env))
              val bodymems1 = evalLocal(localVars, joinedStore, body, funMemo)
              TypeMemories(bodymems1.memories.map {
                case TypeMemory(bodyres, store_) => TypeMemory(bodyres, dropVars(store_, env.keySet))
              })
            })
            Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(bodymems.memories.map { case TypeMemory(bodyres, store_) =>
              bodyres match {
                case SuccessResult(_) =>
                  val widenedstore = Lattice[TypeStore].widen(store, store_)
                  memoFix(widenedstore, memo.updated(store, prevRes))
                case ExceptionalResult(exres) =>
                  exres match {
                    case Break => TypeMemories[VoideableRefinementType, Unit](
                      Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store_)))
                    case Continue =>
                      val widenedstore = Lattice[TypeStore].widen(store, store_)
                      memoFix(widenedstore, memo.updated(store, prevRes))
                    // We have to try everything again because of possible duplicates (although perhaps, it should only be
                    // envs, because it is not possible to change alternative through an iteration
                    case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_)))
                  }
              }
            })
          }
          val newRes = Lattice[TypeMemories[VoideableRefinementType, Unit]].lub(
            TypeMemories[VoideableRefinementType, Unit](
              Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store))), itermems)
          if (Lattice[TypeMemories[VoideableRefinementType, Unit]].<=(newRes, prevRes)) newRes
          else go(Lattice[TypeMemories[VoideableRefinementType, Unit]].widen(prevRes, newRes))
        }
        memo.getOrElse(store, go(Lattice[TypeMemories[VoideableRefinementType, Unit]].bot))
      }
      memoFix(store, Map())
    }
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(envss.map { envs => evalOnEnv(envs) })
  }

  def evalFor(localVars: Map[VarName, Type], store: TypeStore, gen: Generator, body: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val genmems = evalGenerator(localVars, store, gen, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(genmems.memories.flatMap { case TypeMemory(genres, store__) =>
      genres match {
        case SuccessResult(envs) =>
          val bodymems = evalEach(localVars, store__, envs, body, funMemo)
          Set(TypeMemories(bodymems.memories.map[TypeMemory[VoideableRefinementType, Unit], Set[TypeMemory[VoideableRefinementType, Unit]]] { case TypeMemory(bodyres, store_) =>
            bodyres match {
              case SuccessResult(_) => TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store_)
              case ExceptionalResult(exres) => TypeMemory(ExceptionalResult(exres), store_)
            }
          }))
        case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
      }
    })
  }

  def evalWhile(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, body: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    def memoFix(store: TypeStore, memo: Map[TypeStore, TypeMemories[VoideableRefinementType, Unit]]): TypeMemories[VoideableRefinementType, Unit] = {
      def go(prevRes: TypeMemories[VoideableRefinementType, Unit]): TypeMemories[VoideableRefinementType, Unit] = {
        val condmems = evalLocal(localVars, store, cond, funMemo)
        val newRes = Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(condmems.memories.flatMap { case TypeMemory(condres, store__) =>
            condres match {
              case SuccessResult(condty) =>
                val errRes = TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(Error(Set(TypeError(condty, DataType("Bool"))))), store__)
                def succRes(refinenameopt : Option[Refinement]) : TypeMemories[VoideableRefinementType, Unit] = {
                  val refinementdef = refinenameopt.fold(dataTypeDefToRefinementDef("Bool", typememoriesops.datatypes("Bool")))(refinements.definitions)
                  Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(refinementdef.conss.keySet.map {
                    case "false" =>
                      TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store__)))
                    case "true" =>
                      val bodymems = evalLocal(localVars, store__, body, funMemo)
                      Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(bodymems.memories.map { case TypeMemory(bodyres, store_) =>
                        bodyres match {
                          case SuccessResult(_) =>
                            val widenedstore = Lattice[TypeStore].widen(store, store_)
                            memoFix(widenedstore, memo.updated(store, prevRes))
                          case ExceptionalResult(exres) =>
                            exres match {
                              case Break => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store_)))
                              case Continue =>
                                val widenedstore = Lattice[TypeStore].widen(store, store_)
                                memoFix(widenedstore, memo.updated(store, prevRes))
                              case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_)))
                            }
                        }
                      })
                    case _ => throw NonNormalFormMemories
                  })
                }
                val voidRes: Set[TypeMemories[VoideableRefinementType, Unit]] = if (condty.possiblyVoid) Set(TypeMemories(Set(errRes))) else Set()
                val tyRes: Set[TypeMemories[VoideableRefinementType, Unit]] = {
                  condty.refinementType match {
                    case DataRefinementType("Bool", rno) => Set(succRes(rno))
                    case ValueRefinementType => Set(TypeMemories[VoideableRefinementType, Unit](Set(errRes))) ++ Set(succRes(None))
                    case _ => Set(TypeMemories[VoideableRefinementType, Unit](Set(errRes)))
                  }
                }
                voidRes ++ tyRes
              case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
            }
        })
        if (Lattice[TypeMemories[VoideableRefinementType, Unit]].<=(newRes, prevRes)) newRes
        else go(Lattice[TypeMemories[VoideableRefinementType, Unit]].widen(prevRes, newRes))
      }
      memo.getOrElse(store, go(Lattice[TypeMemories[VoideableRefinementType, Unit]].bot))
    }
    memoFix(store, Map())
  }

  def evalSolve(localVars: Map[VarName, Type], store: TypeStore, vars: Seq[VarName], body: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    def memoFix(store: TypeStore, memo: Map[TypeStore, TypeMemories[VoideableRefinementType, Unit]]): TypeMemories[VoideableRefinementType, Unit] = {
      def go(prevRes: TypeMemories[VoideableRefinementType, Unit]): TypeMemories[VoideableRefinementType, Unit] = {
        val bodymems = evalLocal(localVars, store, body, funMemo)
        val newRes = Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(bodymems.memories.flatMap { case TypeMemory(bodyres, store_) =>
          bodyres match {
            case SuccessResult(t) =>
              val prevVars = vars.toList.flatMap(x => getVar(store, x).map(_.refinementType))
              val newVars = vars.toList.flatMap(x => getVar(store_, x).map(_.refinementType))
              val prevEmptyVar = vars.exists(x => getVar(store, x).isEmpty)
              val newEmptyVar = vars.exists(x => getVar(store_, x).isEmpty)
              if (prevEmptyVar || newEmptyVar)
                Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store_))))
              else {
                val prevPosEmptyVar = vars.exists(x => getVar(store, x).fold(true)(_.possiblyVoid))
                val newPosEmptyVar = vars.exists(x => getVar(store_, x).fold(true)(_.possiblyVoid))
                val posEx: Set[TypeMemories[VoideableRefinementType, Unit]] = if (prevPosEmptyVar || newPosEmptyVar)
                  Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Error(Set(OtherError))), store_))))
                else Set[TypeMemories[VoideableRefinementType, Unit]]()
                val posSuc: Set[TypeMemories[VoideableRefinementType, Unit]] = {
                  val widenedstore = Lattice[TypeStore].widen(store, store_)
                  val refinedeqvars = vars.toList.zip(prevVars.zip(newVars)).foldLeftM[Option, Map[VarName, VoideableRefinementType]](Map()) { (prevrefinedvarvals, v3) =>
                    val (varname, (pvv, nvv)) = v3
                    refineEq(VoideableRefinementType(possiblyVoid = false, pvv),
                      VoideableRefinementType(possiblyVoid = false, nvv)).map { eqval =>
                      prevrefinedvarvals.updated(varname, eqval)
                    }
                  }
                  Set(memoFix(widenedstore, memo.updated(store, prevRes))) ++
                    refinedeqvars.fold(Set[TypeMemories[VoideableRefinementType, Unit]]()) { refinedeqvarvals =>
                        Set(TypeMemories(Set(TypeMemory(SuccessResult(t), joinStores(store_, TypeStoreV(refinedeqvarvals))))))
                    }
                }
                posEx ++ posSuc
              }
            case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
          }
        })
        if (Lattice[TypeMemories[VoideableRefinementType, Unit]].<=(newRes, prevRes)) newRes
        else go(Lattice[TypeMemories[VoideableRefinementType, Unit]].widen(prevRes, newRes))
      }
      memo.getOrElse(store, go(Lattice[TypeMemories[VoideableRefinementType, Unit]].bot))
    }
    memoFix(store, Map())
  }

  def evalThrow(localVars: Map[VarName, Type], store: TypeStore, evl: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val valmems = evalLocal(localVars, store, evl, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(valmems.memories.flatMap { case TypeMemory(valres, store_) =>
      valres match {
        case SuccessResult(valty) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(Throw(valty)), store_))))
        case ExceptionalResult(exres) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store_))))
      }
    })
  }

  def evalTryCatch(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, catchVar: VarName, catchB: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val trymems = evalLocal(localVars, store, tryB, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(trymems.memories.flatMap { case TypeMemory(tryres, store__) =>
        tryres match {
          case SuccessResult(trytyp) => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(trytyp), store__))))
          case ExceptionalResult(exres) =>
            exres match {
              case Throw(throwtyp) =>
                val updstore__ = setVar(store__, catchVar, throwtyp)
                Set(TypeMemories[VoideableRefinementType, Unit](evalLocal(localVars, updstore__, catchB, funMemo).memories.map { case TypeMemory(res, store_) =>
                    TypeMemory(res, dropVars(store_, Set(catchVar)))
                }))
              case _ => Set(TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(ExceptionalResult(exres), store__))))
            }
        }
    })
  }

  def evalTryFinally(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, finallyB: Expr, funMemo: FunMemo): TypeMemories[VoideableRefinementType, Unit] = {
    val trymems = evalLocal(localVars, store, tryB, funMemo)
    Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(trymems.memories.map { case TypeMemory(tryres, store__) =>
        val finmems = evalLocal(localVars, store__, finallyB, funMemo)
        Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(finmems.memories.map { case TypeMemory(finres, store_) =>
          finres match {
            case SuccessResult(_) => TypeMemories(Set(TypeMemory[VoideableRefinementType, Unit](tryres, store_)))
            case ExceptionalResult(exres) => TypeMemories(Set(TypeMemory[VoideableRefinementType, Unit](ExceptionalResult(exres), store_)))
          }
        })
    })
  }

  def evalAssert(localVars: Map[VarName, Type], store: TypeStore, cond: Expr): TypeMemories[VoideableRefinementType, Unit] =
    TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = true, NoRefinementType)), store))) // Ignore assertions for now

  def evalLocalAll(localVars: Map[VarName, Type], store: TypeStore, exprs: Seq[Expr], funMemo: FunMemo): TypeMemories[List[VoideableRefinementType], Unit] = {
    exprs.toList.foldLeft[TypeMemories[List[VoideableRefinementType], Unit]](TypeMemories(Set(TypeMemory(SuccessResult(List()), store)))) { (mems, e) =>
      val flatMems = Lattice[TypeMemories[Flat[List[VoideableRefinementType]], Unit]].lubs(mems.memories.map[TypeMemories[Flat[List[VoideableRefinementType]], Unit], Set[TypeMemories[Flat[List[VoideableRefinementType]], Unit]]] {
        case TypeMemory(prevres, store__) =>
          prevres match {
            case SuccessResult(tys) =>
              val emems = evalLocal(localVars, store__, e, funMemo)
              Lattice[TypeMemories[Flat[List[VoideableRefinementType]], Unit]].lubs(emems.memories.map[TypeMemories[Flat[List[VoideableRefinementType]], Unit], Set[TypeMemories[Flat[List[VoideableRefinementType]], Unit]]] {
                case TypeMemory(res, store_) =>
                  res match {
                    case SuccessResult(ty) =>
                      if (Lattice[VoideableRefinementType].isBot(ty)) Lattice[TypeMemories[Flat[List[VoideableRefinementType]], Unit]].bot
                      else TypeMemories(Set(TypeMemory(SuccessResult(FlatValue(tys :+ ty)), store_)))
                    case ExceptionalResult(exres) => TypeMemories(Set(TypeMemory(ExceptionalResult(exres), store_)))
                  }
              })
            case ExceptionalResult(exres) =>
              TypeMemories[Flat[List[VoideableRefinementType]], Unit](Set(TypeMemory(ExceptionalResult(exres), store__)))
          }
      })
      unflatMems(flatMems) // Remove dummy Flat, since all merger of successes happens manually
    }
  }

  lazy val evalLocal: (Map[VarName, Type], TypeStore, Expr, FunMemo) => TypeMemories[VoideableRefinementType, Unit] = {
    if (Thread.interrupted()) {
      throw new InterruptedException()
    }
    memoized[Map[VarName, Type], TypeStore, Expr, FunMemo, TypeMemories[VoideableRefinementType, Unit]](memocacheSize) {
      (localVars: Map[VarName, Type], store: TypeStore, expr: Expr, funMemo: FunMemo) =>
        expr match {
          case BasicExpr(b) =>
            b match {
              case IntLit(i) =>
                TypeMemories(Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false,
                  BaseRefinementType(IntRefinementType(Intervals.Unbounded.singleton(i))))), store)))
              case StringLit(_) =>
                TypeMemories(Set(TypeMemory(SuccessResult(VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType))), store)))
            }
          case VarExpr(x) => evalVar(store, x)
          case FieldAccExpr(target, fieldName) => evalFieldAccess(localVars, store, target, fieldName, funMemo)
          case UnaryExpr(op, operand) => evalUnary(localVars, store, op, operand, funMemo)
          case BinaryExpr(left, op, right) => evalBinary(localVars, store, left, op, right, funMemo)
          case ConstructorExpr(name, args) => evalConstructor(localVars, store, name, args, funMemo)
          case ListExpr(elements) => evalList(localVars, store, elements, funMemo)
          case SetExpr(elements) => evalSet(localVars, store, elements, funMemo)
          case MapExpr(keyvalues) => evalMap(localVars, store, keyvalues, funMemo)
          case MapLookupExpr(emap, ekey) => evalMapLookup(localVars, store, emap, ekey, funMemo)
          case MapUpdExpr(emap, ekey, evl) => evalMapUpdate(localVars, store, emap, ekey, evl, funMemo)
          case FunCallExpr(functionName, args) => evalFunCall(localVars, store, functionName, args, funMemo)
          case ReturnExpr(evl) => evalReturn(localVars, store, evl, funMemo)
          case AssignExpr(assgn, targetexpr) => evalAssign(localVars, store, assgn, targetexpr, funMemo)
          case IfExpr(cond, thenB, elseB) => evalIf(localVars, store, cond, thenB, elseB, funMemo)
          case SwitchExpr(scrutinee, cases) => evalSwitch(localVars, store, scrutinee, cases, funMemo)
          case VisitExpr(strategy, scrutinee, cases) => evalVisit(localVars, store, strategy, scrutinee, cases, funMemo)
          case BreakExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Break), store)))
          case ContinueExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Continue), store)))
          case FailExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Fail(())), store)))
          case LocalBlockExpr(vardefs, exprs) => evalBlock(localVars, store, vardefs, exprs, funMemo)
          case ForExpr(enum, body) => evalFor(localVars, store, enum, body, funMemo)
          case WhileExpr(cond, body) => evalWhile(localVars, store, cond, body, funMemo)
          case SolveExpr(vars, body) => evalSolve(localVars, store, vars, body, funMemo)
          case ThrowExpr(evl) => evalThrow(localVars, store, evl, funMemo)
          case TryCatchExpr(tryB, catchVar, catchB) => evalTryCatch(localVars, store, tryB, catchVar, catchB, funMemo)
          case TryFinallyExpr(tryB, finallyB) => evalTryFinally(localVars, store, tryB, finallyB, funMemo)
          case AssertExpr(cond) => evalAssert(localVars, store, cond)
        }
    }
  }

  def eval(store: TypeStore, expr: Expr): TypeMemories[VoideableRefinementType, Unit] = evalLocal(Map.empty, store, expr, Map.empty)
}

object AbstractRefinementTypeExecutor {

  def executeGlobalVariables(executor: AbstractRefinementTypeExecutor, globVars: List[(VarName, Expr)]): String \/ TypeStore = {
    import executor.typememoriesops._
    import typestoreops._
    val initStore = TypeStoreV(globVars.toMap.transform((_,_) => VoideableRefinementType(possiblyVoid = true, NoRefinementType)))
    globVars.reverse.foldLeftM[String \/ ?, TypeStore](initStore) { (store, unevalglobvar) =>
      val (varname, varexpr) = unevalglobvar
      val resmems = executor.eval(store, varexpr)
      resmems.memories.toList.traverse[String \/ ?, TypeStore] { case TypeMemory(res, store_) =>
          res match {
            case SuccessResult(value) => joinStores(store_, TypeStoreV(Map(varname -> value))).right
            case ExceptionalResult(exres) => s"Evaluation of left-hand side for variable $varname failed with $exres".left
          }
      }.map(_.head)
    }
  }

  def execute(module: ModuleDef, function: VarName,
              initialRefinements: Refinements = new Refinements,
              initialStore: Option[TypeStore] = None,
              memoWidening: MemoWidening = ConstructorWidening(1),
              refinedMatches: Boolean = true): String \/ (Module, Refinements,
                                                          TypeMemories[VoideableRefinementType, Unit],
                                                          (Int, Int, Int), Duration) = {
    val start = Instant.now()
    for (transr <- ModuleTranslator.translateModule(module);
         executor = AbstractRefinementTypeExecutor(transr.semmod, initialRefinements = initialRefinements,
           memoWidening = memoWidening, refinedMatching = refinedMatches);
         store <- executeGlobalVariables(executor, transr.globalVarDefs);
         funcDef <- transr.semmod.funs.get(function).fold(s"Unknown function $function".left[(Type, List[Parameter], FunBody)])(_.right);
         (_, pars, funcBody) = funcDef;
         funcBodyExpr <- funcBody match {
           case ExprFunBody(expr) => expr.right
           case PrimitiveFunBody => s"Primitive function $function unsupported".left
         })
      yield {
        import executor.typememoriesops._
        import refinementtypeops._
        import typestoreops._
        val precallstore =
          initialStore.getOrElse(TypeStoreV(pars.map(p => p.name -> VoideableRefinementType(possiblyVoid = false, typeToRefinement(p.typ))).toMap))
        val callstore = joinStores(store, precallstore)
        val funcBodyRes = executor.evalLocal(pars.map(p => p.name -> p.typ).toMap, callstore, funcBodyExpr, Map.empty)
        val reslub = Lattice[TypeMemories[VoideableRefinementType, Unit]].lubs(funcBodyRes.memories.map { case TypeMemory(res, store_) =>
          res match {
            case ExceptionalResult(Return(retty)) => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(SuccessResult(retty), store_)))
            case _ => TypeMemories[VoideableRefinementType, Unit](Set(TypeMemory(res, store_)))
          }
        })
        val relevantrefinements = relevantRefinements(executor, reslub)
        val resrefinements = new Refinements(executor.refinements.definitions.toMap.filterKeys(relevantrefinements.contains))
        val end = Instant.now()
        (transr.semmod, resrefinements, reslub,
          (executor.memoMissesCount, executor.memoHitsCount, executor.memoWideningCount),
          Duration.between(start, end))
      }
  }

  private
  def relevantRefinements(executor: AbstractRefinementTypeExecutor, reslub: TypeMemories[VoideableRefinementType, Unit]): Set[Refinement] = {
    val allValues = reslub.memories.flatMap { case TypeMemory(res, store) =>
      val resValues = res match {
        case SuccessResult(value) => Set(value.refinementType)
        case ExceptionalResult(exres) => exres match {
          case Return(value) => Set(value.refinementType)
          case Throw(value) => Set(value.refinementType)
          case Break => Set()
          case Continue => Set()
          case Fail(_) => Set()
          case Error(_) => Set()
        }
      }
      val storeValues = store match {
        case TypeStoreTop => Set[RefinementType]()
        case TypeStoreV(vals) => vals.values.toSet[VoideableRefinementType].map(_.refinementType)
        case TypeStoreBot => Set[RefinementType]()
      }
      resValues ++ storeValues
    }
    allValues.flatMap(v => executor.typememoriesops.refinementtypeops.allRefinements(v))
  }
}
