package semantics.domains.abstracting

import semantics.domains.common.RSLattice
import syntax._
import util.Counter

import scalaz.std.option._
import scalaz.std.list._
import scalaz.syntax.foldable._

case class VoideableRefinementType(possiblyVoid: Boolean, refinementType: RefinementType)

sealed trait RefinementType
case class BaseRefinementType(basicType: BasicType) extends RefinementType
case class DataRefinementType(dataname: TypeName, refinename: Option[TypeName]) extends RefinementType
case class ListRefinementType(elementType: RefinementType) extends RefinementType
case class SetRefinementType(elementType: RefinementType) extends RefinementType
case class MapRefinementType(keyType: RefinementType, valueType: RefinementType) extends RefinementType
case object NoRefinementType extends RefinementType
case object ValueRefinementType extends RefinementType

case class RefinementDef(baseDataType: TypeName, conss: Map[ConsName, List[RefinementType]])

object RefinementTypes {
  def possibleConstructors(datatypes: DataTypeDefs, refinements: RefinementDefs, refinementType: RefinementType): Set[ConsName] = refinementType match {
    case BaseRefinementType(basicType) => Set()
    case DataRefinementType(dataname, refinename) =>
      refinename.fold(datatypes(dataname).keySet)(r => refinements(r).conss.keySet)
    case ListRefinementType(elementType) => possibleConstructors(datatypes, refinements, elementType)
    case SetRefinementType(elementType) => possibleConstructors(datatypes, refinements, elementType)
    case MapRefinementType(keyType, valueType) =>
      possibleConstructors(datatypes, refinements, keyType) ++
        possibleConstructors(datatypes, refinements, valueType)
    case NoRefinementType => Set()
    case ValueRefinementType => Set()
  }

  type DataTypeDefs = Map[TypeName, Map[ConsName, List[Type]]]
  type RefinementDefs = Map[TypeName, RefinementDef]

  private
  val counter = Counter(0)

  def allRefinements(refinements: RefinementDefs, rty: RefinementType): Set[TypeName] = {
    def loop(visited: Set[TypeName], rty: RefinementType): Set[TypeName] = {
      rty match {
        case BaseRefinementType(basicType) => Set()
        case DataRefinementType(dataname, refinename) =>
          refinename.toSet.flatMap { rn =>
            val chrtys = refinements(rn).conss.values.toSet[List[RefinementType]]
            val recres =
              if (visited.contains(rn)) Set[TypeName]()
              else chrtys.flatMap(_.toSet[RefinementType].flatMap(crty => loop(visited + rn, crty)))
            recres + rn
          }
        case ListRefinementType(elementType) => loop(visited, elementType)
        case SetRefinementType(elementType) => loop(visited, elementType)
        case MapRefinementType(keyType, valueType) => loop(visited, keyType) ++ loop(visited, valueType)
        case NoRefinementType => Set()
        case ValueRefinementType => Set()
      }
    }
    loop(Set(), rty)
  }

  def newRefinement(dataname: TypeName): TypeName = s"$dataname#${counter.++}"

  def addRefinement(datatypes: DataTypeDefs, refinements: RefinementDefs, dn: TypeName, rn: TypeName, rnrhs: Map[ConsName, List[RefinementType]]): (RefinementDefs, Option[TypeName]) = {
    // Small optimization: if the resulting value is the datatype itself, drop refinements
    val resrefinements = refinements.updated(rn, RefinementDef(dn, rnrhs))
    val dtRefinement = dataTypeDefToRefinementDef(dn, datatypes(dn))
    if (refinementTypeLattice.<=(datatypes, resrefinements.updated(dn, dtRefinement), DataRefinementType(dn, Some(dn)), DataRefinementType(dn, Some(rn)))) (refinements, None)
    else {
      // Another optimization: if there exists a refinement already use that one
      val eqRefineRes = resrefinements.find { case (rn2, rn2ref) => rn2 != rn && rn2ref.baseDataType == dn &&
        rnrhs.keySet == rn2ref.conss.keySet &&
          rnrhs.keySet.forall(cons =>
            rnrhs(cons).zip(rn2ref.conss(cons)).forall { case (rty1, rty2) => refinementTypeLattice.===(datatypes, resrefinements, rty1, rty2) })
      }
      eqRefineRes.fold((resrefinements, Some(rn))){ case (rn2, _) => (refinements, Some(rn2)) }
    }
  }

  def children(datatypes: DataTypeDefs, refinements: RefinementDefs, vrty: VoideableRefinementType): Set[(RefinementDefs, VoideableRefinementType, List[RefinementType])] = {
    val voidRes: Set[(RefinementDefs, VoideableRefinementType, List[RefinementType])] =
      if (vrty.possiblyVoid) Set((refinements, VoideableRefinementType(possiblyVoid = true, NoRefinementType), List()))
      else Set()
    val typRes: Set[(RefinementDefs, VoideableRefinementType, List[RefinementType])] = vrty.refinementType match {
      case BaseRefinementType(basicType) =>
        Set((refinements, VoideableRefinementType(possiblyVoid = false, BaseRefinementType(basicType)), List()))
      case DataRefinementType(dataname, refinenameopt) =>
        val refinementdef = refinenameopt.fold(dataTypeDefToRefinementDef(dataname, datatypes(dataname)))(refinements)
        refinementdef.conss.toSet[(ConsName, List[RefinementType])].map { case (cons, chrtyps) =>
          val newRn = newRefinement(dataname)
          val newrhs = Map(cons -> chrtyps)
          val (newrefinements, nrno) = addRefinement(datatypes, refinements, dataname, newRn, newrhs)
          (newrefinements, VoideableRefinementType(possiblyVoid = false, DataRefinementType(dataname, nrno)), chrtyps)
        }
      case ListRefinementType(elementType) =>
        Set((refinements, VoideableRefinementType(possiblyVoid = false, ListRefinementType(elementType)), List(elementType)))
      case SetRefinementType(elementType) =>
        Set((refinements, VoideableRefinementType(possiblyVoid = false, SetRefinementType(elementType)), List(elementType)))
      case MapRefinementType(keyType, valueType) =>
        Set((refinements, VoideableRefinementType(possiblyVoid = false, MapRefinementType(keyType, valueType)), List(keyType, valueType)))
      case NoRefinementType => Set()
      case ValueRefinementType =>
        Set((refinements, VoideableRefinementType(possiblyVoid = false, ValueRefinementType), List(ValueRefinementType))) // multiplicitly does not matter
    }
    voidRes ++ typRes
  }
  
  def typeToRefinement(t: Type): RefinementType = t match {
    case BaseType(b) => BaseRefinementType(b)
    case DataType(name) => DataRefinementType(name, None)
    case ListType(elementType) => ListRefinementType(typeToRefinement(elementType))
    case SetType(elementType) => SetRefinementType(typeToRefinement(elementType))
    case MapType(keyType, valueType) => MapRefinementType(typeToRefinement(keyType), typeToRefinement(valueType))
    case VoidType => throw new UnsupportedOperationException("Unexpected void type in data type definition")
    case ValueType => ValueRefinementType
  }


  def dataTypeDefToRefinementDef(dn: TypeName, dt: Map[ConsName, List[Type]]): RefinementDef = {
    RefinementDef(dn, dt.mapValues(tys => tys.map(typeToRefinement)))
  }

  def prettyDefs(refinements: RefinementDefs): List[String] = {
    def prettyRty(refinementType: RefinementType): String = refinementType match {
      case BaseRefinementType(basicType) =>
        basicType match {
          case IntType => "int"
          case StringType => "string"
        }
      case DataRefinementType(dataname, refinename) =>
        refinename.fold(dataname)(identity)
      case ListRefinementType(elementType) =>
        s"list<${prettyRty(elementType)}>"
      case SetRefinementType(elementType) =>
        s"set<${prettyRty(elementType)}>"
      case MapRefinementType(keyType, valueType) =>
        s"map<${prettyRty(keyType)}, ${prettyRty(valueType)}>"
      case NoRefinementType =>
        s"void"
      case ValueRefinementType =>
        "value"
    }
    def prettyDefn(defn: RefinementDef): String = {
      defn.conss.toList.map { case (cons, rtys) =>
          s"$cons(${rtys.map(rty => prettyRty(rty)).mkString(", ")})"
      }.mkString(" | ")
    }
    refinements.toList.map { case (nt, defn) =>
      s"refine $nt = ${prettyDefn(defn)}"
    }
  }

  implicit def refinementTypeLattice: RSLattice[RefinementType, DataTypeDefs, RefinementDefs] = new RSLattice[RefinementType, DataTypeDefs, RefinementDefs] {
    override def bot: RefinementType = NoRefinementType

    override def top: RefinementType = ValueRefinementType

    override def isBot(datatypes: DataTypeDefs, refinements: RefinementDefs, rty: RefinementType): Boolean = {
      def checkNonEmpty(memo: Map[TypeName, Boolean], rty: RefinementType): Boolean = {
        rty match {
          case BaseRefinementType(_) => true
          case DataRefinementType(_, refinenameopt) =>
            refinenameopt.fold(true)(refinename => checkNonEmptyP(memo, refinename))
          case ListRefinementType(elementType) => checkNonEmpty(memo, elementType)
          case SetRefinementType(elementType) => checkNonEmpty(memo, elementType)
          case MapRefinementType(keyType, valueType) => checkNonEmpty(memo, keyType) && checkNonEmpty(memo, valueType)
          case NoRefinementType => false
          case ValueRefinementType => true
        }
      }
      def checkNonEmptyP(memo: Map[TypeName, Boolean], refine: TypeName): Boolean = {
        def go (prevRes: Boolean): Boolean = {
          val newRes = refinements(refine).conss.exists { case (_, pvals) =>
            pvals.forall(pval => checkNonEmpty(memo.updated(refine, prevRes), pval))
          }
          if (prevRes == newRes) newRes
          else go(prevRes || newRes)
        }
        memo.getOrElse(refine, go(false))
      }
      !checkNonEmpty(Map.empty, rty)
    }


    private
    def upperBound(datatypes: DataTypeDefs, refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType, widening: Boolean) = {
      def replaceRec(refinements: RefinementDefs, rty: RefinementType, prevRns: Set[TypeName], newRn: TypeName): (RefinementDefs, RefinementType) = {
        def go(refinements: RefinementDefs, rty: RefinementType, visited: Set[TypeName]): (RefinementDefs, RefinementType) =
            rty match {
              case BaseRefinementType(basicType) =>
                (refinements, BaseRefinementType(basicType))
              case DataRefinementType(dataname, refinename) =>
                val (newrefinements, updRn) = refinename.fold[(RefinementDefs, Option[TypeName])]((refinements, None)) { rn =>
                  if (rn == newRn || prevRns.contains(rn)) (refinements, Some(newRn))
                  else if (visited.contains(rn)) (refinements, Some(rn))
                  else {
                    val rrefs = refinements(rn)
                    val (newrefinements, newConss) = rrefs.conss.foldLeft((refinements, Map[ConsName, List[RefinementType]]())) { (st, ccrt) =>
                      val (prevrefinements, prevconss) = st
                      val (cons, crts) = ccrt
                      val (newrefinements, newcrts) = crts.foldLeft((prevrefinements, List[RefinementType]())) { (st2, crt) =>
                        val (prevrefinements2, prevcrts) = st2
                        val (newrefinements, newcrt) = go(prevrefinements2, crt, visited + rn)
                        (newrefinements, prevcrts :+ newcrt)
                      }
                      (newrefinements, prevconss.updated(cons, newcrts))
                    }
                    val newRn2 = newRefinement(dataname)
                    addRefinement(datatypes, newrefinements, dataname, newRn2, newConss)
                  }
                }
                (newrefinements, DataRefinementType(dataname, updRn))
              case ListRefinementType(elementType) =>
                val (newrefinements, newRty) = go(refinements, elementType, visited)
                (newrefinements, ListRefinementType(newRty))
              case SetRefinementType(elementType) =>
                val (newrefinements, newRty) = go(refinements, elementType, visited)
                (newrefinements, SetRefinementType(newRty))
              case MapRefinementType(keyType, valueType) =>
                val (newrefinements, newKRty) = go(refinements, keyType, visited)
                val (newrefinements2, newVRty) = go(refinements, valueType, visited)
                (newrefinements2, MapRefinementType(newKRty, newVRty))
              case NoRefinementType =>
                (refinements, NoRefinementType)
              case ValueRefinementType =>
                (refinements, ValueRefinementType)
            }
        go(refinements, rty, Set())
      }

      def merge(memo: Map[(TypeName, TypeName), TypeName], refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType): (RefinementDefs, RefinementType) = {
        (rty1, rty2) match {
          case (_, ValueRefinementType) | (ValueRefinementType, _) => (refinements, ValueRefinementType)
          case (_, NoRefinementType) => (refinements, rty1)
          case (NoRefinementType, _) => (refinements, rty2)
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntType, IntType) => (refinements, BaseRefinementType(IntType))
              case (StringType, StringType) => (refinements, BaseRefinementType(StringType))
              case (_, _) => (refinements, ValueRefinementType)
            }
          case (ListRefinementType(irty1), ListRefinementType(irty2)) =>
            val (newrefinements, irtylub) = merge(memo, refinements, irty1, irty2)
            (newrefinements, ListRefinementType(irtylub))
          case (SetRefinementType(irty1), SetRefinementType(irty2)) =>
            val (newrefinements, irtylub) = merge(memo, refinements, irty1, irty2)
            (newrefinements, SetRefinementType(irtylub))
          case (MapRefinementType(krty1, vrty1), MapRefinementType(krty2, vrty2)) =>
            val (newrefinements, krtylub) = merge(memo, refinements, krty1, krty2)
            val (newrefinements2, vrtylub) = merge(memo, newrefinements, vrty1, vrty2)
            (newrefinements2, MapRefinementType(krtylub, vrtylub))
          case (DataRefinementType(dn1, rno1), DataRefinementType(dn2, rno2)) if dn1 == dn2 =>
            rno1.fold((refinements, DataRefinementType(dn1, None)))(rn1 => rno2.fold((refinements, DataRefinementType(dn1, None))) { rn2 =>
              val (newrefinements, newrty) = if (widening) {
                mergeP(memo, refinements, dn1, rn1, rn2, widened = true)
              } else {
                mergeP(memo, refinements, dn1, rn1, rn2, widened = false)
              }
              (newrefinements, DataRefinementType(dn1, newrty))
            })
          case (_, _) => (refinements, ValueRefinementType)
        }
      }

      def mergeP(memo: Map[(TypeName, TypeName), TypeName], refinements: RefinementDefs, dn: TypeName, rn1: TypeName, rn2: TypeName, widened: Boolean): (RefinementDefs, Option[TypeName]) = {
        if (rn1 == rn2) (refinements, Some(rn1))
        else if (memo.contains((rn1, rn2))) (refinements, Some(memo((rn1, rn2))))
        else {
          if (!widened && <=(datatypes, refinements, DataRefinementType(dn, Some(rn1)), DataRefinementType(dn, Some(rn2)))) (refinements, Some(rn2))
          else if (!widened && <=(datatypes, refinements, DataRefinementType(dn, Some(rn2)), DataRefinementType(dn, Some(rn1)))) (refinements, Some(rn1))
          else {
            val newRn = newRefinement(dn)
            val RefinementDef(_, rrn1) = refinements(rn1)
            val RefinementDef(_, rrn2) = refinements(rn2)
            val newConss = rrn1.keySet union rrn2.keySet
            val (newrefinements, newRhs) = newConss.foldLeft((refinements, Map.empty[ConsName, List[RefinementType]])) { (st, cons) =>
              val (prevrefinements, prevconss) = st
              val (newrefinements, newRtys) = rrn1.get(cons).fold((prevrefinements, rrn2(cons))) { rn1tys =>
                rrn2.get(cons).fold((prevrefinements, rn1tys)) { rn2tys =>
                  rn1tys.zip(rn2tys).foldLeft((prevrefinements, List.empty[RefinementType])) { (st2, rntypair) =>
                    val (prevrefinements2, prevrtys) = st2
                    val (rnty1, rnty2) = rntypair
                    val (newrefinements, newRty) = merge(memo.updated((rn1, rn2), newRn), prevrefinements2, rnty1, rnty2)
                    (newrefinements, prevrtys :+ newRty)
                  }
                }
              }
              (newrefinements, prevconss.updated(cons, newRtys))
            }
            val (newrefinements2, newRhsW) =
              if (widened)
                newRhs.foldLeft((newrefinements, Map[ConsName, List[RefinementType]]())) { (st, ccrts) =>
                  val (prevrefinements, prevconss) = st
                  val (cons, crts) = ccrts
                  val (newrefinements3, newcrts) = crts.foldLeft((prevrefinements, List[RefinementType]())) { (st2, crt) =>
                    val (prevrefinements2, prevcrts) = st2
                    val (newrefinements4, newcrt) = replaceRec(prevrefinements2, crt, Set(rn1, rn2), newRn)
                    (newrefinements4, prevcrts :+ newcrt)
                  }
                  (newrefinements3, prevconss.updated(cons, newcrts))
                }
              else (newrefinements, newRhs)
            addRefinement(datatypes, newrefinements2, dn, newRn, newRhsW)
          }
        }
      }
      merge(Map.empty, refinements, rty1, rty2)
    }

    override def lub(datatypes: DataTypeDefs, refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType): (RefinementDefs, RefinementType) = {
      val res = upperBound(datatypes, refinements, rty1, rty2, widening = false)
      res
    }

    override def glb(datatypes: DataTypeDefs, refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType): (RefinementDefs, RefinementType) = {
      def merge(memo: Map[(TypeName, TypeName), TypeName], refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType): (RefinementDefs, RefinementType) = {
        (rty1, rty2) match {
          case (NoRefinementType, _) | (_, NoRefinementType) => (refinements, NoRefinementType)
          case (ValueRefinementType, _) => (refinements, rty1)
          case (_, ValueRefinementType) => (refinements, rty2)
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntType, IntType) => (refinements, BaseRefinementType(IntType))
              case (StringType, StringType) => (refinements, BaseRefinementType(StringType))
              case (_, _) => (refinements, NoRefinementType)
            }
          case (ListRefinementType(irty1), ListRefinementType(irty2)) =>
            val (newrefinements, irtyglb) = merge(memo, refinements, irty1, irty2)
            if (isBot(datatypes, newrefinements, irtyglb)) (refinements, ListRefinementType(NoRefinementType))
            else (newrefinements, ListRefinementType(irtyglb))
          case (SetRefinementType(irty1), SetRefinementType(irty2)) =>
            val (newrefinements, irtyglb) = merge(memo, refinements, irty1, irty2)
            if (isBot(datatypes, newrefinements, irtyglb)) (refinements, SetRefinementType(NoRefinementType))
            else (newrefinements, SetRefinementType(irtyglb))
          case (MapRefinementType(krty1, vrty1), MapRefinementType(krty2, vrty2)) =>
            val (newrefinements, krtyglb) = merge(memo, refinements, krty1, krty2)
            if (isBot(datatypes, newrefinements, krtyglb)) (refinements, MapRefinementType(NoRefinementType, NoRefinementType))
            else {
              val (newrefinements2, vrtyglb) = merge(memo, refinements, vrty1, vrty2)
              if (isBot(datatypes, newrefinements2, vrtyglb)) (refinements, MapRefinementType(NoRefinementType, NoRefinementType))
              else (newrefinements2, MapRefinementType(krtyglb, vrtyglb))
            }
          case (DataRefinementType(dn1, rn1o), DataRefinementType(dn2, rn2o)) if dn1 == dn2 =>
            rn1o.fold[(RefinementDefs, RefinementType)]((refinements, DataRefinementType(dn2, rn2o)))(rn1 =>
              rn2o.fold[(RefinementDefs, RefinementType)]((refinements, DataRefinementType(dn1, rn1o))) { rn2 =>
                mergeP(memo, refinements, dn1, rn1, rn2).fold[(RefinementDefs, RefinementType)]((refinements, NoRefinementType)) { case (newrefinements, newrty) =>
                  (newrefinements, DataRefinementType(dn1, Some(newrty)))
                }
              })
          case (_, _) => (refinements, NoRefinementType)
        }
      }
      def mergeP(memo: Map[(TypeName, TypeName), TypeName], refinements: RefinementDefs, dn: TypeName, rn1: TypeName, rn2: TypeName): Option[(RefinementDefs, TypeName)] = {
        if (memo.contains((rn1, rn2))) Some((refinements, memo((rn1, rn2))))
        else {
          if (<=(datatypes, refinements, DataRefinementType(dn, Some(rn1)), DataRefinementType(dn, Some(rn2)))) Some((refinements, rn1))
          else if (<=(datatypes, refinements, DataRefinementType(dn, Some(rn2)), DataRefinementType(dn, Some(rn1)))) Some((refinements, rn2))
          else {
            val newRn = newRefinement(dn)
            val RefinementDef(_, rrn1) = refinements(rn1)
            val RefinementDef(_, rrn2) = refinements(rn2)
            val newConss = rrn1.keySet intersect rrn2.keySet
            if (newConss.isEmpty) None
            else {
              val newres = newConss.toList.foldLeftM[Option, (RefinementDefs, Map[ConsName, List[RefinementType]])]((refinements, Map.empty[ConsName, List[RefinementType]])) { (st, cons) =>
                val (prevrefinements, prevconss) = st
                val rn1tys = rrn1(cons)
                val rn2tys = rrn2(cons)
                val newres = rn1tys.zip(rn2tys).foldLeftM[Option, (RefinementDefs, List[RefinementType])]((prevrefinements, List.empty[RefinementType])) { (st2, rntypair) =>
                  val (prevrefinements2, prevrtys) = st2
                  val (rnty1, rnty2) = rntypair
                  val (newrefinements, newRty) = merge(memo.updated((rn1, rn2), newRn), prevrefinements2, rnty1, rnty2)
                  if (isBot(datatypes, newrefinements, newRty)) None
                  else Some((newrefinements, prevrtys :+ newRty))
                }
                newres.map { case (newrefinements, newRtys) => (newrefinements, prevconss.updated(cons, newRtys)) }
              }
              newres.map { case (newrefinements, newRnRhs) => (newrefinements.updated(newRn, RefinementDef(dn, newRnRhs)), newRn) }
            }
          }
        }
      }
      merge(Map.empty, refinements, rty1, rty2)
    }

    override def <=(datatypes: DataTypeDefs, refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType): Boolean = {
      def sub(assumptions: Map[TypeName, Set[TypeName]], rty1: RefinementType, rty2: RefinementType): Boolean = {
        if (rty1 == rty2) true
        else {
          (rty1, rty2) match {
            case (NoRefinementType, _) => true
            case (_, ValueRefinementType) => true
            case (BaseRefinementType(bty1), BaseRefinementType(bty2)) => bty1 == bty2
            case (ListRefinementType(irty1), ListRefinementType(irty2)) => sub(assumptions, irty1, irty2)
            case (SetRefinementType(irty1), SetRefinementType(irty2)) =>  sub(assumptions, irty1, irty2)
            case (MapRefinementType(krty1, vrty1), MapRefinementType(krty2, vrty2)) =>
              sub(assumptions, krty1, krty2) && sub(assumptions, vrty1, vrty2)
            case (DataRefinementType(dn1, rno1), DataRefinementType(dn2, rno2)) if dn1 == dn2 =>
              rno2.fold(true)(rn2 => rno1.fold(false)(rn1 => subR(assumptions, rn1, rn2)))
            case _ => false
          }
        }
      }
      def subH(assumptions: Map[TypeName, Set[TypeName]], rn1: TypeName, rn2: TypeName) = {
        if (refinements.contains(rn1) && refinements.contains(rn2)) {
          val RefinementDef(_, rrn1) = refinements(rn1)
          val RefinementDef(_, rrn2) = refinements(rn2)
          rrn1.forall { case (cons, rn1tys) =>
            rrn2.contains(cons) &&
              rn1tys.zip(rrn2(cons)).forall { case (rn1ty, rn2ty) => sub(assumptions, rn1ty, rn2ty) }
          }
        } else false
      }
      def subR(assumptions: Map[TypeName, Set[TypeName]], rn1: TypeName, rn2: TypeName): Boolean = {
        if (rn1 == rn2) true
        else {
          assumptions.get(rn1).fold(subH(assumptions.updated(rn1, Set(rn2)), rn1, rn2)) { srefs1 =>
            if (srefs1.contains(rn2)) true
            else subH(assumptions.updated(rn1, srefs1 + rn2), rn1, rn2)
          }
        }
      }
      sub(Map(), rty1, rty2)
    }

    override def widen(datatypes: DataTypeDefs, refinements: RefinementDefs, rty1: RefinementType, rty2: RefinementType, bound: Int): (RefinementDefs, RefinementType) =
      upperBound(datatypes, refinements, rty1, rty2, widening = true)
  }

  implicit def voideableRefinementTypeLattice: RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs] = new RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs] {
    override def bot: VoideableRefinementType = VoideableRefinementType(possiblyVoid = false, RSLattice[RefinementType, DataTypeDefs, RefinementDefs].bot)

    override def top: VoideableRefinementType = VoideableRefinementType(possiblyVoid = true, RSLattice[RefinementType, DataTypeDefs, RefinementDefs].top)

    override def isBot(datatypes: DataTypeDefs, refinements: RefinementDefs, vrty: VoideableRefinementType): Boolean =
      !vrty.possiblyVoid &&
        RSLattice[RefinementType, DataTypeDefs, RefinementDefs].isBot(datatypes, refinements, vrty.refinementType)

    override def lub(datatypes: DataTypeDefs, refinements: RefinementDefs, vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): (RefinementDefs, VoideableRefinementType) = {
      val (newrefinements, rtylub) = RSLattice[RefinementType, DataTypeDefs, RefinementDefs].lub(datatypes, refinements, vrty1.refinementType, vrty2.refinementType)
      (newrefinements, VoideableRefinementType(vrty1.possiblyVoid || vrty2.possiblyVoid, rtylub))
    }

    override def glb(datatypes: DataTypeDefs, refinements: RefinementDefs, vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): (RefinementDefs, VoideableRefinementType) = {
      val (newrefinements, rtyglb) = RSLattice[RefinementType, DataTypeDefs, RefinementDefs].glb(datatypes, refinements, vrty1.refinementType, vrty2.refinementType)
      (newrefinements, VoideableRefinementType(vrty1.possiblyVoid && vrty2.possiblyVoid, rtyglb))
    }

    override def <=(datatypes: DataTypeDefs, refinements: RefinementDefs, vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): Boolean = {
      vrty1.possiblyVoid <= vrty2.possiblyVoid &&
        RSLattice[RefinementType, DataTypeDefs, RefinementDefs].<=(datatypes, refinements, vrty1.refinementType, vrty2.refinementType)
    }

    override def widen(datatypes: DataTypeDefs, refinements: RefinementDefs, vrty1: VoideableRefinementType, vrty2: VoideableRefinementType, bound: Int): (RefinementDefs, VoideableRefinementType) = {
      val (newrefinements, rtywid) = RSLattice[RefinementType, DataTypeDefs, RefinementDefs].widen(datatypes, refinements, vrty1.refinementType, vrty2.refinementType, bound)
      (newrefinements, VoideableRefinementType(vrty1.possiblyVoid || vrty2.possiblyVoid, rtywid))
    }
  }
}