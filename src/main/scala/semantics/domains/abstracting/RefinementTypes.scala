package semantics.domains.abstracting

import semantics.domains.abstracting.RefinementTypes.DataTypeDefs
import semantics.domains.common.Lattice
import syntax._
import util.Counter

import scala.collection.mutable
import scalaz.std.option._
import scalaz.std.list._
import scalaz.syntax.foldable._

case class VoideableRefinementType(possiblyVoid: Boolean, refinementType: RefinementType)

sealed trait RefinementType
case class BaseRefinementType(basicType: BasicType) extends RefinementType
case class DataRefinementType(dataname: TypeName, refinename: Option[Refinement]) extends RefinementType
case class ListRefinementType(elementType: RefinementType) extends RefinementType
case class SetRefinementType(elementType: RefinementType) extends RefinementType
case class MapRefinementType(keyType: RefinementType, valueType: RefinementType) extends RefinementType
case object NoRefinementType extends RefinementType
case object ValueRefinementType extends RefinementType

case class RefinementDef(baseDataType: TypeName, conss: Map[ConsName, List[RefinementType]])

class Refinement(val refinementName: String) {
  override def toString: TypeName = refinementName
}

class Refinements(initialDefinitions: Map[Refinement, RefinementDef] = Map()) {
  private
  val refCounter = Counter(0)

  val definitions: mutable.WeakHashMap[Refinement, RefinementDef] = mutable.WeakHashMap.empty ++= initialDefinitions

  def newRefinement(dataname: TypeName): Refinement = new Refinement(s"$dataname#${refCounter.++}")

  def prettyDefs: List[String] = {
    def prettyRty(refinementType: RefinementType): String = refinementType match {
      case BaseRefinementType(basicType) =>
        basicType match {
          case IntType => "int"
          case StringType => "string"
        }
      case DataRefinementType(dataname, refinename) =>
        refinename.fold(dataname)(_.refinementName)
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
    definitions.toList.map { case (nt, defn) =>
      s"refine ${nt.refinementName} = ${prettyDefn(defn)}"
    }
  }
}

object RefinementTypes {
  type DataTypeDefs = Map[TypeName, Map[ConsName, List[Type]]]
}

case class RefinementTypeOps(datatypes: DataTypeDefs, refinements: Refinements) {
  def possibleConstructors(refinementType: RefinementType): Set[ConsName] = refinementType match {
    case BaseRefinementType(_) => Set()
    case DataRefinementType(dataname, refinename) =>
      refinename.fold(datatypes(dataname).keySet)(r => refinements.definitions(r).conss.keySet)
    case ListRefinementType(elementType) => possibleConstructors(elementType)
    case SetRefinementType(elementType) => possibleConstructors(elementType)
    case MapRefinementType(keyType, valueType) =>
      possibleConstructors(keyType) ++
        possibleConstructors(valueType)
    case NoRefinementType => Set()
    case ValueRefinementType => Set()
  }

  def allRefinements(rty: RefinementType): Set[Refinement] = {
    def loop(visited: Set[Refinement], rty: RefinementType): Set[Refinement] = {
      rty match {
        case BaseRefinementType(_) => Set()
        case DataRefinementType(_, refinename) =>
          refinename.toSet.flatMap { rn =>
            val chrtys = refinements.definitions(rn).conss.values.toSet[List[RefinementType]]
            val recres =
              if (visited.contains(rn)) Set[Refinement]()
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

  def addRefinement(dn: TypeName, rn: Refinement, rnrhs: Map[ConsName, List[RefinementType]]): Option[Refinement] = {
    // Small optimization: if the resulting value is the datatype itself, drop refinements
    refinements.definitions.update(rn, RefinementDef(dn, rnrhs))
    val dtrn = new Refinement(dn)
    val dtRefinement = dataTypeDefToRefinementDef(dn, datatypes(dn))
    refinements.definitions.update(dtrn, dtRefinement)
    val isSubRefinement = Lattice[RefinementType].<=(DataRefinementType(dn, Some(dtrn)), DataRefinementType(dn, Some(rn)))
    refinements.definitions.remove(dtrn)
    if (isSubRefinement) {
      None
    } else {
      // Another optimization: if there exists a refinement already use that one
      val eqRefineRes = refinements.definitions.find { case (rn2, rn2ref) => rn2 != rn && rn2ref.baseDataType == dn &&
        rnrhs.keySet == rn2ref.conss.keySet &&
          rnrhs.keySet.forall(cons =>
            rnrhs(cons).zip(rn2ref.conss(cons)).forall { case (rty1, rty2) => RefinementTypeLattice.===(rty1, rty2) })
      }.map(_._1)
      eqRefineRes.fold(Some(rn))(rn2 => Some(rn2))
    }
  }

  def children(vrty: VoideableRefinementType): Set[(VoideableRefinementType, List[RefinementType])] = {
    val voidRes: Set[(VoideableRefinementType, List[RefinementType])] =
      if (vrty.possiblyVoid) Set((VoideableRefinementType(possiblyVoid = true, NoRefinementType), List()))
      else Set()
    val typRes: Set[(VoideableRefinementType, List[RefinementType])] = vrty.refinementType match {
      case BaseRefinementType(basicType) =>
        Set((VoideableRefinementType(possiblyVoid = false, BaseRefinementType(basicType)), List()))
      case DataRefinementType(dataname, refinenameopt) =>
        val refinementdef = refinenameopt.fold(dataTypeDefToRefinementDef(dataname, datatypes(dataname)))(refinements.definitions)
        refinementdef.conss.toSet[(ConsName, List[RefinementType])].map { case (cons, chrtyps) =>
          val newRn = refinements.newRefinement(dataname)
          val newrhs = Map(cons -> chrtyps)
          val nrno = addRefinement(dataname, newRn, newrhs)
          (VoideableRefinementType(possiblyVoid = false, DataRefinementType(dataname, nrno)), chrtyps)
        }
      case ListRefinementType(elementType) =>
        Set((VoideableRefinementType(possiblyVoid = false, ListRefinementType(elementType)), List(elementType)))
      case SetRefinementType(elementType) =>
        Set((VoideableRefinementType(possiblyVoid = false, SetRefinementType(elementType)), List(elementType)))
      case MapRefinementType(keyType, valueType) =>
        Set((VoideableRefinementType(possiblyVoid = false, MapRefinementType(keyType, valueType)), List(keyType, valueType)))
      case NoRefinementType => Set()
      case ValueRefinementType =>
        Set((VoideableRefinementType(possiblyVoid = false, ValueRefinementType), List(ValueRefinementType))) // multiplicitly does not matter
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


  implicit def RefinementTypeLattice: Lattice[RefinementType] = new Lattice[RefinementType] {
    override def bot: RefinementType = NoRefinementType

    override def top: RefinementType = ValueRefinementType

    override def isBot(rty: RefinementType): Boolean = {
      def checkNonEmpty(memo: Map[Refinement, Boolean], rty: RefinementType): Boolean = {
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
      def checkNonEmptyP(memo: Map[Refinement, Boolean], refine: Refinement): Boolean = {
        def go (prevRes: Boolean): Boolean = {
          val newRes = refinements.definitions(refine).conss.exists { case (_, pvals) =>
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
    def upperBound(rty1: RefinementType, rty2: RefinementType, widening: Boolean) = {
      def merge(memo: Map[(Refinement, Refinement), Refinement], widmemo: Map[Refinement, Refinement], rty1: RefinementType, rty2: RefinementType): RefinementType = {
        (rty1, rty2) match {
          case (_, ValueRefinementType) | (ValueRefinementType, _) => ValueRefinementType
          case (_, NoRefinementType) => rty1
          case (NoRefinementType, _) => rty2
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntType, IntType) => BaseRefinementType(IntType)
              case (StringType, StringType) => BaseRefinementType(StringType)
              case (_, _) => ValueRefinementType
            }
          case (ListRefinementType(irty1), ListRefinementType(irty2)) =>
            val irtylub = merge(memo, widmemo, irty1, irty2)
            ListRefinementType(irtylub)
          case (SetRefinementType(irty1), SetRefinementType(irty2)) =>
            val irtylub = merge(memo, widmemo, irty1, irty2)
            SetRefinementType(irtylub)
          case (MapRefinementType(krty1, vrty1), MapRefinementType(krty2, vrty2)) =>
            val krtylub = merge(memo, widmemo, krty1, krty2)
            val vrtylub = merge(memo, widmemo, vrty1, vrty2)
            MapRefinementType(krtylub, vrtylub)
          case (DataRefinementType(dn1, rno1), DataRefinementType(dn2, rno2)) if dn1 == dn2 =>
            rno1.fold(DataRefinementType(dn1, None))(rn1 => rno2.fold(DataRefinementType(dn1, None)) { rn2 =>
              val newrty = mergeP(memo, widmemo, dn1, rn1, rn2)
              val newrtyw = {
                if (widening && newrty.exists(widmemo.contains)) Some(widmemo(newrty.get))
                else newrty
              }
              DataRefinementType(dn1, newrtyw)
            })
          case (_, _) => ValueRefinementType
        }
      }

      def mergeP(memo: Map[(Refinement, Refinement), Refinement], widmemo: Map[Refinement, Refinement], dn: TypeName, rn1: Refinement, rn2: Refinement): Option[Refinement] = {
        if (rn1 == rn2) Some(rn1)
        else if (memo.contains((rn1, rn2)) || memo.contains((rn2, rn1))) Some(memo((rn1, rn2)))
        else {
          if (!widening && <=(DataRefinementType(dn, Some(rn1)), DataRefinementType(dn, Some(rn2)))) Some(rn2)
          else if (<=(DataRefinementType(dn, Some(rn2)), DataRefinementType(dn, Some(rn1)))) Some(rn1)
          else {
            val newRn = refinements.newRefinement(dn)
            val RefinementDef(_, rrn1) = refinements.definitions(rn1)
            val RefinementDef(_, rrn2) = refinements.definitions(rn2)
            val newConss = rrn1.keySet union rrn2.keySet
            val newRhs = newConss.foldLeft(Map.empty[ConsName, List[RefinementType]]) { (prevconss, cons) =>
              val newRtys = rrn1.get(cons).fold(rrn2(cons)) { rn1tys =>
                rrn2.get(cons).fold(rn1tys) { rn2tys =>
                  rn1tys.zip(rn2tys).foldLeft(List.empty[RefinementType]) { (prevrtys, rntypair) =>
                    val (rnty1, rnty2) = rntypair
                    val newRty = merge(memo.updated((rn1, rn2), newRn), widmemo.updated(rn1, newRn).updated(rn2, newRn), rnty1, rnty2)
                    prevrtys :+ newRty
                  }
                }
              }
              prevconss.updated(cons, newRtys)
            }
            addRefinement(dn, newRn, newRhs)
          }
        }
      }
      merge(Map.empty, Map.empty, rty1, rty2)
    }

    override def lub(rty1: RefinementType, rty2: RefinementType): RefinementType = {
      upperBound(rty1, rty2, widening = false)
    }

    override def glb(rty1: RefinementType, rty2: RefinementType): RefinementType = {
      def merge(memo: Map[(Refinement, Refinement), Refinement], rty1: RefinementType, rty2: RefinementType): RefinementType = {
        (rty1, rty2) match {
          case (NoRefinementType, _) | (_, NoRefinementType) => NoRefinementType
          case (ValueRefinementType, _) => rty1
          case (_, ValueRefinementType) => rty2
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntType, IntType) => BaseRefinementType(IntType)
              case (StringType, StringType) => BaseRefinementType(StringType)
              case (_, _) => NoRefinementType
            }
          case (ListRefinementType(irty1), ListRefinementType(irty2)) =>
            val irtyglb = merge(memo, irty1, irty2)
            if (isBot(irtyglb)) ListRefinementType(NoRefinementType)
            else ListRefinementType(irtyglb)
          case (SetRefinementType(irty1), SetRefinementType(irty2)) =>
            val irtyglb = merge(memo, irty1, irty2)
            if (isBot(irtyglb)) SetRefinementType(NoRefinementType)
            else SetRefinementType(irtyglb)
          case (MapRefinementType(krty1, vrty1), MapRefinementType(krty2, vrty2)) =>
            val krtyglb = merge(memo, krty1, krty2)
            if (isBot(krtyglb)) MapRefinementType(NoRefinementType, NoRefinementType)
            else {
              val vrtyglb = merge(memo, vrty1, vrty2)
              if (isBot(vrtyglb)) MapRefinementType(NoRefinementType, NoRefinementType)
              else MapRefinementType(krtyglb, vrtyglb)
            }
          case (DataRefinementType(dn1, rn1o), DataRefinementType(dn2, rn2o)) if dn1 == dn2 =>
            rn1o.fold[RefinementType](DataRefinementType(dn2, rn2o))(rn1 =>
              rn2o.fold[RefinementType](DataRefinementType(dn1, rn1o)) { rn2 =>
                mergeP(memo, dn1, rn1, rn2).fold[RefinementType](NoRefinementType) { newrty =>
                  DataRefinementType(dn1, Some(newrty))
                }
              })
          case (_, _) => NoRefinementType
        }
      }
      def mergeP(memo: Map[(Refinement, Refinement), Refinement], dn: TypeName, rn1: Refinement, rn2: Refinement): Option[Refinement] = {
        if (memo.contains((rn1, rn2))) Some(memo((rn1, rn2)))
        else {
          if (<=(DataRefinementType(dn, Some(rn1)), DataRefinementType(dn, Some(rn2)))) Some(rn1)
          else if (<=(DataRefinementType(dn, Some(rn2)), DataRefinementType(dn, Some(rn1)))) Some(rn2)
          else {
            val newRn = refinements.newRefinement(dn)
            val RefinementDef(_, rrn1) = refinements.definitions(rn1)
            val RefinementDef(_, rrn2) = refinements.definitions(rn2)
            val newConss = rrn1.keySet intersect rrn2.keySet
            if (newConss.isEmpty) None
            else {
              val newres = newConss.toList.foldLeftM[Option, Map[ConsName, List[RefinementType]]](Map.empty[ConsName, List[RefinementType]]) { (prevconss, cons) =>
                val rn1tys = rrn1(cons)
                val rn2tys = rrn2(cons)
                val newres = rn1tys.zip(rn2tys).foldLeftM[Option, List[RefinementType]](List.empty[RefinementType]) { (prevrtys, rntypair) =>
                  val (rnty1, rnty2) = rntypair
                  val newRty = merge(memo.updated((rn1, rn2), newRn), rnty1, rnty2)
                  if (isBot(newRty)) None
                  else Some(prevrtys :+ newRty)
                }
                newres.map { newRtys => prevconss.updated(cons, newRtys) }
              }
              newres.map { newRnRhs =>
                refinements.definitions.update(newRn, RefinementDef(dn, newRnRhs))
                newRn
              }
            }
          }
        }
      }
      merge(Map.empty, rty1, rty2)
    }

    override def <=(rty1: RefinementType, rty2: RefinementType): Boolean = {
      def sub(assumptions: Map[Refinement, Set[Refinement]], rty1: RefinementType, rty2: RefinementType): Boolean = {
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
      def subH(assumptions: Map[Refinement, Set[Refinement]], rn1: Refinement, rn2: Refinement) = {
        if (refinements.definitions.contains(rn1) && refinements.definitions.contains(rn2)) {
          val RefinementDef(_, rrn1) = refinements.definitions(rn1)
          val RefinementDef(_, rrn2) = refinements.definitions(rn2)
          rrn1.forall { case (cons, rn1tys) =>
            rrn2.contains(cons) &&
              rn1tys.zip(rrn2(cons)).forall { case (rn1ty, rn2ty) => sub(assumptions, rn1ty, rn2ty) }
          }
        } else false
      }
      def subR(assumptions: Map[Refinement, Set[Refinement]], rn1: Refinement, rn2: Refinement): Boolean = {
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

    override def widen(rty1: RefinementType, rty2: RefinementType, bound: Int): RefinementType =
      upperBound(rty1, rty2, widening = true)
  }

  implicit def VoideableRefinementTypeLattice: Lattice[VoideableRefinementType] = new Lattice[VoideableRefinementType] {
    override def bot: VoideableRefinementType = VoideableRefinementType(possiblyVoid = false, Lattice[RefinementType].bot)

    override def top: VoideableRefinementType = VoideableRefinementType(possiblyVoid = true, Lattice[RefinementType].top)

    override def isBot(vrty: VoideableRefinementType): Boolean =
      !vrty.possiblyVoid && Lattice[RefinementType].isBot(vrty.refinementType)

    override def lub(vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): VoideableRefinementType = {
      val rtylub = Lattice[RefinementType].lub(vrty1.refinementType, vrty2.refinementType)
      VoideableRefinementType(vrty1.possiblyVoid || vrty2.possiblyVoid, rtylub)
    }

    override def glb(vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): VoideableRefinementType = {
      val rtyglb = Lattice[RefinementType].glb(vrty1.refinementType, vrty2.refinementType)
      VoideableRefinementType(vrty1.possiblyVoid && vrty2.possiblyVoid, rtyglb)
    }

    override def <=(vrty1: VoideableRefinementType, vrty2: VoideableRefinementType): Boolean = {
      vrty1.possiblyVoid <= vrty2.possiblyVoid &&
        Lattice[RefinementType].<=(vrty1.refinementType, vrty2.refinementType)
    }

    override def widen(vrty1: VoideableRefinementType, vrty2: VoideableRefinementType, bound: Int): VoideableRefinementType = {
      val rtywid = Lattice[RefinementType].widen(vrty1.refinementType, vrty2.refinementType, bound)
      VoideableRefinementType(vrty1.possiblyVoid || vrty2.possiblyVoid, rtywid)
    }
  }
}