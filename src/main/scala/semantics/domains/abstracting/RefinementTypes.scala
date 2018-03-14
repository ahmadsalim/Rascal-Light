package semantics.domains.abstracting

import semantics.domains.abstracting.IntegerW._
import semantics.domains.abstracting.RefinementTypes._
import semantics.domains.common.Lattice
import syntax._
import util.{Counter, Memoization}

import scala.collection.mutable
import scalaz.std.list._
import scalaz.std.option._
import scalaz.syntax.foldable._
import Intervals.Positive.{Lattice => PosLattice}

import scala.collection.immutable.ListMap

import Memoization._

case class VoideableRefinementType(possiblyVoid: Boolean, refinementType: RefinementType)

sealed trait BasicRefinementType
case class IntRefinementType(ival: Intervals.Unbounded.Interval) extends BasicRefinementType
case object StringRefinementType extends BasicRefinementType

sealed trait RefinementType
case class BaseRefinementType(basicType: BasicRefinementType) extends RefinementType
case class DataRefinementType(dataname: TypeName, refinename: Option[Refinement]) extends RefinementType
case class ListRefinementType(elementType: RefinementType, length: Intervals.Positive.Interval) extends RefinementType
case class SetRefinementType(elementType: RefinementType, cardinality: Intervals.Positive.Interval) extends RefinementType
case class MapRefinementType(keyType: RefinementType, valueType: RefinementType, size: Intervals.Positive.Interval) extends RefinementType
case object NoRefinementType extends RefinementType
case object ValueRefinementType extends RefinementType

sealed trait RefinementChildren[RT] {
  def isFixed: Boolean
  def map[RT2](f: RT => RT2): RefinementChildren[RT2]
}
case class FixedSeqChildren[RT](children: List[RT]) extends RefinementChildren[RT] {
  override def isFixed: Boolean = true
  override def map[RT2](f: (RT) => RT2): RefinementChildren[RT2] = FixedSeqChildren(children.map(f))
}
case class ArbitrarySeqChildren[RT](childty: RT, size: Intervals.Positive.Interval) extends RefinementChildren[RT] {
  override def isFixed: Boolean = false
  override def map[RT2](f: (RT) => RT2): RefinementChildren[RT2] = ArbitrarySeqChildren(f(childty), size)
}

case class RefinementDef(baseDataType: TypeName, conss: Map[ConsName, List[RefinementType]])
case class URefinementDef(baseDataType: TypeName, conss: Map[ConsName, Set[List[RefinementType]]])

class Refinement(val refinementName: String) {
  override def toString: TypeName = refinementName

  def canEqual(other: Any): Boolean = other.isInstanceOf[Refinement]

  override def equals(other: Any): Boolean = other match {
    case that: Refinement =>
      (that canEqual this) &&
        refinementName == that.refinementName
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(refinementName)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }
}

class Refinements(initialDefinitions: Map[Refinement, RefinementDef] = Map()) {
  private
  val refCounter = Counter(0)

  val definitions: mutable.WeakHashMap[Refinement, RefinementDef] = mutable.WeakHashMap.empty ++= initialDefinitions

  def newRefinement(dataname: TypeName): Refinement = new Refinement(s"$dataname#${refCounter.++}")

  def prettyDefs: List[String] = {

    def prettyDefn(defn: RefinementDef): String = {
      defn.conss.toList.sortBy(_._1).map { case (cons, rtys) =>
        s"$cons(${rtys.map(rty => RefinementTypes.pretty(rty)).mkString(", ")})"
      }.mkString(" | ")
    }
    definitions.toList.map { case (nt, defn) =>
      s"refine ${nt.refinementName} = ${prettyDefn(defn)}"
    }
  }
}

object RefinementTypes {
  type DataTypeDefs = Map[TypeName, Map[ConsName, List[Type]]]

  def pretty(refinementType: RefinementType): String = refinementType match {
    case BaseRefinementType(basicType) =>
      basicType match {
        case IntRefinementType(ival) =>
          if (Intervals.Unbounded.Lattice.isTop(ival)) "int"
          else s"{x : int | x ∈ $ival}"
        case StringRefinementType => "string"
      }
    case DataRefinementType(dataname, refinename) =>
      refinename.fold(dataname)(_.refinementName)
    case ListRefinementType(elementType, length) =>
      val plistty = s"list[${pretty(elementType)}]"
      if (Intervals.Positive.Lattice.isTop(length)) plistty
      else s"{xs : $plistty | |xs| ∈ $length}"
    case SetRefinementType(elementType, cardinality) =>
      val psetty = s"set[${pretty(elementType)}]"
      if (Intervals.Positive.Lattice.isTop(cardinality)) psetty
      else s"{xs : $psetty | |xs| ∈ $cardinality}"
    case MapRefinementType(keyType, valueType, size) =>
      val pmapty = s"map[${pretty(keyType)}, ${pretty(valueType)}]"
      if (Intervals.Positive.Lattice.isTop(size)) pmapty
      else s"{xs : $pmapty | |xs| ∈ $size}"
    case NoRefinementType =>
      s"void"
    case ValueRefinementType =>
      "value"
  }
}

object RefinementChildren {
  // TODO A partial lattice to allow merging some items, can be made more type safe
  implicit def RefinementChildrenLattice[RT : Lattice]: Lattice[RefinementChildren[RT]] = new Lattice[RefinementChildren[RT]] {
    override def <=(a1: RefinementChildren[RT], a2: RefinementChildren[RT]): Boolean = {
      a1 match {
        case FixedSeqChildren(cs1) =>
          a2 match {
            case FixedSeqChildren(cs2) if cs1.lengthCompare(cs2.length) == 0 =>
              cs1.zip(cs2).forall { case (c1, c2) => Lattice[RT].<=(c1, c2) }
            case _ => throw new UnsupportedOperationException
          }
        case ArbitrarySeqChildren(cty1, size1) =>
          a2 match {
            case ArbitrarySeqChildren(cty2, size2) =>
              Lattice[RT].<=(cty1, cty2) && Lattice[Intervals.Positive.Interval].<=(size1, size2)
            case _ => throw new UnsupportedOperationException
          }
      }
    }

    override def widen(a1: RefinementChildren[RT], a2: RefinementChildren[RT], bound: Int): RefinementChildren[RT] = {
      a1 match {
        case FixedSeqChildren(cs1) =>
          a2 match {
            case FixedSeqChildren(cs2) if cs1.lengthCompare(cs2.length) == 0 =>
              FixedSeqChildren(cs1.zip(cs2).map { case (c1, c2) => Lattice[RT].widen(c1, c2, bound) })
            case _ => throw new UnsupportedOperationException
          }
        case ArbitrarySeqChildren(cty1, size1) =>
          a2 match {
            case ArbitrarySeqChildren(cty2, size2) =>
              ArbitrarySeqChildren(Lattice[RT].widen(cty1, cty2, bound), Lattice[Intervals.Positive.Interval].widen(size1, size2, bound))
            case _=> throw new UnsupportedOperationException
          }
      }
    }

    override def isBot(a: RefinementChildren[RT]): Boolean = false

    override def bot: RefinementChildren[RT] = throw new UnsupportedOperationException

    override def top: RefinementChildren[RT] = throw new UnsupportedOperationException

    override def lub(a1: RefinementChildren[RT], a2: RefinementChildren[RT]): RefinementChildren[RT] = {
      a1 match {
        case FixedSeqChildren(cs1) =>
          a2 match {
            case FixedSeqChildren(cs2) if cs1.lengthCompare(cs2.length) == 0 =>
              FixedSeqChildren(cs1.zip(cs2).map { case (c1, c2) => Lattice[RT].lub(c1, c2) })
            case _ => throw new UnsupportedOperationException
          }
        case ArbitrarySeqChildren(cty1, size1) =>
          a2 match {
            case ArbitrarySeqChildren(cty2, size2) =>
              ArbitrarySeqChildren(Lattice[RT].lub(cty1, cty2), Lattice[Intervals.Positive.Interval].lub(size1, size2))
            case _=> throw new UnsupportedOperationException
          }
      }
    }

    override def glb(a1: RefinementChildren[RT], a2: RefinementChildren[RT]): RefinementChildren[RT] = {
      a1 match {
        case FixedSeqChildren(cs1) =>
          a2 match {
            case FixedSeqChildren(cs2) if cs1.lengthCompare(cs2.length) == 0 =>
              FixedSeqChildren(cs1.zip(cs2).map { case (c1, c2) => Lattice[RT].glb(c1, c2) })
            case _ => throw new UnsupportedOperationException
          }
        case ArbitrarySeqChildren(cty1, size1) =>
          a2 match {
            case ArbitrarySeqChildren(cty2, size2) =>
              ArbitrarySeqChildren(Lattice[RT].glb(cty1, cty2), Lattice[Intervals.Positive.Interval].glb(size1, size2))
            case _=> throw new UnsupportedOperationException
          }
      }
    }
  }

  def makeNil[RT: Lattice](rcs: RefinementChildren[RT]): RefinementChildren[RT] = rcs match {
    case FixedSeqChildren(_) => FixedSeqChildren(List())
    case ArbitrarySeqChildren(childty, size) => ArbitrarySeqChildren(Lattice[RT].bot, Intervals.Positive.singleton(0))
  }

  def makeCons[RT: Lattice](rc: RT, rcs: RefinementChildren[RT]): RefinementChildren[RT] = rcs match {
    case FixedSeqChildren(children) => FixedSeqChildren(rc :: children)
    case ArbitrarySeqChildren(childty, size) =>
      ArbitrarySeqChildren(Lattice[RT].lub(rc, childty), Intervals.Positive.+(size, Intervals.Positive.singleton(1)))
  }

  def getNil[RT](refinementChildren: RefinementChildren[RT]): Boolean = refinementChildren match {
    case FixedSeqChildren(children) => children.isEmpty
    case ArbitrarySeqChildren(_, size) => Intervals.Positive.contains(size, 0)
  }

  def getCons[RT](refinementChildren: RefinementChildren[RT]): Option[(RT, RefinementChildren[RT])] = refinementChildren match {
    case FixedSeqChildren(children) =>
      children match {
        case Nil => None
        case c::cs => Some((c,FixedSeqChildren(cs)))
      }
    case ArbitrarySeqChildren(childty, size) =>
      if (Lattice[Intervals.Positive.Interval].isBot(size) || IntegerW.<=(size.ub, 0)) None
      else Some((childty, ArbitrarySeqChildren(childty, Intervals.Positive.-(size, Intervals.Positive.singleton(1)))))
  }

  def getSize[RT](refinementChildren: RefinementChildren[RT]): Intervals.Positive.Interval = refinementChildren match {
    case FixedSeqChildren(children) => Intervals.Positive.singleton(children.length)
    case ArbitrarySeqChildren(_, size) => size
  }
}

object VoideableRefinementTypes {
  def pretty(voideableRefinementType: VoideableRefinementType): String = {
    val prettyRty = RefinementTypes.pretty(voideableRefinementType.refinementType)
    val prettyVoideable = if (voideableRefinementType.possiblyVoid) "?" else ""
    s"$prettyRty$prettyVoideable"
  }
}


case class RefinementTypeOps(datatypes: DataTypeDefs, refinements: Refinements) {


  def makeList(content: List[RefinementType]): ListRefinementType =
    ListRefinementType(Lattice[RefinementType].lubs(content.toSet), Intervals.Positive.singleton(content.length))

  private
  def partitionElements(rtys: List[RefinementType]): Set[RefinementType] = {
    rtys.foldLeft(Set[RefinementType]()) { (prtys, rty) =>
      if (prtys.exists(prty => Lattice[RefinementType].<=(rty, prty))) {
        prtys
      } else {
        prtys.filterNot(prty => Lattice[RefinementType].<=(prty, rty)) + rty
      }
    }
  }

  def makeSet(content: List[RefinementType]): SetRefinementType = {
    val partitioned = partitionElements(content)
    val minSize = partitioned.size
    val maxSize = content.size
    val rtylub = Lattice[RefinementType].lubs(partitioned)
    SetRefinementType(rtylub, Intervals.Positive.makeInterval(minSize, maxSize))
  }

  def makeMap(keys: List[RefinementType], values: List[RefinementType]): MapRefinementType = {
    val partitionedKeys = partitionElements(keys)
    val minSize = partitionedKeys.size
    val maxSize = keys.size
    val krtylub = Lattice[RefinementType].lubs(partitionedKeys)
    val vrtylub = Lattice[RefinementType].lubs(values.toSet)
    MapRefinementType(krtylub, vrtylub, Intervals.Positive.makeInterval(minSize, maxSize))
  }

  def possibleConstructors(refinementType: RefinementType): Set[ConsName] = refinementType match {
    case BaseRefinementType(_) => Set()
    case DataRefinementType(dataname, refinename) =>
      refinename.fold(datatypes(dataname).keySet)(r => refinements.definitions(r).conss.keySet)
    case ListRefinementType(elementType, _) => possibleConstructors(elementType)
    case SetRefinementType(elementType, _) => possibleConstructors(elementType)
    case MapRefinementType(keyType, valueType, _) =>
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
        case ListRefinementType(elementType, _) => loop(visited, elementType)
        case SetRefinementType(elementType, _) => loop(visited, elementType)
        case MapRefinementType(keyType, valueType, _) => loop(visited, keyType) ++ loop(visited, valueType)
        case NoRefinementType => Set()
        case ValueRefinementType => Set()
      }
    }
    loop(Set(), rty)
  }

  private
  val (dataTypeNameRefs, dataTypeRefinements) = {
    val refs = datatypes.keySet.map(tn => tn -> new Refinement(tn)).toMap
    (refs,
      refs.map { case (tn, tnr) =>
        (tnr, dataTypeDefToRefinementDef(tn, datatypes(tn), refs)) })
  }

  def addRefinement(dn: TypeName, rn: Refinement, rnrhs: Map[ConsName, List[RefinementType]]): Option[Refinement] = {
    // Small optimization: if the resulting value is the datatype itself, drop refinements
    refinements.definitions.update(rn, RefinementDef(dn, rnrhs))
    ensureUnique(dn, rn, Set())
  }

  private
  def ensureUnique(dn: TypeName, rn: Refinement, excludedRns: Set[Refinement]): Option[Refinement] = {
    refinements.definitions ++= dataTypeRefinements
    val isSubRefinement = Lattice[RefinementType].<=(DataRefinementType(dn, dataTypeNameRefs.get(dn)), DataRefinementType(dn, Some(rn)))
    refinements.definitions --= dataTypeRefinements.keySet
    if (isSubRefinement) {
      refinements.definitions.remove(rn)
      None
    } else {
      // Another optimization: if there exists a refinement already use that one
      val eqRefineRes = refinements.definitions.find { case (rn2, rn2ref) =>
        rn2 != rn && !excludedRns.contains(rn2) &&
          rn2ref.baseDataType == dn &&
            RefinementTypeLattice.===(DataRefinementType(dn, Some(rn)), DataRefinementType(dn, Some(rn2)))
      }.map(_._1)
      eqRefineRes.fold(Some(rn)) {
        rn2 =>
          refinements.definitions.remove(rn)
          Some(rn2)
      }
    }
  }

  def children(vrty: VoideableRefinementType): Set[(VoideableRefinementType, RefinementChildren[RefinementType])] = {
    val voidRes: Set[(VoideableRefinementType, RefinementChildren[RefinementType])] =
      if (vrty.possiblyVoid) Set((VoideableRefinementType(possiblyVoid = true, NoRefinementType), FixedSeqChildren(List())))
      else Set()
    val typRes: Set[(VoideableRefinementType, RefinementChildren[RefinementType])] = vrty.refinementType match {
      case BaseRefinementType(basicType) =>
        Set((VoideableRefinementType(possiblyVoid = false, BaseRefinementType(basicType)), FixedSeqChildren(List())))
      case DataRefinementType(dataname, refinenameopt) =>
        val refinementdef = refinenameopt.fold(dataTypeDefToRefinementDef(dataname, datatypes(dataname)))(refinements.definitions)
        refinementdef.conss.toSet[(ConsName, List[RefinementType])].map { case (cons, chrtyps) =>
          val newRn = refinements.newRefinement(dataname)
          val newrhs = Map(cons -> chrtyps)
          val nrno = addRefinement(dataname, newRn, newrhs)
          (VoideableRefinementType(possiblyVoid = false, DataRefinementType(dataname, nrno)), FixedSeqChildren(chrtyps))
        }
      case ListRefinementType(elementType, length) =>
        Set((VoideableRefinementType(possiblyVoid = false, ListRefinementType(elementType, length)), ArbitrarySeqChildren(elementType, length)))
      case SetRefinementType(elementType, cardinality) =>
        Set((VoideableRefinementType(possiblyVoid = false, SetRefinementType(elementType, cardinality)), ArbitrarySeqChildren(elementType, cardinality)))
      case MapRefinementType(keyType, valueType, size) =>
        // TODO Fix to use arbitrary seq children without losing precision (now slightly incorrect on stateful programs)
        Set((VoideableRefinementType(possiblyVoid = false, MapRefinementType(keyType, valueType, size)), FixedSeqChildren(List(keyType, valueType))))
      case NoRefinementType => Set()
      case ValueRefinementType =>
        Set((VoideableRefinementType(possiblyVoid = false, ValueRefinementType), ArbitrarySeqChildren(ValueRefinementType, Intervals.Positive.Lattice.top)))
    }
    voidRes ++ typRes
  }

  def basetypeToRefinement(b: BasicType): BasicRefinementType = b match {
    case IntType => IntRefinementType(Intervals.Unbounded.Lattice.top)
    case StringType => StringRefinementType
  }

  def typeToRefinement(t: Type, refs: Map[TypeName, Refinement] = Map()): RefinementType = t match {
    case BaseType(b) => BaseRefinementType(basetypeToRefinement(b))
    case DataType(name) => DataRefinementType(name, refs.get(name))
    case ListType(elementType) => ListRefinementType(typeToRefinement(elementType, refs), Intervals.Positive.Lattice.top)
    case SetType(elementType) => SetRefinementType(typeToRefinement(elementType, refs), Intervals.Positive.Lattice.top)
    case MapType(keyType, valueType) => MapRefinementType(typeToRefinement(keyType, refs), typeToRefinement(valueType, refs), Intervals.Positive.Lattice.top)
    case VoidType => throw new UnsupportedOperationException("Unexpected void type in data type definition")
    case ValueType => ValueRefinementType
  }

  def dataTypeDefToRefinementDef(dn: TypeName, dt: Map[ConsName, List[Type]], refs: Map[TypeName, Refinement] = Map()): RefinementDef = {
    RefinementDef(dn, dt.mapValues(tys => tys.map(typeToRefinement(_, refs))))
  }

  // Overapproximative negation
  def negate(rty: RefinementType): RefinementType = {
    // TODO Implement negation algorithm of Aiken instead

    def negateRty(memo: Map[Refinement, Refinement], rty: RefinementType): RefinementType = rty match {
      case BaseRefinementType(basicType) => BaseRefinementType(basicType)
      case DataRefinementType(dataname, refinename) =>
        if (datatypes(dataname).values.forall(_.isEmpty) && refinename.isDefined) {
          val rndef = refinements.definitions(refinename.get)
          val newRn = refinements.newRefinement(dataname)
          val newRnDef = dataTypeRefinements(dataTypeNameRefs(dataname)).conss -- rndef.conss.keySet
          val finalRn = addRefinement(dataname, newRn, newRnDef)
          DataRefinementType(dataname, finalRn)
        } else DataRefinementType(dataname, None)
      case ListRefinementType(elementType, _) =>
        ListRefinementType(RefinementTypeLattice.lub(elementType, negateRty(memo, elementType)), Intervals.Positive.Lattice.top) // To ensure overapproximation
      case SetRefinementType(elementType, _) =>
        SetRefinementType(RefinementTypeLattice.lub(elementType, negateRty(memo, elementType)), Intervals.Positive.Lattice.top) // To ensure overapproximation
      case MapRefinementType(keyType, valueType, _) =>
        MapRefinementType(RefinementTypeLattice.lub(keyType, negateRty(memo, keyType)),
          RefinementTypeLattice.lub(valueType, negateRty(memo, valueType)), Intervals.Positive.Lattice.top) // To ensure overapproximation
      case NoRefinementType => NoRefinementType
      case ValueRefinementType => ValueRefinementType
    }

    negateRty(Map[Refinement, Refinement](), rty)
  }

  // Excludes constructors in `excludedConss` recursively from a datatype
  def excluding(dn: TypeName, excludedConss: Set[ConsName]): RefinementType = {
    def removeSelfRefinements(rty: RefinementType): RefinementType = rty match {
      case DataRefinementType(dataname, refinename) if refinename.exists(r => r.refinementName == dataname) =>
        DataRefinementType(dataname, None)
      case ListRefinementType(elementType, length) => ListRefinementType(removeSelfRefinements(elementType), length)
      case SetRefinementType(elementType, cardinality) => SetRefinementType(removeSelfRefinements(elementType), cardinality)
      case MapRefinementType(keyType, valueType, size) =>
        MapRefinementType(removeSelfRefinements(keyType), removeSelfRefinements(valueType), size)
      case _ => rty
    }
    val newRn = refinements.newRefinement(dn)
    val newRnDef = dataTypeRefinements(dataTypeNameRefs(dn)).conss -- excludedConss
    val newRnDefRep = newRnDef.transform {
      (_, tys) => tys.map(rty => removeSelfRefinements(substDataRefsInType(rty, dataTypeNameRefs(dn), Some(newRn))))
    }
    val resRn = addRefinement(dn, newRn, newRnDefRep)
    DataRefinementType(dn, resRn)
  }

  private
  def substDataRefsInType(refinementType: RefinementType, rn: Refinement, nrno: Option[Refinement]): RefinementType = refinementType match {
    case DataRefinementType(dataname, refinename) =>
      DataRefinementType(dataname, refinename.flatMap(rn2 => if (rn2 == rn) nrno else Some(rn2)))
    case ListRefinementType(elementType, length) =>
      ListRefinementType(substDataRefsInType(elementType, rn, nrno), length)
    case SetRefinementType(elementType, cardinality) =>
      SetRefinementType(substDataRefsInType(elementType, rn, nrno), cardinality)
    case MapRefinementType(keyType, valueType, size) =>
      MapRefinementType(substDataRefsInType(keyType, rn, nrno), substDataRefsInType(valueType, rn, nrno), size)
    case _ => refinementType
  }

  val memocacheSize = 10000

  implicit def RefinementTypeLattice: Lattice[RefinementType] = new Lattice[RefinementType] {
    override def bot: RefinementType = NoRefinementType

    override def top: RefinementType = ValueRefinementType

    override def isBot(rty: RefinementType): Boolean = isBotH(rty)

    private
    lazy val isBotH: (RefinementType) => Boolean = memoized[RefinementType, Boolean](memocacheSize){ (rty: RefinementType) =>
      def checkNonEmpty(memo: Map[Refinement, Boolean], rty: RefinementType): Boolean = {
        rty match {
          case BaseRefinementType(_) => true
          case DataRefinementType(_, refinenameopt) =>
            refinenameopt.fold(true)(refinename => checkNonEmptyP(memo, refinename))
          case ListRefinementType(irty, length) =>
            !Intervals.Positive.Lattice.isBot(length)
          case SetRefinementType(irty, cardinality) =>
            !Intervals.Positive.Lattice.isBot(cardinality)
          case MapRefinementType(krty, vrty, size) =>
            !Intervals.Positive.Lattice.isBot(size)
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

    override def lub(rty1: RefinementType, rty2: RefinementType): RefinementType = lubH(rty1, rty2)

    private
    lazy val lubH: (RefinementType, RefinementType) => RefinementType =
      memoized[RefinementType,RefinementType,RefinementType](memocacheSize) { (rty1: RefinementType, rty2: RefinementType) =>
      def merge(memo: Map[(Refinement, Refinement), Refinement], rty1: RefinementType, rty2: RefinementType): RefinementType = {
        (rty1, rty2) match {
          case (_, ValueRefinementType) | (ValueRefinementType, _) => ValueRefinementType
          case (_, NoRefinementType) => rty1
          case (NoRefinementType, _) => rty2
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntRefinementType(ival1), IntRefinementType(ival2)) =>
                BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.lub(ival1, ival2)))
              case (StringRefinementType, StringRefinementType) => BaseRefinementType(StringRefinementType)
              case (_, _) => ValueRefinementType
            }
          case (ListRefinementType(irty1, length1), ListRefinementType(irty2, length2)) =>
            val irtylub = merge(memo, irty1, irty2)
            val length = Intervals.Positive.Lattice.lub(length1, length2)
            ListRefinementType(irtylub, length)
          case (SetRefinementType(irty1, cardinality1), SetRefinementType(irty2, cardinality2)) =>
            val irtylub = merge(memo, irty1, irty2)
            val cardinality = Intervals.Positive.Lattice.lub(cardinality1, cardinality2)
            SetRefinementType(irtylub, cardinality)
          case (MapRefinementType(krty1, vrty1, size1), MapRefinementType(krty2, vrty2, size2)) =>
            val krtylub = merge(memo, krty1, krty2)
            val vrtylub = merge(memo, vrty1, vrty2)
            val size = Intervals.Positive.Lattice.lub(size1, size2)
            MapRefinementType(krtylub, vrtylub, size)
          case (DataRefinementType(dn1, rno1), DataRefinementType(dn2, rno2)) if dn1 == dn2 =>
            rno1.fold(DataRefinementType(dn1, None))(rn1 => rno2.fold(DataRefinementType(dn1, None)) { rn2 =>
              val newrty = mergeP(memo, dn1, rn1, rn2)
              DataRefinementType(dn1, newrty)
            })
          case (_, _) => ValueRefinementType
        }
      }

      def mergeP(memo: Map[(Refinement, Refinement), Refinement], dn: TypeName, rn1: Refinement, rn2: Refinement): Option[Refinement] = {
        if (rn1 == rn2) Some(rn1)
        else if (memo.contains((rn1, rn2)) || memo.contains((rn2, rn1))) Some(memo((rn1, rn2)))
        else {
          if (<=(DataRefinementType(dn, Some(rn1)), DataRefinementType(dn, Some(rn2)))) Some(rn2)
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
                    val newRty = merge(memo.updated((rn1, rn2), newRn), rnty1, rnty2)
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
      merge(Map.empty, rty1, rty2)
    }

    override def glb(rty1: RefinementType, rty2: RefinementType): RefinementType = glbH(rty1, rty2)

    private
    lazy val glbH: (RefinementType, RefinementType) => RefinementType = memoized[RefinementType, RefinementType, RefinementType](memocacheSize) {
      (rty1 : RefinementType, rty2: RefinementType) =>
      def merge(memo: Map[(Refinement, Refinement), Refinement], rty1: RefinementType, rty2: RefinementType): RefinementType = {
        (rty1, rty2) match {
          case (NoRefinementType, _) | (_, NoRefinementType) => NoRefinementType
          case (ValueRefinementType, _) => rty1
          case (_, ValueRefinementType) => rty2
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntRefinementType(ival1), IntRefinementType(ival2)) =>
                val ivalglb = Intervals.Unbounded.Lattice.glb(ival1, ival2)
                if (Intervals.Unbounded.Lattice.isBot(ivalglb)) NoRefinementType
                else BaseRefinementType(IntRefinementType(ivalglb))
              case (StringRefinementType, StringRefinementType) => BaseRefinementType(StringRefinementType)
              case (_, _) => NoRefinementType
            }
          case (ListRefinementType(irty1, length1), ListRefinementType(irty2, length2)) =>
            val length = Intervals.Positive.Lattice.glb(length1, length2)
            if (Intervals.Positive.Lattice.isBot(length)) bot
            else {
              val irtyglb = merge(memo, irty1, irty2)
              if (isBot(irtyglb)) ListRefinementType(NoRefinementType, Intervals.Positive.singleton(0))
              else ListRefinementType(irtyglb, length)
            }
          case (SetRefinementType(irty1, cardinality1), SetRefinementType(irty2, cardinality2)) =>
            val cardinality = Intervals.Positive.Lattice.glb(cardinality1, cardinality2)
            if (Intervals.Positive.Lattice.isBot(cardinality)) bot
            else {
              val irtyglb = merge(memo, irty1, irty2)
              if (isBot(irtyglb)) SetRefinementType(NoRefinementType, Intervals.Positive.singleton(0))
              else SetRefinementType(irtyglb, cardinality)
            }
          case (MapRefinementType(krty1, vrty1, size1), MapRefinementType(krty2, vrty2, size2)) =>
            val size = Intervals.Positive.Lattice.glb(size1, size2)
            if (Intervals.Positive.Lattice.isBot(size)) bot
            else {
              val krtyglb = merge(memo, krty1, krty2)
              if (isBot(krtyglb)) MapRefinementType(NoRefinementType, NoRefinementType, Intervals.Positive.singleton(0))
              else {
                val vrtyglb = merge(memo, vrty1, vrty2)
                if (isBot(vrtyglb)) MapRefinementType(NoRefinementType, NoRefinementType, Intervals.Positive.singleton(0))
                else MapRefinementType(krtyglb, vrtyglb, size)
              }
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

    override def <=(rty1: RefinementType, rty2: RefinementType): Boolean = leqH(rty1, rty2)

    private lazy val
    leqH: (RefinementType, RefinementType) => Boolean = memoized[RefinementType, RefinementType, Boolean](memocacheSize) {
      (rty1: RefinementType, rty2: RefinementType) =>
      def sub(assumptions: Map[Refinement, Set[Refinement]], rty1: RefinementType, rty2: RefinementType): Boolean = {
        if (rty1 == rty2) true
        else {
          (rty1, rty2) match {
            case (NoRefinementType, _) => true
            case (_, ValueRefinementType) => true
            case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
              (bty1, bty2) match {
                case (IntRefinementType(ival1), IntRefinementType(ival2)) => Intervals.Unbounded.Lattice.<=(ival1, ival2)
                case (StringRefinementType, StringRefinementType) => true
                case _ => false
              }
            case (ListRefinementType(irty1, length1), ListRefinementType(irty2, length2)) =>
              sub(assumptions, irty1, irty2) && Intervals.Positive.Lattice.<=(length1, length2)
            case (SetRefinementType(irty1, cardinality1), SetRefinementType(irty2, cardinality2)) =>
              sub(assumptions, irty1, irty2) && Intervals.Positive.Lattice.<=(cardinality1, cardinality2)
            case (MapRefinementType(krty1, vrty1, size1), MapRefinementType(krty2, vrty2, size2)) =>
              sub(assumptions, krty1, krty2) && sub(assumptions, vrty1, vrty2) &&
                Intervals.Positive.Lattice.<=(size1, size2)
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

    private def toURefinementDef(rnDef: RefinementDef) = {
      URefinementDef(rnDef.baseDataType, rnDef.conss.mapValues(Set(_)))
    }

    private def getURefinementDef(wrefinements: Map[Refinement, URefinementDef], prevRn: Refinement): URefinementDef = {
      if (wrefinements.contains(prevRn)) wrefinements(prevRn)
      else {
        val prevRnDef = refinements.definitions(prevRn)
        toURefinementDef(prevRnDef)
      }
    }

    def reachable(wrefinements: Map[Refinement, URefinementDef], rn1: Refinement, rn2: Refinement): Boolean = {
      def go(visited: Set[Refinement], rn: Refinement): Boolean = {
        def recursiveRef(karg: RefinementType): Boolean = karg match {
          case DataRefinementType(_, refinename) =>
            refinename.exists(drn => drn == rn2 || go(visited = visited + rn, drn))
          case ListRefinementType(elementType,_) => recursiveRef(elementType)
          case SetRefinementType(elementType,_) => recursiveRef(elementType)
          case MapRefinementType(keyType, valueType,_) => recursiveRef(keyType) || recursiveRef(valueType)
          case _ => false
        }
        if (visited.contains(rn)) false
        else {
          val rndef = getURefinementDef(wrefinements, rn)
          rndef.conss.exists { case (_, kargss) =>
            kargss.exists { kargs =>
              kargs.exists(recursiveRef)
            }
          }
        }
      }
      go(Set(), rn1)
    }


    private
    def copyInType(currmemo: Map[Refinement, Refinement], currwrefinements: Map[Refinement, URefinementDef], rty: RefinementType):
      (Map[Refinement, Refinement], Map[Refinement, URefinementDef]) = {
      rty match {
        case DataRefinementType(dataname, refinename) =>
          refinename.fold((currmemo, currwrefinements)) { rn =>
            copyToWorkingRefinements(currmemo, currwrefinements, dataname, rn)
          }
        case ListRefinementType(elementType, _) => copyInType(currmemo, currwrefinements, elementType)
        case SetRefinementType(elementType, _) => copyInType(currmemo, currwrefinements, elementType)
        case MapRefinementType(keyType, valueType, _) =>
          val (memo1, wrefinements1) = copyInType(currmemo, currwrefinements, keyType)
          copyInType(memo1, wrefinements1, valueType)
        case _ => (currmemo, currwrefinements)
      }
    }

    private
    def copyToWorkingRefinements(memo: Map[Refinement, Refinement], wrefinements:  Map[Refinement, URefinementDef], dn: TypeName, rn: Refinement): (Map[Refinement, Refinement], Map[Refinement, URefinementDef]) = {
      if (wrefinements.contains(rn) || memo.contains(rn)) (memo, wrefinements)
      else {

        val newRn = refinements.newRefinement(dn)
        val rndef = toURefinementDef(refinements.definitions(rn))
        val newMemo = memo.updated(rn, newRn)
        val newWrefinements = wrefinements.updated(newRn, rndef)
        rndef.conss.values.toList.foldLeft((newMemo, newWrefinements)) { (st, kargss) =>
          kargss.foldLeft(st) { (st, kargs) =>
            kargs.foldLeft(st) { (st, rty) =>
              val (currmemo, currwrefinements) = st
              copyInType(currmemo, currwrefinements, rty)
            }
          }
        }
      }
    }

    private
    def applySubstRefs(wrefinements: Map[Refinement, URefinementDef], subst: Map[Refinement, Refinement]): Map[Refinement, URefinementDef] = {
      val substRefs = wrefinements.foldLeft (Map[Refinement, URefinementDef]()) { (prevRevs, df) =>
        val (kref, urefdef) = df
        val newKref = applySubst(kref, subst)
        val newConss = applySubstCons(urefdef.conss, subst)
        if (prevRevs.contains(newKref)) {
          val otherconss = prevRevs(newKref).conss
          val finalconss = (otherconss.keySet ++ newConss.keySet).map(k => k ->
            otherconss.getOrElse(k, Set()).union(newConss.getOrElse(k, Set()))
          ).toMap
          prevRevs.updated(newKref, URefinementDef(urefdef.baseDataType, finalconss))
        }
        else prevRevs.updated(newKref, URefinementDef(urefdef.baseDataType, newConss))
      }
      substRefs
    }

    private
    def applySubstCons(conss: Map[ConsName, Set[List[RefinementType]]], subst: Map[Refinement, Refinement]): Map[ConsName, Set[List[RefinementType]]] = {
      conss.mapValues(applySubstKargss(_, subst))
    }

    private
    def applySubstKargss(kargss: Set[List[RefinementType]], subst: Map[Refinement, Refinement]): Set[List[RefinementType]] = {
      kargss.map(applySubstKargs(_, subst))
    }

    private
    def applySubstKargs(kargs: List[RefinementType], subst: Map[Refinement, Refinement]) = {
      kargs.map(applySubstTy(_, subst))
    }

    def applySubst(rn: Refinement, subst: Map[Refinement, Refinement]): Refinement = { // Transitively apply substitions
      val newRn = subst.getOrElse(rn, rn)
      if (rn == newRn) rn
      else applySubst(newRn, subst)
    }

    private
    def applySubstTy(rty: RefinementType, subst: Map[Refinement, Refinement]): RefinementType = rty match {
      case DataRefinementType(dataname, refinename) =>
        DataRefinementType(dataname, refinename.map(rn => applySubst(rn, subst)))
      case ListRefinementType(elementType, length) => ListRefinementType(applySubstTy(elementType, subst), length)
      case SetRefinementType(elementType, cardinality) => SetRefinementType(applySubstTy(elementType, subst), cardinality)
      case MapRefinementType(keyType, valueType, size) => MapRefinementType(applySubstTy(keyType, subst), applySubstTy(valueType, subst), size)
      case _ => rty
    }

    private
    def applyNewSubst(prevsubst: Map[Refinement, Refinement], newsubst: Map[Refinement, Refinement])(implicit di: DummyImplicit, di2: DummyImplicit): Map[Refinement, Refinement] = {
      val res = newsubst ++ prevsubst.map { case (r1, r2) => r1 -> applySubst(r2, newsubst) }
      res
    }

    private
    def replaceRec(wrefinements: Map[Refinement, URefinementDef], dn: TypeName, prevRn: Refinement, newRn: Refinement): (URefinementDef, Map[Refinement, Refinement]) = {
      val prevRnDefs = getURefinementDef(wrefinements, prevRn)
      val newsubst = if (prevRnDefs.conss.size > 1) Map(prevRn -> newRn) else Map[Refinement, Refinement]()
      (prevRnDefs, newsubst)
    }


    private
    def addAllRefinements(newrefinements: List[(Refinement, RefinementDef)]): Map[Refinement, Option[Refinement]] = {
      def ensureUniqueAll(refs: List[(TypeName, Refinement)]): Map[Refinement, Option[Refinement]] = {
        refs match {
          case Nil => Map()
          case (dn, rn) :: rns =>
            val rnsrefs = rns.map(_._2).toSet
            val nrno = ensureUnique(dn, rn, rnsrefs)
            refinements.definitions.transform { case (_, rn2def) =>
              rn2def.copy(conss = rn2def.conss.transform((_, v) => v.map(substDataRefsInType(_, rn, nrno))))
            }
            ensureUniqueAll(rns).updated(rn, nrno)
        }
      }
      refinements.definitions ++= newrefinements
      ensureUniqueAll(newrefinements.map { case (rn, rndef) => (rndef.baseDataType, rn) })
    }

    override def widen(rty1: RefinementType, rty2: RefinementType, bound: Int): RefinementType = widenH(rty1, rty2, bound)

    private
    lazy val widenH: (RefinementType, RefinementType, Int) => RefinementType = memoized[RefinementType, RefinementType, Int, RefinementType](memocacheSize) {
      (rty1: RefinementType, rty2: RefinementType, bound: Int) =>
      def fixIC(resrt : RefinementType, icrefs: List[Refinement], wrefinements: Map[Refinement, URefinementDef]): (RefinementType, Map[Refinement, URefinementDef]) = {
        val res =
          if (icrefs.isEmpty) (resrt, wrefinements)
          else {
            val icref = icrefs.head
            val icrefsr = icrefs.tail
            if (wrefinements.contains(icref)) {
              val icrefdef = wrefinements(icref)
              val (newConss, shmerges, _) = icrefdef.conss.foldLeft(
                (Map[ConsName, Set[List[RefinementType]]](), ListMap[Refinement, (TypeName, Refinement, Refinement)](), Map[(RefinementType, RefinementType), RefinementType]())) { (st, kkargss) =>
                  val (prevConss, prevShmerges, prevMemo) = st
                  val (k, kargss) = kkargss
                  if (kargss.size > 1) {
                    val (newKargs, newShmerges, newMemo) = kargss.tail.foldLeft((kargss.head, prevShmerges, prevMemo)) { (st, kargs2) =>
                      val (kargs1, prevShmergesKs, prevMemoKs) = st
                      kargs1.zip(kargs2).foldLeft((List[RefinementType](), prevShmergesKs, prevMemoKs)) { (st, ka12) =>
                        val (prevKargs, prevShmergesK, prevMemoK) = st
                        val (ka1, ka2) = ka12
                        if (prevMemoK.contains((ka1, ka2))) (prevKargs :+ prevMemoK((ka1, ka2)), prevShmergesK, prevMemoK)
                        else {
                          val (newkarg, newShmerges) = shallowMerge(ka1, ka2)
                          (prevKargs :+ newkarg, prevShmergesK ++ newShmerges, prevMemoK.updated((ka1, ka2), newkarg))
                        }
                      }
                    }
                    (prevConss.updated(k, Set(newKargs)), newShmerges, newMemo)
                  } else (prevConss.updated(k, kargss), prevShmerges, prevMemo)
                }
              val newwrefinements = wrefinements.updated(icref, URefinementDef(icrefdef.baseDataType, newConss))
              val (finalsubst, finalicrefs, finalwrefinements) = shmerges.foldLeft((Map[Refinement,Refinement](), icrefsr, newwrefinements)) { (st, rop) =>
                val (prevSubst, prevIcrefs, prevwrefinements) = st
                val (newRn, (dn, rn1r, rn2r)) = rop
                val rn1 = applySubst(rn1r, prevSubst)
                val rn2 = applySubst(rn2r, prevSubst)
                val (subst, nicrefs, newwrefinements) = mergeP(prevwrefinements, dn, rn1, rn2, newRn)
                val finalsubst = applyNewSubst(prevSubst, subst)
                val resIcs = (prevIcrefs union nicrefs).map(applySubst(_, finalsubst))
                val finalRefinements = applySubstRefs(newwrefinements, finalsubst)
                (finalsubst, resIcs, finalRefinements)
              }
              val finalresrt = applySubstTy(resrt, finalsubst)
              fixIC(finalresrt, finalicrefs, finalwrefinements)
            } else fixIC(resrt, icrefsr, wrefinements)
          }
        res
      }

      def shallowMerge(rty1: RefinementType, rty2: RefinementType): (RefinementType, ListMap[Refinement, (TypeName, Refinement, Refinement)]) = {
        (rty1, rty2) match {
          case (_, NoRefinementType) => (rty1, ListMap.empty)
          case (NoRefinementType, _) => (rty2, ListMap.empty)
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntRefinementType(ival1), IntRefinementType(ival2)) => (BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.widen(ival1, ival2))), ListMap.empty)
              case (StringRefinementType, StringRefinementType) => (BaseRefinementType(StringRefinementType), ListMap.empty)
              case (_, _) => (ValueRefinementType, ListMap.empty)
            }
          case (ListRefinementType(irty1, length1), ListRefinementType(irty2, length2)) =>
            val (irtywid, shmerges) = shallowMerge(irty1, irty2)
            val length = Intervals.Positive.Lattice.widen(length1, length2)
            (ListRefinementType(irtywid, length), shmerges)
          case (SetRefinementType(irty1, cardinality1), SetRefinementType(irty2, cardinality2)) =>
            val (irtywid, shmerges) = shallowMerge(irty1, irty2)
            val cardinality = Intervals.Positive.Lattice.widen(cardinality1, cardinality2)
            (SetRefinementType(irtywid, cardinality), shmerges)
          case (MapRefinementType(krty1, vrty1, size1), MapRefinementType(krty2, vrty2, size2)) =>
            val size = Intervals.Positive.Lattice.widen(size1, size2)
            // Small optimization
            if (krty1 == vrty1 && krty2 == vrty2) {
              val (irtywid, shmerges) = shallowMerge(krty1, krty2)
              (MapRefinementType(irtywid, irtywid, size), shmerges)
            } else {
              val (krtywid, shmerges1) = shallowMerge(krty1, krty2)
              val (vrtywid, shmerges2) = shallowMerge(vrty1, vrty2)
              (MapRefinementType(krtywid, vrtywid, size), shmerges1 ++ shmerges2)
            }
          case (DataRefinementType(dn1, rno1), DataRefinementType(dn2, rno2)) if dn1 == dn2 =>
            if (rno1.isEmpty || rno2.isEmpty) (DataRefinementType(dn1, None), ListMap.empty)
            else {
              val rn1 = rno1.get
              val rn2 = rno2.get
              val newRn = refinements.newRefinement(dn1)
              (DataRefinementType(dn1, Some(newRn)), ListMap(newRn -> (dn1, rn1, rn2)))
            }
          case _ => (ValueRefinementType, ListMap.empty)
        }
      }

      def mergeP(wrefinements: Map[Refinement, URefinementDef],
                 dn: TypeName, rn1: Refinement, rn2: Refinement, newRn: Refinement): (Map[Refinement, Refinement], List[Refinement], Map[Refinement, URefinementDef]) = {
          val (rn1defs, subst1) = replaceRec(wrefinements, dn, rn1, newRn)
          val (rn2defs, subst2)  = replaceRec(wrefinements, dn, rn2, newRn)
          val newRnDefsCons = rn1defs.conss.keySet union rn2defs.conss.keySet
          val newRnDefs = newRnDefsCons.map(k => k ->
                              rn1defs.conss.getOrElse(k, Set()).union(rn2defs.conss.getOrElse(k, Set()))).toMap
          val finalwrefinements = applySubstRefs(wrefinements.updated(newRn, URefinementDef(dn, newRnDefs)), subst1 ++ subst2)
          (subst1 ++ subst2, List(newRn), finalwrefinements)
      }

      // Returns new refinement type, substitution, set of possibly inconsistent refinements, and an updated local refinement map
      def merge(wrefinements: Map[Refinement, URefinementDef],
                rty1: RefinementType, rty2: RefinementType): (RefinementType, Map[Refinement, Refinement], List[Refinement], Map[Refinement, URefinementDef]) = {
        (rty1, rty2) match {
          case (_, NoRefinementType) => (rty1, Map(), List(), wrefinements)
          case (NoRefinementType, _) => (rty2, Map(), List(), wrefinements)
          case (BaseRefinementType(bty1), BaseRefinementType(bty2)) =>
            (bty1, bty2) match {
              case (IntRefinementType(ival1), IntRefinementType(ival2)) =>
                (BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.widen(ival1, ival2))), Map(), List(), wrefinements)
              case (StringRefinementType, StringRefinementType) => (BaseRefinementType(StringRefinementType), Map(), List(), wrefinements)
              case (_, _) => (ValueRefinementType, Map(), List(), wrefinements)
            }
          case (ListRefinementType(irty1, length1), ListRefinementType(irty2, length2)) =>
            val (irtywid, subst, icrefs, nwrefinements) = merge(wrefinements, irty1, irty2)
            (ListRefinementType(irtywid, Intervals.Positive.Lattice.widen(length1, length2)), subst, icrefs, nwrefinements)
          case (SetRefinementType(irty1, cardinality1), SetRefinementType(irty2, cardinality2)) =>
            val (irtywid, subst, icrefs, nwrefinements) = merge(wrefinements, irty1, irty2)
            (SetRefinementType(irtywid, Intervals.Positive.Lattice.widen(cardinality1, cardinality2)), subst, icrefs, nwrefinements)
          case (MapRefinementType(krty1, vrty1, size1), MapRefinementType(krty2, vrty2, size2)) =>
            // Small optimization
            val size = Intervals.Positive.Lattice.widen(size1, size2)
            if (krty1 == vrty1 && krty2 == vrty2) {
              val (irtywid, subst, icrefs, nwrefinements) = merge(wrefinements, krty1, krty2)
              (MapRefinementType(irtywid, irtywid, size), subst, icrefs, nwrefinements)
            } else {
              val (krtylub, subst1, icrefs1, nwrefinements1) = merge(wrefinements, krty1, krty2)
              val (vrtylub, subst2, icrefs2, nwrefinements2) = merge(nwrefinements1, vrty1, vrty2)
              (MapRefinementType(krtylub, vrtylub, size), subst1 ++ subst2, icrefs1 ++ icrefs2, nwrefinements2)
            }
          case (DataRefinementType(dn1, rno1), DataRefinementType(dn2, rno2)) if dn1 == dn2 =>
            if (rno1.isEmpty || rno2.isEmpty) (DataRefinementType(dn1, None), Map(), List(), wrefinements)
            else {
              val rn1 = rno1.get
              val rn2 = rno2.get
              if (rn1 == rn2) (DataRefinementType(dn1, Some(rn1)), Map(), List(), wrefinements) // No need to complicate things
              else {
                val newRn = refinements.newRefinement(dn1)
                val (subst, icrefs, newWrefinements) = mergeP(wrefinements, dn1, rn1, rn2, newRn)
                (DataRefinementType(dn1, Some(applySubst(newRn, subst))), subst, icrefs, newWrefinements)
              }
            }
          case _ => (ValueRefinementType, Map(), List(), wrefinements)
        }
      }

      def copyRelevantRefinements(rty1: RefinementType, rty2: RefinementType) = {
        val (memo1, wrefinements1) = copyInType(Map(), Map(), rty1)
        val (memo2, wrefinements2) = copyInType(memo1, applySubstRefs(wrefinements1, memo1), rty2)
        (applySubstTy(rty1,memo2), applySubstTy(rty2, memo2), applySubstRefs(wrefinements2, memo2))
      }

      val (nrty1, nrty2, copiedRefinements) = copyRelevantRefinements(rty1, rty2)
      val (newrt, _, icrefs, newRefinements) = merge(copiedRefinements, nrty1, nrty2)
      val (resrt, finalRefinements) = fixIC(newrt, icrefs, newRefinements)
      // TODO Smarter add to global
      val addedTys = addAllRefinements(finalRefinements.transform((_, urdef) => RefinementDef(urdef.baseDataType, urdef.conss.mapValues(_.head))).toList)
      addedTys.foldLeft(resrt) { (resrt, subst) =>
        substDataRefsInType(resrt, subst._1, subst._2)
      }
    }
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