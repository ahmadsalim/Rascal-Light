import org.scalatest.{FlatSpec, Matchers}
import semantics.domains.abstracting._
import semantics.domains.common.Lattice
import syntax.{ConsName, DataType, Type, TypeName}

/**
  * Created by asal on 18/08/2017.
  */
class VoideableRefinementTypeWideningTests extends FlatSpec with Matchers {
  "Cousot example: iteration #1" should "widen correctly" in {
    val datatypes: Map[TypeName, Map[ConsName, List[Type]]] =
      Map("content" -> Map("Zero" -> List(), "A" -> List(DataType("content")), "B" -> List(DataType("content")), "C" -> List(DataType("content")))
         , "list" -> Map("Nil" -> List(), "Cons" -> List(DataType("content"), DataType("list"))))
    val ZeroRef = new Refinement("Zero")
    val NilRef = new Refinement("Nil")
    val AZeroRef = new Refinement("AZero")
    val BZeroRef = new Refinement("BZero")
    val CZeroRef = new Refinement("CZero")
    val X1Ref = new Refinement("X1")
    val X2Ref = new Refinement("X2")
    val X3Ref = new Refinement("X3")
    val NX1Ref = new Refinement("NX1")
    val NX2Ref = new Refinement("NX2")
    val NX3Ref = new Refinement("NX3")
    val RXRef = new Refinement("RX")
    val RARef = new Refinement("RA")
    val RBRef = new Refinement("RB")
    val RCRef = new Refinement("RC")
    val RDRef = new Refinement("RD")
    val RERef = new Refinement("RE")
    val initialRefs: Map[Refinement, RefinementDef] =
      Map( ZeroRef -> RefinementDef("content", Map("Zero" -> List()))
         , NilRef ->  RefinementDef("list", Map("Nil" -> List()))
         , AZeroRef -> RefinementDef("content", Map("A" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , BZeroRef -> RefinementDef("content", Map("B" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , CZeroRef -> RefinementDef("content", Map("C" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , X1Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(ZeroRef)), DataRefinementType("list", Some(X2Ref)))))
         , X2Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(ZeroRef)), DataRefinementType("list", Some(X3Ref)))))
         , X3Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(ZeroRef)), DataRefinementType("list", Some(NilRef)))))
         , NX1Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(AZeroRef)), DataRefinementType("list", Some(NX2Ref)))))
         , NX2Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(BZeroRef)), DataRefinementType("list", Some(NX3Ref)))))
         , NX3Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(CZeroRef)), DataRefinementType("list", Some(NilRef)))))
         , RXRef -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(RARef)), DataRefinementType("list", Some(RBRef)))))
         , RARef -> RefinementDef("content", Map("Zero" -> List(), "A" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , RBRef -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(RCRef)), DataRefinementType("list", Some(RDRef)))))
         , RCRef -> RefinementDef("content", Map("Zero" -> List(), "B" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , RDRef -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(RERef)), DataRefinementType("list", Some(NilRef)))))
         , RERef -> RefinementDef("content",  Map("Zero" -> List(), "C" -> List(DataRefinementType("content", Some(ZeroRef)))))
      )
    val refinements = new Refinements(initialRefs)
    val RTOS = RefinementTypeOps(datatypes, refinements)
    import RTOS._
    val wrty = Lattice[VoideableRefinementType].widen(
      VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(X1Ref))),
      VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(NX1Ref))))
    Lattice[VoideableRefinementType].===(wrty, VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(RXRef)))) shouldBe true
  }

  "Cousot example: iteration #2" should "widen correctly" in {
    val datatypes: Map[TypeName, Map[ConsName, List[Type]]] =
      Map("content" -> Map("Zero" -> List(), "A" -> List(DataType("content")), "B" -> List(DataType("content")), "C" -> List(DataType("content")))
        , "list" -> Map("Nil" -> List(), "Cons" -> List(DataType("content"), DataType("list"))))
    val ZeroRef = new Refinement("Zero")
    val NilRef = new Refinement("Nil")
    val AZeroRef = new Refinement("AZero")
    val AZZRef = new Refinement("AZZ")
    val BZZRef = new Refinement("BZZ")
    val CZZRef = new Refinement("CZZ")
    val AARef = new Refinement("AA")
    val BBRef = new Refinement("BB")
    val CCRef = new Refinement("CC")
    val BZeroRef = new Refinement("BZero")
    val CZeroRef = new Refinement("CZero")
    val X1Ref = new Refinement("X1")
    val X2Ref = new Refinement("X2")
    val X3Ref = new Refinement("X3")
    val NX1Ref = new Refinement("NX1")
    val NX2Ref = new Refinement("NX2")
    val NX3Ref = new Refinement("NX3")
    val NNX1Ref = new Refinement("NNX1")
    val NNX2Ref = new Refinement("NNX2")
    val NNX3Ref = new Refinement("NNX3")
    val RX1Ref = new Refinement("RX1")
    val RX2Ref = new Refinement("RX2")
    val RX3Ref = new Refinement("RX3")
    val RARef = new Refinement("RA")
    val RBRef = new Refinement("RB")
    val RCRef = new Refinement("RC")
    val initialRefs: Map[Refinement, RefinementDef] =
      Map( ZeroRef -> RefinementDef("content", Map("Zero" -> List()))
         , NilRef ->  RefinementDef("list", Map("Nil" -> List()))
         , AZeroRef -> RefinementDef("content", Map("A" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , BZeroRef -> RefinementDef("content", Map("B" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , CZeroRef -> RefinementDef("content", Map("C" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , AZZRef -> RefinementDef("content", Map("Zero" -> List(), "A" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , BZZRef -> RefinementDef("content", Map("Zero" -> List(), "B" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , CZZRef -> RefinementDef("content", Map("Zero" -> List(), "C" -> List(DataRefinementType("content", Some(ZeroRef)))))
         , AARef -> RefinementDef("content", Map("A" -> List(DataRefinementType("content", Some(AZZRef)))))
         , BBRef -> RefinementDef("content", Map("B" -> List(DataRefinementType("content", Some(BZZRef)))))
         , CCRef -> RefinementDef("content", Map("C" -> List(DataRefinementType("content", Some(CZZRef)))))
         , X1Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(ZeroRef)), DataRefinementType("list", Some(X2Ref)))))
         , X2Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(ZeroRef)), DataRefinementType("list", Some(X3Ref)))))
         , X3Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(ZeroRef)), DataRefinementType("list", Some(NilRef)))))
         , NX1Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(AARef)), DataRefinementType("list", Some(NX2Ref)))))
         , NX2Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(BBRef)), DataRefinementType("list", Some(NX3Ref)))))
         , NX3Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(CCRef)), DataRefinementType("list", Some(NilRef)))))
         , NNX1Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(AZZRef)), DataRefinementType("list", Some(NNX2Ref)))))
         , NNX2Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(BZZRef)), DataRefinementType("list", Some(NNX3Ref)))))
         , NNX3Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(CZZRef)), DataRefinementType("list", Some(NilRef)))))
         , RX1Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(RARef)), DataRefinementType("list", Some(RX2Ref)))))
         , RX2Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(RBRef)), DataRefinementType("list", Some(RX3Ref)))))
         , RX3Ref -> RefinementDef("list", Map("Cons" -> List(DataRefinementType("content", Some(RCRef)), DataRefinementType("list", Some(NilRef)))))
         , RARef -> RefinementDef("content", Map("Zero" -> List(), "A" -> List(DataRefinementType("content", Some(RARef)))))
         , RBRef -> RefinementDef("content", Map("Zero" -> List(), "B" -> List(DataRefinementType("content", Some(RBRef)))))
         , RCRef -> RefinementDef("content", Map("Zero" -> List(), "C" -> List(DataRefinementType("content", Some(RCRef)))))
      )
    val refinements = new Refinements(initialRefs)
    val RTOS = RefinementTypeOps(datatypes, refinements)
    import RTOS._
    val wrty = Lattice[VoideableRefinementType].widen(
      Lattice[VoideableRefinementType].widen(
        VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(X1Ref))),
        VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(NX1Ref)))),
        VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(NNX1Ref))))
    Lattice[VoideableRefinementType].===(wrty, VoideableRefinementType(possiblyVoid = false, DataRefinementType("list", Some(RX1Ref)))) shouldBe true
  }
}
