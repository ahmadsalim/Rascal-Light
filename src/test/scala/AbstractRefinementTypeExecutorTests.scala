import org.scalatest.{FlatSpec, Matchers}
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting._
import semantics.domains.common._
import semantics.typing.AbstractTyping
import syntax.{DataType, StringType, Type}
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 20/06/2017.
  */
class AbstractRefinementTypeExecutorTests extends FlatSpec with Matchers {

  private
  def memsOK(module: Module, refinements: Refinements, mems: TypeMemories[VoideableRefinementType], targetType: Type): Unit = {
    println("=" * 100)
    refinements.prettyDefs.foreach(println)
    mems.memories.foreach(println)
    println("=" * 100)
    val atyping = AbstractTyping(module)
    mems.memories.exists { case TypeMemory(res, _) =>
      res match {
        case SuccessResult(_) => true
        case _ => false
      }
    } shouldBe true
    mems.memories.foreach { case TypeMemory(res, _) => res match {
        case SuccessResult(restype) =>
          //restype.possiblyVoid shouldBe false
          atyping.inferType(restype.refinementType) shouldBe targetType
        case ExceptionalResult(exres) =>  exres shouldNot be (an [Error])
      }
    }
  }

  "The expression simplification procedure in Expr.rscli" should "run correctly with the abstract type executor" in {
    val modExprO = RascalWrapper.loadModuleFromFile(getClass.getResource("Expr.rscli").getFile)
    val modExprExecRes = modExprO.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "simplify")
    }
    modExprExecRes shouldBe a [\/-[_]]
    modExprExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Expr"))
    }
  }

  "The negation normal form transformation in NNF.rscli" should "run correctly with the abstract type executor" in {
    val modNnfO = RascalWrapper.loadModuleFromFile(getClass.getResource("NNF.rscli").getFile)
    val modNnfExecRes = modNnfO.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "nnf")
    }
    modNnfExecRes shouldBe a [\/-[_]]
    modNnfExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Formula"))
    }
  }
  /*

    "The rename field refactoring in RenameField.rscli" should "run correctly with the abstract type executor" in {
      val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("RenameField.rscli").getFile)
      val modRFExecRes = modRFO.flatMap { moddef =>
        val ofnrn = new Refinement("Nominal#ofn")
        val nfnrn = new Refinement("Nominal#nfn")
        val initialRefinements: Refinements =
          new Refinements(Map(ofnrn -> RefinementDef("Nominal", Map("ofn" -> List())),
                               nfnrn -> RefinementDef("Nominal", Map("nfn" -> List()))))
        val initialStore =
          TypeStoreV(Map(
            "pkg" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Package", None)),
            "cl" -> VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringType)),
            "oldFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Nominal", Some(ofnrn))),
            "newFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Nominal", Some(nfnrn)))
          ))
        AbstractRefinementTypeExecutor.execute(moddef, "renameField")
      }
      modRFExecRes shouldBe a [\/-[_]]
      modRFExecRes.foreach {  case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The extract superclass refactoring in ExtractSuperclass.rscli" should "run correctly with the abstract type executor" in {
      val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("ExtractSuperclass.rscli").getFile)
      val modESExecRes = modESO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "extractSuperclass")
      }
      modESExecRes shouldBe a [\/-[_]]
      modESExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The replace delegation with inheritance refactoring in ReplaceDelegation.rscli" should "run correctly with the abstract type executor" in {
      val modRDO = RascalWrapper.loadModuleFromFile(getClass.getResource("ReplaceDelegation.rscli").getFile)
      val modRDExecRes = modRDO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "replaceDelegationWithInheritance")
      }
      modRDExecRes shouldBe a [\/-[_]]
      modRDExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The simplification procedure in SimplifyTableau.rscli" should "run correctly with the abstract type executor" in {
      val modSTab = RascalWrapper.loadModuleFromFile(getClass.getResource("SimplifyTableau.rscli").getFile)
      val modSTabExecRes = modSTab.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "simplify")
      }
      modSTabExecRes shouldBe a [\/-[_]]
      modSTabExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Tableau"))
      }
    }
    "The desugaring in DesugarOberon.rscli" should "run correctly with the abstract type executor" in {
      val modDSOb = RascalWrapper.loadModuleFromFile(getClass.getResource("DesugarOberon.rscli").getFile)
      val modDSObExecRes = modDSOb.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "desugar")
      }
      modDSObExecRes shouldBe a [\/-[_]]
      modDSObExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Module"))
      }
    }

    "The statement translation in Glagol2PHP.rscli" should "run correctly with the abstract type executor" in {
      val modG2P = RascalWrapper.loadModuleFromFile(getClass.getResource("Glagol2PHP.rscli").getFile)
      val modG2PExecRes = modG2P.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "toPhpStmt")
      }
      modG2PExecRes shouldBe a [\/-[_]]
      modG2PExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("PhpName"))
      }
    }
    */
}