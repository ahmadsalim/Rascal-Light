import org.scalatest.{FlatSpec, Matchers}
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting.RefinementTypes.RefinementDefs
import semantics.domains.abstracting.{RefinementTypes, TypeMemories, TypeMemory, VoideableRefinementType}
import semantics.domains.common._
import semantics.typing.AbstractTyping
import syntax.{DataType, Type}
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 20/06/2017.
  */
class AbstractRefinementTypeExecutorTests extends FlatSpec with Matchers {

  private
  def memsOK(module: Module, refinements: RefinementDefs, mems: TypeMemories[VoideableRefinementType], targetType: Type): Unit = {
    println("=" * 100)
    RefinementTypes.prettyDefs(refinements).foreach(println)
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
          restype.possiblyVoid shouldBe false
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

  "The rename field refactoring in RenameField.rscli" should "run correctly with the abstract type executor" in {
    val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("RenameField.rscli").getFile)
    val modRFExecRes = modRFO.flatMap { moddef =>
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
}