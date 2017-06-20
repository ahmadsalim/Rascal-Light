import org.scalatest.{FlatSpec, Matchers}
import semantics.AbstractTypeExecutor
import semantics.domains.abstracting.{TypeMemories, TypeMemory}
import semantics.domains.common
import semantics.domains.common._
import syntax.{DataType, Type}
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 20/06/2017.
  */
class TypeExecutorTests extends FlatSpec with Matchers {

  private
  def memsOK(mems: TypeMemories[Type], targetType: Type): Unit = {
    mems.memories.exists { case TypeMemory(res, _) =>
      res match {
        case SuccessResult(_) => true
        case _ => false
      }
    } shouldBe true
    mems.memories.foreach { case TypeMemory(res, _) => res match {
        case SuccessResult(restype) => restype shouldBe targetType
        case ExceptionalResult(_) => false
      }
    }
    mems.memories.foreach { case TypeMemory(res, _) =>
        res match {
          case ExceptionalResult(Error(kinds)) =>
            kinds.foreach {
              _ shouldBe a [ReconstructError]
            }
          case _ =>
        }
    }
  }

  "The expression simplification procedure in Expr.rscli" should "run correctly with the abstract type executor" in {
    val modExprO = RascalWrapper.loadModuleFromFile(getClass.getResource("Expr.rscli").getFile)
    val modExprExecRes = modExprO.flatMap { moddef =>
      AbstractTypeExecutor.execute(moddef, "simplify")
    }
    modExprExecRes shouldBe a [\/-[_]]
    modExprExecRes.foreach { tmems =>
      memsOK(tmems, DataType("Expr"))
    }
  }

  "The negation normal form transformation in NNF.rscli" should "run correctly with the abstract type executor" in {
    val modNnfO = RascalWrapper.loadModuleFromFile(getClass.getResource("NNF.rscli").getFile)
    val modNnfExecRes = modNnfO.flatMap { moddef =>
      AbstractTypeExecutor.execute(moddef, "nnf")
    }
    modNnfExecRes shouldBe a [\/-[_]]
    modNnfExecRes.foreach { tmems =>
      memsOK(tmems, DataType("Formula"))
    }
  }

  "The rename field refactoring in RenameField.rscli" should "run correctly with the abstract type executor" in {
    val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("RenameField.rscli").getFile)
    val modRFExecRes = modRFO.flatMap { moddef =>
      AbstractTypeExecutor.execute(moddef, "renameField")
    }
    modRFExecRes shouldBe a [\/-[_]]
    modRFExecRes.foreach { tmems =>
      memsOK(tmems, DataType("Package"))
    }
  }

  "The extract superclass refactoring in ExtractSuperclass.rscli" should "run correctly with the abstract type executor" in {
    val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("ExtractSuperclass.rscli").getFile)
    val modESExecRes = modESO.flatMap { moddef =>
      AbstractTypeExecutor.execute(moddef, "extractSuperclass")
    }
    modESExecRes shouldBe a [\/-[_]]
    modESExecRes.foreach { tmems =>
      memsOK(tmems, DataType("Package"))
    }
  }

  "The replace delegation with inheritance refactoring in ReplaceDelegation.rscli" should "run correctly with the abstract type executor" in {
    val modRDO = RascalWrapper.loadModuleFromFile(getClass.getResource("ReplaceDelegation.rscli").getFile)
    val modRDExecRes = modRDO.flatMap { moddef =>
      AbstractTypeExecutor.execute(moddef, "replaceDelegationWithInheritance")
    }
    modRDExecRes shouldBe a [\/-[_]]
    modRDExecRes.foreach { tmems =>
      memsOK(tmems, DataType("Package"))
    }
  }
}
