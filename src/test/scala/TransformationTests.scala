import org.scalatest.{FlatSpec, Matchers}
import semantics.Executor
import syntax._
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 01/03/2017.
  */
class TransformationTests extends FlatSpec with Matchers {
  "The expression simplification procedure in Expr.rscli" should "pass all its tests correctly" in {
    val modExprO = RascalWrapper.loadModuleFromFile(getClass.getResource("Expr.rscli").getFile)
    val modExprExecRes = modExprO.flatMap(Executor.execute)
    modExprExecRes shouldBe a [\/-[_]]
    modExprExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The negation normal form transformation in NNF.rscli" should "pass all its tests correctly" in {
    val modNNFO = RascalWrapper.loadModuleFromFile(getClass.getResource("NNF.rscli").getFile)
    val modNNFExecRes = modNNFO.flatMap(Executor.execute)
    modNNFExecRes shouldBe a [\/-[_]]
    modNNFExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The rename field refactoring in RenameField.rscli" should "pass all its tests correctly" in {
    val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("RenameField.rscli").getFile)
    val modRFExecRes = modRFO.flatMap(Executor.execute)
    modRFExecRes shouldBe a [\/-[_]]
    modRFExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The extract superclass refactoring in ExtractSuperclass.rscli" should "pass all its tests correctly" in {
    val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("ExtractSuperclass.rscli").getFile)
    val modESExecRes = modESO.flatMap(Executor.execute)
    modESExecRes shouldBe a [\/-[_]]
    modESExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The replace delegation with inheritance refactoring in ReplaceDelegation.rscli" should "pass all its tests correctly" in {
    val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("ReplaceDelegation.rscli").getFile)
    val modESExecRes = modESO.flatMap(Executor.execute)
    modESExecRes shouldBe a [\/-[_]]
    modESExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }
}
