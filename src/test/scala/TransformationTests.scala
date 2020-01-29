import org.scalatest.{FlatSpec, Matchers}
import semantics.ConcreteExecutor
import syntax._
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 01/03/2017.
  */
class TransformationTests extends FlatSpec with Matchers {
  "The expression simplification procedure in Expr.rsc" should "pass all its tests correctly" in {
    val modExprO = RascalWrapper.loadModuleFromFile(getClass.getResource("Expr.rsc").getFile)
    val modExprExecRes = modExprO.flatMap(ConcreteExecutor.execute)
    modExprExecRes shouldBe a [\/-[_]]
    modExprExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The negation normal form transformation in NNF.rsc" should "pass all its tests correctly" in {
    val modNNFO = RascalWrapper.loadModuleFromFile(getClass.getResource("NNF.rsc").getFile)
    val modNNFExecRes = modNNFO.flatMap(ConcreteExecutor.execute)
    modNNFExecRes shouldBe a [\/-[_]]
    modNNFExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The rename field refactoring in RenameField.rsc" should "pass all its tests correctly" in {
    val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("original/RenameField.rsc").getFile)
    val modRFExecRes = modRFO.flatMap(ConcreteExecutor.execute)
    modRFExecRes shouldBe a [\/-[_]]
    modRFExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The extract superclass refactoring in ExtractSuperclass.rsc" should "pass all its tests correctly" in {
    val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("unported/ExtractSuperclass.rsc").getFile)
    val modESExecRes = modESO.flatMap(ConcreteExecutor.execute)
    modESExecRes shouldBe a [\/-[_]]
    modESExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }

  "The replace delegation with inheritance refactoring in ReplaceDelegation.rsc" should "pass all its tests correctly" in {
    val modRDO = RascalWrapper.loadModuleFromFile(getClass.getResource("unported/ReplaceDelegation.rsc").getFile)
    val modRDExecRes = modRDO.flatMap(ConcreteExecutor.execute)
    modRDExecRes shouldBe a [\/-[_]]
    modRDExecRes.foreach { execres =>
      execres.failingTests shouldBe empty
    }
  }
}
