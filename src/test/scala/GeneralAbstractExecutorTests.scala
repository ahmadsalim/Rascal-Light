import helper.AbstractExecutorTests
import semantics.AbstractRefinementTypeExecutor
import syntax._
import util.rascalwrapper.RascalWrapper
import scalaz.\/-

class GeneralAbstractExecutorTests extends AbstractExecutorTests("test") {
    "The expression simplification procedure in Expr.rsc" should "run correctly with the abstract type executor" in {
      val modExprO = RascalWrapper.loadModuleFromFile(getClass.getResource("Expr.rsc").getFile)
      val modExprExecRes = modExprO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "simplify")
      }
      modExprExecRes shouldBe a [\/-[_]]
      modExprExecRes.foreach { case (module, refinements, tmems, _, _) =>
        memsOK(module, refinements, tmems, DataType("Expr"))
      }
    }

    "The extract superclass refactoring in ExtractSuperclass.rsc" should "run correctly with the abstract type executor" in {
      val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("unported/ExtractSuperclass.rsc").getFile)
      val modESExecRes = modESO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "extractSuperclass")
      }
      modESExecRes shouldBe a [\/-[_]]
      modESExecRes.foreach { case (module, refinements, tmems, _, _) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The replace delegation with inheritance refactoring in ReplaceDelegation.rsc" should "run correctly with the abstract type executor" in {
      val modRDO = RascalWrapper.loadModuleFromFile(getClass.getResource("unported/ReplaceDelegation.rsc").getFile)
      val modRDExecRes = modRDO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "replaceDelegationWithInheritance")
      }
      modRDExecRes shouldBe a [\/-[_]]
      modRDExecRes.foreach { case (module, refinements, tmems, _, _) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The simplification procedure in SimplifyTableau.rsc" should "run correctly with the abstract type executor" in {
      val modSTab = RascalWrapper.loadModuleFromFile(getClass.getResource("unported/SimplifyTableau.rsc").getFile)
      val modSTabExecRes = modSTab.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "simplify")
      }
      modSTabExecRes shouldBe a [\/-[_]]
      modSTabExecRes.foreach { case (module, refinements, tmems, _, _) =>
        memsOK(module, refinements, tmems, DataType("Tableau"))
      }
    }

    "The even list calculation procedure in IntProgs.rsc" should "run currectly with the abstract type executor" in {
      val modIntP = RascalWrapper.loadModuleFromFile(getClass.getResource("IntProgs.rsc").getFile)
      val modIntPExecRes = modIntP.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "evenedout")
      }
      modIntPExecRes shouldBe a [\/-[_]]
      modIntPExecRes.foreach { case (module, refinements, tmems, _, _) =>
        memsOK(module, refinements, tmems, ListType(BaseType(IntType)))
      }
    }
}