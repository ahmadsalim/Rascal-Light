package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class MiniConfigEvaluation extends Evaluation("mini-config-evaluation") {

  "The modernization transformation in MiniConfigMod.rsc" should "run correctly with the abstract type executor" in {
    forAll(configs) { (refinement, memowidening) =>
      val modMCM = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniConfigMod.rsc").getFile)
      val modMCMExecRes = modMCM.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "modernize",
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modMCMExecRes shouldBe a[\/-[_]]
      modMCMExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Expression"), Some(memoinfo), Some(duration))
      }
    }
  }

}
