package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class DesugarOberonEvaluation extends Evaluation("desugar-oberon-evaluation") {
  "The desugaring in DesugarOberonSimpl.rsc" should "run correctly with the abstract type executor" in {
    forAll(configs) { (refinement, memowidening) =>
      val modDSOb = RascalWrapper.loadModuleFromFile(getClass.getResource("/DesugarOberonSimpl.rsc").getFile)
      val modDSObExecRes = modDSOb.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "desugar",
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modDSObExecRes shouldBe a[\/-[_]]
      modDSObExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Module"), Some(memoinfo), Some(duration))
      }
    }
  }
}
