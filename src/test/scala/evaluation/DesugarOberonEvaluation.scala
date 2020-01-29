package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class DesugarOberonEvaluation extends Evaluation("desugar-oberon-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The desugaring in DesugarOberonSimpl.rsc" should
      s"run correctly with the abstract type executor using $confname" in {
      val modDSOb = RascalWrapper.loadModuleFromFile(getClass.getResource("/DesugarOberonSimpl.rsc").getFile)
      val modDSObExecRes = modDSOb.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "desugar",
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modDSObExecRes shouldBe a[\/-[_]]
      modDSObExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Module"), Some(memoinfo), Some(duration), confname)
      }
    }
  }
}
