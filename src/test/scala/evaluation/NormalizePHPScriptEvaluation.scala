package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting._
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class NormalizePHPScriptEvaluation extends Evaluation("normalize-php-script-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The normalize PHP script function in NormalizePHPScript.rsc" should
    s"run correctly with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/NormalizePHPScript.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "normalizeScript",
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Script"), Some(memoinfo), Some(duration), confname)
      }
    }
  }
}
