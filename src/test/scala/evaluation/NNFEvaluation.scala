package evaluation

import scalaz.\/-
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator}
import semantics.domains.abstracting.{RefinementTypeOps, Refinements, TypeStoreV, VoideableRefinementType}
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class NNFEvaluation extends Evaluation("nnf-evaluation") {

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The negation normal form transformation in NNF.rsc" should
    s"run correctly with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/NNF.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val transmodule = ModuleTranslator.translateModule(moddef)
        transmodule shouldBe a[\/-[_]]
        val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
          mtr => {
            mtr.semmod.datatypes.transform((_, conss) =>
              mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
          })
        val initialRefinements = new Refinements(Map())
        val rtops = RefinementTypeOps(datatypes, initialRefinements)
        val ordinaryFormula = rtops.excluding("Formula", Set("begin"))
        val initialStore = TypeStoreV(Map("phi" -> VoideableRefinementType(possiblyVoid = false, ordinaryFormula)))
        AbstractRefinementTypeExecutor.execute(moddef, "nnf",
          initialStore = Some(initialStore), initialRefinements = initialRefinements, memoWidening = memowidening,
          refinedMatches = refinement)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Formula"), Some(memoinfo), Some(duration), confname)
      }
    }
  }
}
