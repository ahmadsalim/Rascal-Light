package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting._
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class RenameFieldEvaulation extends Evaluation("rename-field-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    "The rename field refactoring in RenameStructField.rsc" should
    s"run correctly with the abstract type executor using ${Evaluation.refinementWideningName(refinement, memowidening)}" in {
      val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("/RenameStructField.rsc").getFile)
      val modRFExecRes = modRFO.flatMap { moddef =>
        val ofnrn = new Refinement("Nominal#ofn")
        val nfnrn = new Refinement("Nominal#nfn")
        val initialRefinements: Refinements =
          new Refinements(Map(ofnrn -> RefinementDef("Nominal#ofn", Map("ofn" -> List())),
            nfnrn -> RefinementDef("Nominal#nfn", Map("nfn" -> List()))))
        val initialStore =
          TypeStoreV(Map(
            "pkg" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Package", None)),
            "st" -> VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType)),
            "oldFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Nominal", Some(ofnrn))),
            "newFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Nominal", Some(nfnrn)))
          ))
        AbstractRefinementTypeExecutor.execute(moddef, "renameField", initialStore = Some(initialStore),
          initialRefinements = initialRefinements, refinedMatches = refinement, memoWidening = memowidening)
      }
      modRFExecRes shouldBe a[\/-[_]]
      modRFExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Package"), Some(memoinfo), Some(duration))
      }
    }
  }
}
