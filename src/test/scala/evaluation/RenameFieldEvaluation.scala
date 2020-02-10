package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting._
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class RenameFieldEvaluation extends Evaluation("rename-field-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The rename field refactoring in RenameStructField.rsc" should
    s"run correctly with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/RenameStructField.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val ofnrn = new Refinement("FieldNominal#ofn")
        val nfnrn = new Refinement("FieldNominal#nfn")
        val initialRefinements: Refinements =
          new Refinements(Map(ofnrn -> RefinementDef("FieldNominal#ofn", Map("ofn" -> List())),
            nfnrn -> RefinementDef("FieldNominal#nfn", Map("nfn" -> List()))))
        val initialStore =
          TypeStoreV(Map(
            "pkg" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Package", None)),
            "st" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("StructNominal", None)),
            "oldFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("FieldNominal", Some(ofnrn))),
            "newFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("FieldNominal", Some(nfnrn)))
          ))
        AbstractRefinementTypeExecutor.execute(moddef, "renameField", initialStore = Some(initialStore),
          initialRefinements = initialRefinements, refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Package"), Some(memoinfo), Some(duration), confname)
      }
    }
  }
}
