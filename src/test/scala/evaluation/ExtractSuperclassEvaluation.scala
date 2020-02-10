package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting._
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class ExtractSuperclassEvaluation extends Evaluation("extract-superclass-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The extract superclass refactoring in ExtractSuperclass.rsc" should
    s"run correctly with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/ExtractSuperclass.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val cnosupername = new Refinement("Maybeclassnominal#cnosuper")
        val cl1name = new Refinement("ClassNominal#cl1name")
        val cl2name = new Refinement("ClassNominal#cl2name")
        val csupername = new Refinement("Maybeclassnominal#csuper")
        val cl1fnref = new Refinement("FieldNominal#cl1fn")
        val cl2fnref = new Refinement("FieldNominal#cl2fn")
        val cl1ref = new Refinement("Class#cl1")
        val cl2ref = new Refinement("Class#cl2")
        val cl1mref = new Refinement("Maybeclass#cl1")
        val cl2mref = new Refinement("Maybeclass#cl2")
        val clsupermref = new Refinement("Maybeclass#clsuper")
        val packageref = new Refinement("Package#pkg")
        val initialRefinements: Refinements =
          new Refinements(Map(
            packageref -> RefinementDef("Package", Map("package" -> List(DataRefinementType("Maybeclass", Some(cl1mref)), DataRefinementType("Maybeclass", Some(cl2mref)), DataRefinementType("Maybeclass", Some(clsupermref))))),
            clsupermref -> RefinementDef("Maybeclass", Map("nothingclass" -> List())),
            cl1mref -> RefinementDef("Maybeclass", Map("justclass" -> List(DataRefinementType("Class", Some(cl1ref))))),
            cl2mref -> RefinementDef("Maybeclass", Map("justclass" -> List(DataRefinementType("Class", Some(cl2ref))))),
            cl1ref -> RefinementDef("Class", Map("class" -> List(DataRefinementType("ClassNominal", Some(cl1name)),
              MapRefinementType(DataRefinementType("FieldNominal", Some(cl1fnref)), DataRefinementType("Field", None), Intervals.Positive.Lattice.top),
              MapRefinementType(BaseRefinementType(StringRefinementType), DataRefinementType("Method", None), Intervals.Positive.Lattice.top),
              DataRefinementType("Maybeclassnominal", Some(cnosupername))))),
            cl2ref -> RefinementDef("Class", Map("class" -> List(DataRefinementType("ClassNominal", Some(cl2name)),
              MapRefinementType(DataRefinementType("FieldNominal", Some(cl2fnref)), DataRefinementType("Field", None), Intervals.Positive.Lattice.top),
              MapRefinementType(BaseRefinementType(StringRefinementType), DataRefinementType("Method", None), Intervals.Positive.Lattice.top),
              DataRefinementType("Maybeclassnominal", Some(cnosupername))))),
            cl1fnref -> RefinementDef("FieldNominal", Map("scf1" -> List(), "scf2" -> List(), "c1f1" -> List(), "c1f2" -> List())),
            cl2fnref -> RefinementDef("FieldNominal", Map("scf1" -> List(), "scf2" -> List(), "c2f1" -> List(), "c2f2" -> List())),
            cnosupername -> RefinementDef("Maybeclassnominal", Map("nothingclnom" -> List())),
            csupername -> RefinementDef("ClassNominal", Map("clsname" -> List())),
            cl1name -> RefinementDef("ClassNominal", Map("cl1name" -> List())),
            cl2name -> RefinementDef("ClassNominal", Map("cl2name" -> List()))
          ))
        val initialStore =
          TypeStoreV(Map(
            "pkg" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Package", Some(packageref))),
            "clsupername" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("ClassNominal", Some(csupername)))
          ))
        AbstractRefinementTypeExecutor.execute(moddef, "extractSuperclass", initialStore = Some(initialStore),
          initialRefinements = initialRefinements, refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Package"), Some(memoinfo), Some(duration), confname)
      }
    }
  }
}
