package evaluation

import scalaz.\/-
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator}
import semantics.domains.abstracting._
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class NormalizePHPScriptEvaluation extends Evaluation("normalize-php-script-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The discardHTML function in NormalizePHPScript.rsc" should
    s"run correctly with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/NormalizePHPScript.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "discardHTML",
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Script"), Some(memoinfo), Some(duration), confname)
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The useBuiltins function in NormalizePHPScript.rsc" should
      s"run correctly with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/NormalizePHPScript.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val transmodule = ModuleTranslator.translateModule(moddef)
        transmodule shouldBe a[\/-[_]]
        val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
          mtr => {
            mtr.semmod.datatypes.transform((_, conss) =>
              mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
          })
        val simpleScriptRn = new Refinement("Script#simple")
        val simpleStmtRn = new Refinement("Stmt#simple")
        val initialRefinements = new Refinements(Map(
          simpleScriptRn -> RefinementDef("Script", Map("script" -> List(ListRefinementType(DataRefinementType("Stmt", Some(simpleStmtRn)), Intervals.Positive.Lattice.top)))),
          simpleStmtRn -> RefinementDef("Stmt", Map("exprstmt"-> List(DataRefinementType("Expr", None))))
        ))
        val initialStore = TypeStoreV(Map("s" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Script", Some(simpleScriptRn)))))
        AbstractRefinementTypeExecutor.execute(moddef, "useBuiltins",
          refinedMatches = refinement, memoWidening = memowidening, initialRefinements = initialRefinements,
          initialStore = Some(initialStore))
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Script"), Some(memoinfo), Some(duration), confname)
      }
    }
  }
}
