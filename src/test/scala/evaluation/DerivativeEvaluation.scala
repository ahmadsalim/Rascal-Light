package evaluation

import scalaz.\/-
import semantics.AbstractRefinementTypeExecutor
import semantics.domains.abstracting._
import semantics.domains.common.Lattice
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class DerivativeEvaluation extends Evaluation("derivative-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The derivative computation in Derivative.rsc" should
    s"produce constant zero when run with a derivative not containing target variable or multiplication with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/Derivative.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val xref = new Refinement("VarNominal#x")
        val yref = new Refinement("VarNominal#y")
        val expref = new Refinement("Exp#nox")
        val initialRefinements: Refinements =
          new Refinements(Map(
            xref -> RefinementDef("VarNominal", Map("x" -> List())),
            yref -> RefinementDef("VarNominal", Map("y" -> List())),
            expref -> RefinementDef("Exp", Map(
              "con" -> List(BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.top))),
              "var" -> List(DataRefinementType("VarNominal", Some(yref))),
              "add" -> List(DataRefinementType("Exp", Some(expref)), DataRefinementType("Exp", Some(expref)))
            ))
          ))
        val initialStore =
          TypeStoreV(Map(
            "e" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Exp", Some(expref))),
            "v" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("VarNominal", Some(xref)))
          ))
        AbstractRefinementTypeExecutor.execute(moddef, "derivative", initialRefinements = initialRefinements,
          initialStore = Some(initialStore), refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Exp"), Some(memoinfo), Some(duration), s"zero: $confname")
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The derivative computation in Derivative.rsc" should
      s"produce an expression with only constant leafs when run with a derivative not containing non-linear multiplication with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/Derivative.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val xref = new Refinement("VarNominal#x")
        val conref = new Refinement("Exp#con")
        val linref = new Refinement("Exp#lin")
        val expref = new Refinement("Exp#linearx")
        val initialRefinements: Refinements =
          new Refinements(Map(
            xref -> RefinementDef("VarNominal", Map("x" -> List())),
            conref -> RefinementDef("Exp", Map(
              "con" -> List(BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.top)))
              )),
            linref -> RefinementDef("Exp", Map(
              "con" -> List(BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.top))),
              "var" -> List(DataRefinementType("VarNominal", Some(xref)))
            )),
            expref -> RefinementDef("Exp", Map(
              "con" -> List(BaseRefinementType(IntRefinementType(Intervals.Unbounded.Lattice.top))),
              "var" -> List(DataRefinementType("VarNominal", None)),
              "mul" -> List(DataRefinementType("Exp", Some(linref)), DataRefinementType("Exp", Some(conref)))
            ))
          ))
        val initialStore =
          TypeStoreV(Map(
            "e" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Exp", Some(expref))),
            "v" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("VarNominal", Some(xref)))
          ))
        AbstractRefinementTypeExecutor.execute(moddef, "dd", initialRefinements = initialRefinements,
          initialStore = Some(initialStore), refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Exp"), Some(memoinfo), Some(duration), s"linear: $confname")
      }
    }
  }
}
