import org.scalatest.{FlatSpec, Matchers}
import syntax._
import util.rascalwrapper.RascalWrapper

import scala.io.Source
import scalaz.\/-

/**
  * Created by asal on 05/05/2017.
  */
class RascalWrapperParsingTests extends FlatSpec with Matchers {
  "The wrapped parser" should "parse Expr.rscli correctly" in {
    val resource = getClass.getResource("Expr.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    val translated = RascalWrapper.translateModule(parsed)
    val expected = Module(
      List(DataDef("Expr", List(ConstructorDef("var", List(Parameter(BaseType(StringType), "nm"))),
                                ConstructorDef("cst", List(Parameter(BaseType(IntType), "vl"))),
                                ConstructorDef("mult", List(Parameter(DataType("Expr"), "el"), Parameter(DataType("Expr"), "er"))))),
           FunDef(DataType("Expr"), "simplify", List(Parameter(DataType("Expr"), "expr")),
             VisitExpr(BottomUp, VarExpr("expr"),
               List(Case(ConstructorPatt("mult", List(ConstructorPatt("cst", List(BasicPatt(IntLit(0)))), VarPatt("y"))), ConstructorExpr("cst", List(BasicExpr(IntLit(0))))),
                    Case(ConstructorPatt("mult", List(VarPatt("x"), ConstructorPatt("cst", List(BasicPatt(IntLit(0)))))), ConstructorExpr("cst", List(BasicExpr(IntLit(0))))),
                    Case(ConstructorPatt("mult", List(ConstructorPatt("cst", List(BasicPatt(IntLit(1)))), VarPatt("y"))), VarExpr("y")),
                    Case(ConstructorPatt("mult", List(VarPatt("x"), ConstructorPatt("cst", List(BasicPatt(IntLit(1)))))), VarExpr("x")))))))
    println(translated)
    translated shouldBe a [\/-[_]]
  }
}
