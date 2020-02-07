import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.prop.Tables.Table
import org.scalatest.{FlatSpec, Matchers}
import syntax._
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 05/05/2017.
  */
class RascalWrapperParsingTests extends FlatSpec with Matchers {

  private def parseAndTranslateWithoutAnyError(fileName : String) = {
    val resource = getClass.getResource(fileName)
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a[\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    translated should matchPattern { case \/-(_) => }
  }

  private def parseAndTranslateMatchingExpected(fileName : String, expected : Any) = {
    val resource = getClass.getResource(fileName)
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a [\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    translated shouldBe a [\/-[_]]
    translated.foreach(m => m.withoutTests shouldBe expected)
  }

  "The wrapped parser" should "parse Expr.rsc correctly" in {
    val expected = ModuleDef(List(
      DataDef("Nat",List(ConstructorDef("zero",List()), ConstructorDef("suc",List(Parameter(DataType("Nat"),"pre"))))),
      DataDef("Expr",List(ConstructorDef("var",List(Parameter(BaseType(StringType),"nm"))),
                          ConstructorDef("cst",List(Parameter(DataType("Nat"),"vl"))),
                          ConstructorDef("mult",List(Parameter(DataType("Expr"),"el"), Parameter(DataType("Expr"),"er"))))),
      FunDef(DataType("Expr"), "simplify", List(Parameter(DataType("Expr"), "expr")),
               VisitExpr(BottomUp,VarExpr("expr"), List(
                 Case(ConstructorPatt("mult",List(ConstructorPatt("cst",List(ConstructorPatt("zero",List()))), VarPatt("y"))),
                             ConstructorExpr("cst",List(ConstructorExpr("zero",List())))),
                 Case(ConstructorPatt("mult", List(VarPatt("x"), ConstructorPatt("cst",List(ConstructorPatt("zero",List()))))),ConstructorExpr("cst",List(ConstructorExpr("zero",List())))),
                 Case(ConstructorPatt("mult",List(ConstructorPatt("cst",List(ConstructorPatt("suc",List(ConstructorPatt("zero",List()))))), VarPatt("y"))),VarExpr("y")),
                 Case(ConstructorPatt("mult",List(VarPatt("x"), ConstructorPatt("cst",List(ConstructorPatt("suc",List(ConstructorPatt("zero",List()))))))),VarExpr("x")))))))
    parseAndTranslateMatchingExpected("Expr.rsc", expected)
  }

  it should "parse NNF.rsc correctly" in {
    val expected = ModuleDef(List(
      DataDef("Formula", List(ConstructorDef("atom", List(Parameter(BaseType(StringType), "arg0"))),
                              ConstructorDef("and", List(Parameter(DataType("Formula"), "l"), Parameter(DataType("Formula"), "r"))),
                              ConstructorDef("or", List(Parameter(DataType("Formula"), "l"), Parameter(DataType("Formula"), "r"))),
                              ConstructorDef("imp", List(Parameter(DataType("Formula"), "l"), Parameter(DataType("Formula"), "r"))),
                              ConstructorDef("neg", List(Parameter(DataType("Formula"), "f"))), ConstructorDef("begin", List(Parameter(DataType("Formula"), "f"))))),
                              FunDef(DataType("Formula"), "rawnnf", List(Parameter(DataType("Formula"), "phi")),
                                VisitExpr(TopDown,VarExpr("phi"), List(
                                  Case(ConstructorPatt("neg", List(ConstructorPatt("or", List(VarPatt("l"), VarPatt("r"))))),
                                    ConstructorExpr("and", List(ConstructorExpr("neg",List(VarExpr("l"))), ConstructorExpr("neg",List(VarExpr("r")))))),
                                  Case(ConstructorPatt("neg",List(ConstructorPatt("and", List(VarPatt("l"), VarPatt("r"))))),
                                    ConstructorExpr("or",List(ConstructorExpr("neg",List(VarExpr("l"))), ConstructorExpr("neg",List(VarExpr("r")))))),
                                  Case(ConstructorPatt("neg",List(ConstructorPatt("imp",List(VarPatt("l"), VarPatt("r"))))),
                                    ConstructorExpr("and",List(VarExpr("l"), ConstructorExpr("neg",List(VarExpr("r")))))),
                                  Case(ConstructorPatt("neg",List(ConstructorPatt("neg",List(VarPatt("f"))))),
                                    ConstructorExpr("begin",List(VarExpr("f")))),
                                  Case(ConstructorPatt("imp",List(VarPatt("l"), VarPatt("r"))),
                                    ConstructorExpr("or",List(ConstructorExpr("neg",List(VarExpr("l"))), VarExpr("r"))))))),
                              FunDef(DataType("Formula"), "nobegin", List(Parameter(DataType("Formula"), "phi")),
                                VisitExpr(BottomUp,VarExpr("phi"), List(
                                  Case(ConstructorPatt("begin",List(VarPatt("f"))),VarExpr("f"))))),
                              FunDef(DataType("Formula"), "nnf", List(Parameter(DataType("Formula"), "phi")),
                                FunCallExpr("nobegin",List(FunCallExpr("rawnnf",List(VarExpr("phi"))))))))
    parseAndTranslateMatchingExpected("NNF.rsc", expected)
  }

  it should "parse RenameField.rsc correctly" in {
    val expected = ModuleDef(
      List(DataDef("Nominal", List(ConstructorDef("nfn", List()), ConstructorDef("ofn", List()), ConstructorDef("other",List()))),
           DataDef("Package", List(ConstructorDef("package",List(Parameter(MapType(BaseType(StringType),DataType("Class")), "classes"))))),
           DataDef("Maybestr",List(ConstructorDef("nothing",List()),
                                   ConstructorDef("just",List(Parameter(BaseType(StringType), "val"))))),
           DataDef("Class", List(ConstructorDef("class",List(Parameter(BaseType(StringType),"name"),
                                                             Parameter(MapType(DataType("Nominal"),DataType("Field")),"fields"),
                                                             Parameter(MapType(BaseType(StringType),DataType("Method")),"methods"),
                                                             Parameter(DataType("Maybestr"), "super"))))),
           DataDef("Field",List(ConstructorDef("field",List(Parameter(DataType("Nominal"),"name"),
                                                            Parameter(BaseType(StringType), "typ"))))),
           DataDef("Method",List(ConstructorDef("method",List(Parameter(BaseType(StringType),"name"),
                                                              Parameter(BaseType(StringType),"return_typ"),
                                                              Parameter(ListType(DataType("Parameter")),"parameters"),
                                                              Parameter(DataType("Stmt"),"body"))))),
           DataDef("Parameter",List(ConstructorDef("parameter",List(Parameter(BaseType(StringType),"typ"),
                                                                    Parameter(BaseType(StringType),"name"))))),
           DataDef("Stmt",List(ConstructorDef("ifstmt",List(Parameter(DataType("Expr"), "cond"),
                                                            Parameter(DataType("Stmt"), "thenb"),
                                                            Parameter(DataType("Stmt"), "elseb"))),
                               ConstructorDef("returnstmt",List(Parameter(DataType("Expr"),"val"))),
                               ConstructorDef("assignstmt",List(Parameter(DataType("Expr"),"lhs"),
                                                                Parameter(DataType("Expr"),"rhs"))),
                               ConstructorDef("block",List(Parameter(ListType(DataType("Stmt")),"stmts"))))),
           DataDef("Expr",List(ConstructorDef("fieldaccessexpr",List(Parameter(BaseType(StringType),"typ"),
                                                                     Parameter(DataType("Expr"),"target"),
                                                                     Parameter(DataType("Nominal"),"fieldname"))),
                               ConstructorDef("var",List(Parameter(BaseType(StringType),"typ"), Parameter(BaseType(StringType),"name"))),
                               ConstructorDef("methodcallexpr",List(Parameter(BaseType(StringType),"typ"),
                                                                    Parameter(DataType("Expr"),"target"),
                                                                    Parameter(BaseType(StringType),"methodname"),
                                                                    Parameter(ListType(DataType("Expr")),"args"))))),
           FunDef(DataType("Package"),"renameField", List(Parameter(DataType("Package"),"pkg"),
                                                          Parameter(BaseType(StringType),"cl"),
                                                          Parameter(DataType("Nominal"),"oldFieldName"),
                                                          Parameter(DataType("Nominal"),"newFieldName")),
             LocalBlockExpr(List(),
               List(AssertExpr(BinaryExpr(BinaryExpr(BinaryExpr(VarExpr("cl"),"in",FieldAccExpr(VarExpr("pkg"),"classes")),"&&",
                                 BinaryExpr(VarExpr("oldFieldName"),"in", FieldAccExpr(MapLookupExpr(FieldAccExpr(VarExpr("pkg"), "classes"),VarExpr("cl")),"fields"))),"&&",
                                   BinaryExpr(VarExpr("newFieldName"),"notin",FieldAccExpr(MapLookupExpr(FieldAccExpr(VarExpr("pkg"), "classes"),VarExpr("cl")), "fields")))),
                 LocalBlockExpr(List(Parameter(DataType("Field"),"fieldDef")),
                                List(AssignExpr(VarAssgn("fieldDef"),
                                          MapLookupExpr(FieldAccExpr(MapLookupExpr(FieldAccExpr(VarExpr("pkg"),"classes"),VarExpr("cl")),"fields"),VarExpr("oldFieldName"))),
                                     AssignExpr(FieldAccAssgn(VarAssgn("fieldDef"), "name"),VarExpr("newFieldName")),
                                     AssignExpr(FieldAccAssgn(MapUpdAssgn(FieldAccAssgn(VarAssgn("pkg"),"classes"),VarExpr("cl")),"fields"),
                                          MapUpdExpr(FunCallExpr("delete",List(FieldAccExpr(MapLookupExpr(FieldAccExpr(VarExpr("pkg"),"classes"),VarExpr("cl")),"fields"), VarExpr("oldFieldName"))),VarExpr("newFieldName"),VarExpr("fieldDef"))),
                                     ReturnExpr(VisitExpr(TopDown,VarExpr("pkg"),
                                       List(Case(LabelledTypedPatt(ValueType,"fae", ConstructorPatt("fieldaccessexpr", List(VarPatt("faty"), VarPatt("target"), VarPatt("oldFieldName")))),
                                         LocalBlockExpr(List(),
                                                        List(IfExpr(BinaryExpr(FieldAccExpr(VarExpr("target"),"typ"),"==",VarExpr("cl")),
                                                               ConstructorExpr("fieldaccessexpr",List(VarExpr("faty"), VarExpr("target"), VarExpr("newFieldName"))),
                                                               VarExpr("fae")))))))),
                                                               LocalBlockExpr(List(),List()))))))))
    parseAndTranslateMatchingExpected("original/RenameField.rsc", expected)
  }

  val testRscliFiles =
    Table( "test file"
         , "ExtractSuperclass.rsc"
         , "unported/ReplaceDelegation.rsc"
         , "unported/SimplifyTableau.rsc"
         , "unported/DeriveTableau.rsc"
         , "unported/NormalizeOberon.rsc"
         , "unported/ConstantElimOberon.rsc"
         , "original/DesugarOberon.rsc"
         , "original/Glagol2PHP.rsc"
         , "IntProgs.rsc"
         , "MiniCalc.rsc"
         , "MiniConfigMod.rsc"
         , "unported/MarvolCompile.rsc"
         , "unported/NormalizePHPScript.rsc"
         , "unported/ConvertRascalType.rsc")

  TableDrivenPropertyChecks.forAll(testRscliFiles) { (testFile : String) =>
    it should s"parse and translate $testFile without any error" in {
      parseAndTranslateWithoutAnyError(testFile)
    }
  }
}
