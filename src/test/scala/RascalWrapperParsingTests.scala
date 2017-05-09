import org.scalatest.{FlatSpec, Matchers}
import syntax._
import util.rascalwrapper.RascalWrapper

import scalaz.\/-

/**
  * Created by asal on 05/05/2017.
  */
class RascalWrapperParsingTests extends FlatSpec with Matchers {
  "The wrapped parser" should "parse Expr.rscli correctly" in {
    val resource = getClass.getResource("Expr.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a [\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    val expected = Module(
      List(DataDef("Expr", List(ConstructorDef("var", List(Parameter(BaseType(StringType), "nm"))),
                                ConstructorDef("cst", List(Parameter(BaseType(IntType), "vl"))),
                                ConstructorDef("mult", List(Parameter(DataType("Expr"), "el"), Parameter(DataType("Expr"), "er"))))),
           FunDef(DataType("Expr"), "simplify", List(Parameter(DataType("Expr"), "expr")),
             VisitExpr(BottomUp, VarExpr("expr"),
               List(Case(ConstructorPatt("mult", List(ConstructorPatt("cst", List(BasicPatt(IntLit(0)))), VarPatt("y"))), ConstructorExpr("cst", List(BasicExpr(IntLit(0))))),
                    Case(ConstructorPatt("mult", List(VarPatt("x"), ConstructorPatt("cst", List(BasicPatt(IntLit(0)))))), ConstructorExpr("cst", List(BasicExpr(IntLit(0))))),
                    Case(ConstructorPatt("mult", List(ConstructorPatt("cst", List(BasicPatt(IntLit(1)))), VarPatt("y"))), VarExpr("y")),
                    Case(ConstructorPatt("mult", List(VarPatt("x"), ConstructorPatt("cst", List(BasicPatt(IntLit(1)))))), VarExpr("x")))))
      ))
    translated shouldBe a [\/-[_]]
    translated.map(m => m.withoutTests shouldBe expected)
  }

  it should "parse NNF.rscli correctly" in {
    val resource = getClass.getResource("NNF.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a [\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    val expected = Module(
      List(DataDef("Formula",List(ConstructorDef("atom",List(Parameter(BaseType(StringType),"nm"))),
                                  ConstructorDef("and",List(Parameter(DataType("Formula"),"l"), Parameter(DataType("Formula"),"r"))),
                                  ConstructorDef("or",List(Parameter(DataType("Formula"),"l"), Parameter(DataType("Formula"),"r"))),
                                  ConstructorDef("imp",List(Parameter(DataType("Formula"),"l"), Parameter(DataType("Formula"),"r"))),
                                  ConstructorDef("neg",List(Parameter(DataType("Formula"),"f"))))),
           FunDef(DataType("Formula"),"nnf", List(Parameter(DataType("Formula"), "phi")),
             VisitExpr(TopDown,VarExpr("phi"),
               List(Case(ConstructorPatt("neg", List(ConstructorPatt("or",List(VarPatt("l"), VarPatt("r"))))),
                              ConstructorExpr("and",List(ConstructorExpr("neg",List(VarExpr("l"))), ConstructorExpr("neg",List(VarExpr("r")))))),
                    Case(ConstructorPatt("neg",List(ConstructorPatt("and",List(VarPatt("l"), VarPatt("r"))))),
                              ConstructorExpr("or",List(ConstructorExpr("neg",List(VarExpr("l"))), ConstructorExpr("neg",List(VarExpr("r")))))),
                    Case(ConstructorPatt("neg",List(ConstructorPatt("imp",List(VarPatt("l"), VarPatt("r"))))),
                      ConstructorExpr("and",List(VarExpr("l"), ConstructorExpr("neg",List(VarExpr("r")))))),
                 Case(ConstructorPatt("neg",List(ConstructorPatt("neg",List(VarPatt("f"))))),FunCallExpr("nnf",List(VarExpr("f")))))))))
    translated shouldBe a [\/-[_]]
    translated.map(m => m.withoutTests shouldBe expected)
  }

  it should "parse RenameField.rscli correctly" in {
    val resource = getClass.getResource("RenameField.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a [\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    val expected = Module(
      List(DataDef("Package", List(ConstructorDef("package",List(Parameter(MapType(BaseType(StringType),DataType("Class")), "classes"))))),
           DataDef("Maybestr",List(ConstructorDef("nothing",List()),
                                   ConstructorDef("just",List(Parameter(BaseType(StringType), "val"))))),
           DataDef("Class", List(ConstructorDef("class",List(Parameter(BaseType(StringType),"name"),
                                                             Parameter(MapType(BaseType(StringType),DataType("Field")),"fields"),
                                                             Parameter(MapType(BaseType(StringType),DataType("Method")),"methods"),
                                                             Parameter(DataType("Maybestr"), "super"))))),
           DataDef("Field",List(ConstructorDef("field",List(Parameter(BaseType(StringType),"name"),
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
                                                                     Parameter(BaseType(StringType),"fieldname"))),
                               ConstructorDef("var",List(Parameter(BaseType(StringType),"typ"), Parameter(BaseType(StringType),"name"))),
                               ConstructorDef("methodcallexpr",List(Parameter(BaseType(StringType),"typ"),
                                                                    Parameter(DataType("Expr"),"target"),
                                                                    Parameter(BaseType(StringType),"methodname"),
                                                                    Parameter(ListType(DataType("Expr")),"args"))))),
           FunDef(DataType("Package"),"renameField", List(Parameter(DataType("Package"),"pkg"),
                                                          Parameter(BaseType(StringType),"cl"),
                                                          Parameter(BaseType(StringType),"oldFieldName"),
                                                          Parameter(BaseType(StringType),"newFieldName")),
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
    translated shouldBe a [\/-[_]]
    translated.map(m => m.withoutTests shouldBe expected)
  }

  it should "parse and translate ExtractSuperclass.rscli without any error" in {
    val resource = getClass.getResource("ExtractSuperclass.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a [\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    translated should matchPattern { case \/-(_) => }
  }

  it should "parse and translate ReplaceDelegation.rscli without any error" in {
    val resource = getClass.getResource("ReplaceDelegation.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    parsed shouldBe a [\/-[_]]
    val translated = parsed.flatMap(RascalWrapper.translateModule)
    translated should matchPattern { case \/-(_) => }
  }

}
