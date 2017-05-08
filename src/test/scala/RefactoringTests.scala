import example.Refactoring
import org.scalatest.{FlatSpec, Matchers}
import semantics.Executor
import semantics.domains._
import syntax._

import scalaz.\/-

/**
  * Created by asal on 01/03/2017.
  */
class RefactoringTests extends FlatSpec with Matchers {
  "The rename field refactoring" should "rename field in class correctly, including all field access expressions" in {
    val pkg = GlobalVarDef(DataType("Package"), "inpkg",
      ConstructorExpr("package", Seq(MapExpr(Seq(
        BasicExpr(StringLit("H")) ->
          ConstructorExpr("class", Seq(BasicExpr(StringLit("H")), MapExpr(Seq(
            BasicExpr(StringLit("f")) -> ConstructorExpr("field", Seq(BasicExpr(StringLit("f")), BasicExpr(StringLit("H"))))
          )), MapExpr(Seq(
            BasicExpr(StringLit("m")) -> ConstructorExpr("method",
              Seq(BasicExpr(StringLit("m")), BasicExpr(StringLit("H")), ListExpr(Seq()),
                ConstructorExpr("returnstmt", Seq(ConstructorExpr("fieldaccessexpr", Seq(BasicExpr(StringLit("H")), ConstructorExpr("var", Seq(BasicExpr(StringLit("H")), BasicExpr(StringLit("x")))), BasicExpr(StringLit("f"))))))))
          )), ConstructorExpr("MaybeClass.nothing", Seq())))
      ))))
    )
    val resultStore = Store(Map(
      "inpkg" ->
        ConstructorValue("package", Seq(MapValue(Map(
          BasicValue(StringLit("H")) ->
            ConstructorValue("class", Seq(BasicValue(StringLit("H")), MapValue(Map(
              BasicValue(StringLit("f")) -> ConstructorValue("field", Seq(BasicValue(StringLit("f")), BasicValue(StringLit("H"))))
            )), MapValue(Map(
              BasicValue(StringLit("m")) -> ConstructorValue("method",
                Seq(BasicValue(StringLit("m")), BasicValue(StringLit("H")), ListValue(List()),
                  ConstructorValue("returnstmt", Seq(ConstructorValue("fieldaccessexpr", Seq(BasicValue(StringLit("H")), ConstructorValue("var", Seq(BasicValue(StringLit("H")), BasicValue(StringLit("x")))), BasicValue(StringLit("f"))))))))
            )), ConstructorValue("MaybeClass.nothing", Seq())))
        )))),
      "_" ->
      ConstructorValue("package", Seq(MapValue(Map(
        BasicValue(StringLit("H")) ->
          ConstructorValue("class", Seq(BasicValue(StringLit("H")), MapValue(Map(
            BasicValue(StringLit("g")) -> ConstructorValue("field", Seq(BasicValue(StringLit("g")), BasicValue(StringLit("H"))))
          )), MapValue(Map(
            BasicValue(StringLit("m")) -> ConstructorValue("method",
              Seq(BasicValue(StringLit("m")), BasicValue(StringLit("H")), ListValue(List()),
                ConstructorValue("returnstmt", Seq(ConstructorValue("fieldaccessexpr", Seq(BasicValue(StringLit("H")), ConstructorValue("var", Seq(BasicValue(StringLit("H")), BasicValue(StringLit("x")))), BasicValue(StringLit("g"))))))))
          )), ConstructorValue("MaybeClass.nothing", Seq())))
      ))))
    ))
    val inputModule = syntax.Module(Refactoring.refactoringsModule.defs :+
      pkg :+
      GlobalVarDef(ValueType, "_", FunCallExpr("renameField", Seq(VarExpr("inpkg"), BasicExpr(StringLit("H")), BasicExpr(StringLit("f")), BasicExpr(StringLit("g"))))))
    val actual = Executor.execute(inputModule)
    actual should matchPattern { case \/-(ExecutionResult(`resultStore`, _, _)) => }
  }
}
