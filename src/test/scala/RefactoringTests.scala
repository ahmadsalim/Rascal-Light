import example.Refactoring
import org.scalatest.{FlatSpec, Matchers}
import semantics.Executor
import semantics.domains._
import syntax._

/**
  * Created by asal on 01/03/2017.
  */
class RefactoringTests extends FlatSpec with Matchers {
  "The rename field refactoring" should "rename field in class correctly, including all field access expressions" in {
    val initialStore = Store(Map("pkg" ->
      ConstructorValue("package", Seq(MapValue(Map(
        BasicValue(StringLit("H")) ->
          ConstructorValue("class", Seq(BasicValue(StringLit("H")), MapValue(Map(
            BasicValue(StringLit("f")) -> ConstructorValue("field", Seq(BasicValue(StringLit("f")), BasicValue(StringLit("H"))))
          )), MapValue(Map(
            BasicValue(StringLit("m")) -> ConstructorValue("method",
              Seq(BasicValue(StringLit("m")), BasicValue(StringLit("H")), ListValue(List()),
                ConstructorValue("returnstmt", Seq(ConstructorValue("fieldaccessexpr", Seq(BasicValue(StringLit("H")), ConstructorValue("var", Seq(BasicValue(StringLit("H")), BasicValue(StringLit("x")))), BasicValue(StringLit("f"))))))))
          )), ConstructorValue("MaybeClass.nothing", Seq())))
      ))))
    ))
    val resultStore = Store(Map("pkg" ->
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
      GlobalVarDef(ValueType, "_", FunCallExpr("renameField", Seq(VarExpr("pkg"), BasicExpr(StringLit("H")), BasicExpr(StringLit("f")), BasicExpr(StringLit("g"))))))
    Executor.execute(inputModule, initialStore)
  }
}
