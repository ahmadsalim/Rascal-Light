import org.scalatest.{FlatSpec, Matchers}
import semantics.domains.{BasicValue, Domains, ExecutionResult, Store}
import semantics.Executor
import syntax._

import scalaz.\/-

/**
  * Created by asal on 01/03/2017.
  */
class ModuleExecutionTests extends FlatSpec with Matchers {
  "The empty module" should "produce an empty store and only have prelude definitions" in {
    val emptyModule = syntax.Module(Seq())
    val expected = ExecutionResult(Store(Map()), Domains.prelude, List())
    val actual = Executor.execute(emptyModule)
    actual should matchPattern { case \/-(`expected`) => }
  }

  "The module with definition `value _ = 2 + 3`" should "produce a store with `_` mapped to `5` and a module with `value _`" in {
    val valModule = syntax.Module(Seq(
      GlobalVarDef(ValueType, "_", BinaryExpr(BasicExpr(IntLit(2)), "+", BasicExpr(IntLit(3))))))
    val expected = ExecutionResult(Store(Map("_" -> BasicValue(IntLit(5)))),
                        Domains.prelude.copy(globalVars = Domains.prelude.globalVars.updated("_", ValueType)), List())
    val actual = Executor.execute(valModule)
    actual should matchPattern { case \/-(`expected`) => }
  }

  "The module with definition `int double(int x) = x * x`" should "produce an empty store and a module with the function definition" in {
    val funModule = syntax.Module(Seq(
      FunDef(BaseType(IntType), "double", Seq(Parameter(BaseType(IntType), "x")), BinaryExpr(VarExpr("x"), "*", VarExpr("x")))))
    val expected = ExecutionResult(Store(Map()),
      Domains.prelude.copy(funs =
        Domains.prelude.funs.updated("double",
          (BaseType(IntType), List(Parameter(BaseType(IntType), "x")), BinaryExpr(VarExpr("x"), "*", VarExpr("x"))))), List())
    val actual = Executor.execute(funModule)
    actual should matchPattern { case \/-(`expected`) => }
  }

  "The module with `definition data Nat = zero() | succ(n: Nat)`" should "produce an empty store and a module with the data type definition" in {
    val dataModule = syntax.Module(
      Seq(DataDef("Nat", Seq(ConstructorDef("zero", Seq()), ConstructorDef("succ", Seq(Parameter(DataType("Nat"), "n")))))))
    val expected = ExecutionResult(Store(Map()),
      Domains.prelude.copy(datatypes = Domains.prelude.datatypes.updated("Nat", List("zero", "succ")),
      constructors = Domains.prelude.constructors.updated("zero", ("Nat", List()))
                                                 .updated("succ", ("Nat", List(Parameter(DataType("Nat"), "n"))))), List())

    val actual = Executor.execute(dataModule)
    actual should matchPattern { case \/-(`expected`) => }
  }


  "The module with definitions `int double(int x) = x * x` and `int y = double(5)`" should
    "produce a store mapping `y` to `25` to and a module with the function definition and `int y`" in {
    val module = syntax.Module(Seq(
      FunDef(BaseType(IntType), "double", Seq(Parameter(BaseType(IntType), "x")), BinaryExpr(VarExpr("x"), "*", VarExpr("x"))),
      GlobalVarDef(BaseType(IntType), "y", FunCallExpr("double", Seq(BasicExpr(IntLit(5)))))))
    val expected = ExecutionResult(Store(Map("y" -> BasicValue(IntLit(25)))),
      Domains.prelude.copy(globalVars = Domains.prelude.globalVars.updated("y", BaseType(IntType)),
        funs = Domains.prelude.funs.updated("double",
          (BaseType(IntType), List(Parameter(BaseType(IntType), "x")), BinaryExpr(VarExpr("x"), "*", VarExpr("x"))))), List())
    val actual = Executor.execute(module)
    actual should matchPattern { case \/-(`expected`) => }
  }
}
