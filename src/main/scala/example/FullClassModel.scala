package example

import syntax._

object FullClassModel {
  val classDefs: Seq[Def] =
    Seq(DataDef("Package", Seq(ConstructorDef("package", Seq(Parameter(MapType(BaseType(StringType), DataType("Class")), "classes"))))),
      DataDef("Class",
        Seq(ConstructorDef("class", Seq(Parameter(BaseType(StringType), "name"),
          Parameter(MapType(BaseType(StringType), DataType("Field")), "fields"),
          Parameter(MapType(BaseType(StringType), DataType("Method")), "methods"),
          Parameter(DataType("MaybeClass"), "super"))))),
      DataDef("MaybeClass", Seq(
        ConstructorDef("MaybeClass.just", Seq(Parameter(DataType("Class"), "c"))),
        ConstructorDef("MaybeClass.nothing", Seq())
      )),
      DataDef("Field", Seq(
        ConstructorDef("field", Seq(Parameter(BaseType(StringType), "name"), Parameter(BaseType(StringType), "typ")))
      )),
      DataDef("Method", Seq(
        ConstructorDef("method",
          Seq(Parameter(BaseType(StringType), "name"),
            Parameter(BaseType(StringType), "return_typ"),
            Parameter(ListType(DataType("Parameter")), "parameters"),
            Parameter(DataType("Statement"), "body")
            ))
      )),
      DataDef("Parameter", Seq(ConstructorDef("parameter",
        Seq(Parameter(BaseType(StringType), "typ"),
          Parameter(BaseType(StringType), "name")))
      )),
      DataDef("Stmt", Seq(
        ConstructorDef("ifstmt",
          Seq(Parameter(DataType("Expr"), "cond"), Parameter(DataType("Stmt"), "thenB"), Parameter(DataType("Stmt"), "elseB"))),
        ConstructorDef("returnstmt",
          Seq(Parameter(DataType("Expr"), "val"))),
        ConstructorDef("assignstmt",
          Seq(Parameter(DataType("Expr"), "lhs"), Parameter(DataType("Expr"), "rhs"))),
        ConstructorDef("block",
          Seq(Parameter(ListType(DataType("Stmt")), "stmts")))
      )),
      DataDef("Expr", Seq(
        ConstructorDef("fieldaccessexpr",
          Seq(Parameter(BaseType(StringType), "typ"),
                Parameter(DataType("target"), "expr"),
                  Parameter(BaseType(StringType), "fieldname"))),
        ConstructorDef("var", Seq(Parameter(BaseType(StringType), "typ"), Parameter(BaseType(StringType), "name"))),
        ConstructorDef("methodcallexpr", Seq(
          Parameter(BaseType(StringType), "typ"),
            Parameter(DataType("Expr"), "target"),
              Parameter(BaseType(StringType), "methodname"),
                Parameter(ListType(DataType("Expr")), "args"))
      ))
    ))
}
