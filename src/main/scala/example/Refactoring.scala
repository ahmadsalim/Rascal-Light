package example

import syntax._

/**
  * Created by asal on 01/03/2017.
  */
object Refactoring {
  val refactoringsModule = Module(FullClassModel.classDefs ++ Seq(
    FunDef(DataType("Package"), "renameField",
      Seq(Parameter(DataType("Package"), "pkg"),
          Parameter(BaseType(StringType), "cl"),
          Parameter(BaseType(StringType), "oldFieldName"),
          Parameter(BaseType(StringType), "newFieldName")),
      LocalBlockExpr(Seq(Parameter(DataType("Field"), "fieldDef")), Seq(
        AssignExpr("fieldDef",
          SwitchExpr(VarExpr("pkg"),
            Seq(Case(ConstructorPatt("package", Seq(VarPatt("pkg_classes"))),
              SwitchExpr(LookupExpr(VarExpr("pkg_classes"), VarExpr("cl")),
                Seq(Case(ConstructorPatt("class", Seq(VarPatt("cl.name"), VarPatt("cl.fields"), VarPatt("cl.methods"), VarPatt("cl.super"))),
                  LookupExpr(VarExpr("cl.fields"), VarExpr("oldFieldName")))))
            )))
        ),
        AssignExpr("fieldDef",
          SwitchExpr(VarExpr("fieldDef"),
            Seq(Case(ConstructorPatt("field", Seq(VarPatt("fieldDef.name"), VarPatt("fieldDef.typ"))),
              ConstructorExpr("field", Seq(VarExpr("newFieldName"), VarExpr("fieldDef.typ"))))))
          ),
        AssignExpr("pkg",
          SwitchExpr(VarExpr("pkg"),
            Seq(Case(ConstructorPatt("package", Seq(VarPatt("pkg_classes"))),
              ConstructorExpr("package",
                Seq(SwitchExpr(LookupExpr(VarExpr("pkg_classes"), VarExpr("cl")),
                  Seq(Case(ConstructorPatt("class", Seq(VarPatt("cl.name"), VarPatt("cl.fields"), VarPatt("cl.methods"), VarPatt("cl.super"))),
                     UpdateExpr(VarExpr("pkg_classes"), VarExpr("cl"),
                       ConstructorExpr("class", Seq(VarExpr("cl.name"),
                         UpdateExpr(BinaryExpr(VarExpr("cl.fields"), "delete", VarExpr("oldFieldName")), VarExpr("newFieldName"), VarExpr("fieldDef")), VarExpr("cl.methods"), VarExpr("cl.super"))))
                  ))))
              ))))
        ),
        VisitExpr(TopDown, VarExpr("pkg"),
          Seq(Case(LabelledTypedPatt(DataType("Expr"), "fae",
            ConstructorPatt("fieldaccessexpr", Seq(VarPatt("faty"), VarPatt("target"), VarPatt("oldFieldName")))),
              IfExpr(BinaryExpr(SwitchExpr(VarExpr("target"),
                Seq(Case(ConstructorPatt("fieldaccessexpr", Seq(VarPatt("target.typ"), VarPatt("target.target"), VarPatt("target.fieldname"))), VarExpr("target.typ")),
                    Case(ConstructorPatt("var", Seq(VarPatt("target.typ"), VarPatt("target.name"))),
                      VarExpr("target.typ")),
                    Case(ConstructorPatt("methodcallexpr", Seq(VarPatt("target.typ"), VarPatt("target.target"), VarPatt("target.methodname"), VarPatt("target.args"))),
                      VarExpr("target.typ")))), "==", VarExpr("cl")),
                ConstructorExpr("fieldaccessexpr", Seq(VarExpr("faty"), VarExpr("target"), VarExpr("newFieldName"))),
                VarExpr("fae"))
          )))
      ))
    )
  ))
}
