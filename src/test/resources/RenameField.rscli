module RenameField

data Nominal = nfn() | ofn() | other();
data Package = package(map[str, Class] classes);
data Maybestr = nothing() | just(str val) ;
data Class = class(str name, map[Nominal, Field] fields, map[str, Method] methods, Maybestr super);
data Field = field(Nominal name, str typ);
data Method = method(str name, str return_typ, list[Parameter] parameters, Stmt body);
data Parameter = parameter(str typ, str name);
data Stmt = ifstmt(Expr cond, Stmt thenb, Stmt elseb)
          | returnstmt(Expr val)
          | assignstmt(Expr lhs, Expr rhs)
          | block(list[Stmt] stmts)
          ;
data Expr = fieldaccessexpr(str typ, Expr target, Nominal fieldname)
          | var(str typ, str name)
          | methodcallexpr(str typ, Expr target, str methodname, list[Expr] args)
          ;

Package renameField(Package pkg, str cl, Nominal oldFieldName, Nominal newFieldName) {
	assert (cl in pkg.classes) && 
	       (oldFieldName in pkg.classes[cl].fields) && 
	       (newFieldName notin pkg.classes[cl].fields);
	Field fieldDef = pkg.classes[cl].fields[oldFieldName]; 
	fieldDef.name = newFieldName;
	pkg.classes[cl].fields = delete(pkg.classes[cl].fields, oldFieldName) + (newFieldName: fieldDef);
	return top-down visit(pkg) {
		case fae : fieldaccessexpr(faty, target, oldFieldName) =>
			{ if (target.typ == cl) fieldaccessexpr(faty, target, newFieldName); else fae; }
	};
}

test bool renames_field_accessexpr_correctly() {
  Package inpkg =
  	package(("H" : class("H", (ofn(): field(ofn(), "H")),
  	("m": method("m", "H", [], returnstmt(fieldaccessexpr("H", var("H", "x"), ofn())))),
  	nothing())));
  Package outpkg =
  	package(("H": class("H", (nfn(): field(nfn(), "H")),
  	("m": method("m", "H", [], returnstmt(fieldaccessexpr("H", var("H", "x"), nfn())))),
  	nothing())));
  return renameField(inpkg, "H", ofn(), nfn()) ==  outpkg;
}

test bool does_not_rename_fieldaccessexpr_with_same_name_but_other_type() {
  Package inpkg =
  	package(("H" : class("H", (ofn(): field(ofn(), "H")),
  	("m": method("m", "H", [], returnstmt(fieldaccessexpr("H", var("G", "x"), ofn())))),
  	nothing()), "G" : class("G", (ofn(): field(ofn(), "G")), (), nothing())));
  Package outpkg =
  	package(("H" : class("H", (nfn(): field(nfn(), "H")),
  	("m": method("m", "H", [], returnstmt(fieldaccessexpr("H", var("G", "x"), ofn())))),
  	nothing()), "G": class("G", (ofn(): field(ofn(), "G")), (), nothing())));
  return renameField(inpkg, "H", ofn(), nfn()) == outpkg;
}