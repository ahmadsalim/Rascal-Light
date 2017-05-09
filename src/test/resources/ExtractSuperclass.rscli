module ExtractSuperclass

data Package = package(map[str, Class] classes);
data Maybestr = nothing() | just(str val) ;
data Class = class(str name, map[str, Field] fields, map[str, Method] methods, Maybestr super);
data Field = field(str name, str typ);
data Method = method(str name, str return_typ, list[Parameter] parameters, Stmt body);
data Parameter = parameter(str typ, str name);
data Stmt = ifstmt(Expr cond, Stmt thenb, Stmt elseb)
          | returnstmt(Expr val)
          | assignstmt(Expr lhs, Expr rhs)
          | block(list[Stmt] stmts)
          ;
data Expr = fieldaccessexpr(str typ, Expr target, str fieldname)
          | var(str typ, str name)
          | methodcallexpr(str typ, Expr target, str methodname, list[Expr] args)
          ;

Package extractSuperclass(Package pkg, str cl1name, str cl2name, str clsupername) {
	assert (cl1name in pkg.classes) && 
	       (cl2name in pkg.classes) && 
	       (clsupername notin pkg.classes) &&
	       (pkg.classes[cl1name].super == nothing()) &&
	       (pkg.classes[cl2name].super == nothing());
	Class clsuper = class(clsupername, (), (), nothing());
	Class cl1 = pkg.classes[cl1name];
	Class cl2 = pkg.classes[cl2name];
	cl1.super = just(clsupername);
	cl2.super = just(clsupername);
	for (cl1fname <- cl1.fields) {
		for (cl2fname <- cl2.fields) {
		// fields might have been deleted by previous iteration
			if (cl1fname in cl1.fields && cl2fname in cl2.fields) {
				Field cl1f = cl1.fields[cl1fname];
				Field cl2f = cl2.fields[cl2fname];
				if (cl1f.name == cl2f.name && cl1f.typ == cl2f.typ) {
					cl1.fields = delete(cl1.fields, cl1fname);
					cl2.fields = delete(cl2.fields, cl2fname);
					clsuper.fields = clsuper.fields + (cl1fname: cl1f);
				};
			};
		};
	};
	pkg.classes[cl1name] = cl1;
	pkg.classes[cl2name] = cl2;
	pkg.classes = pkg.classes + (clsupername: clsuper);
	return pkg;
}

test bool extract_common_superclass_correctly() {
  Package inpkg =
  	package(("C1" : class("C1", ("f": field("f", "C2"), "h": field("h", "C1")), (), nothing()),
  	         "C2" : class("C2", ("g" : field("g", "C1"), "f": field("f", "C2")), (), nothing())));
  Package outpkg =
  	package(("C1": class("C1", ("h": field("h", "C1")), (), just("B")),
  	         "C2": class("C2", ("g": field("g", "C1")), (), just("B")),
  	         "B":  class("B", ("f": field("f", "C2")), (), nothing())));
  return extractSuperclass(inpkg, "C1", "C2", "B") == outpkg;
}

test bool extract_common_superclass_keeping_fields_with_common_names_but_same_types_in_the_subtypes() {
  Package inpkg =
  	package(("C1" : class("C1", ("f": field("f", "C1"), "h": field("h", "C1")), (), nothing()),
  	         "C2" : class("C2", ("g" : field("g", "C1"), "f": field("f", "C2")), (), nothing())));
  Package outpkg =
  	package(("C1" : class("C1", ("f": field("f", "C1"), "h": field("h", "C1")), (), just("B")),
  	         "C2" : class("C2", ("g" : field("g", "C1"), "f": field("f", "C2")), (),just("B")),
  	         "B": class("B", (), (), nothing())));
  return extractSuperclass(inpkg, "C1", "C2", "B") == outpkg;
}
