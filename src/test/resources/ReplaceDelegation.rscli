module ReplaceDelegation

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

Package replaceDelegationWithInheritance(Package pkg, str clname, str fname) {
	assert (clname in pkg.classes) &&
	       (fname in pkg.classes[clname].fields) &&
	       (pkg.classes[clname].fields[fname].typ != clname) && // TODO not is subtype
	       (pkg.classes[clname].super == nothing());
	Class cl = pkg.classes[clname];
	Field f = cl.fields[fname];
	Class ftyp = pkg.classes[f.typ];
	// Delete purely delegating methods
	for (ftmname <- ftyp.methods) {
	    for (cmname <- cl.methods) {
            if (cmname in cl.methods) { // Might be deleted by previous iteration
                Method ftm = ftyp.methods[ftmname];
                Method cm = cl.methods[cmname];
                if (ftm.name == cm.name) {
                    switch (cm.body) {
                        case returnstmt(methodcallexpr(_,
                          fieldaccessexpr(_, var(_, "this"), fname), ftmname, _)) =>
                            ({ cl.methods = delete(cl.methods, cmname); })
                        case _ => ({
                             cm.body = top-down visit(cm.body) {
                                case fieldaccessexpr(_, var(_, "this"), fname) => var(f.typ, "super")
                             }
                             cl.methods[cmname] = cm;
                           })
                    };
                };
            };
		};
	};
	cl.fields = delete(cl.fields, fname);
	cl.super = just(f.typ);
	pkg.classes[clname] = cl;
	return top-down visit(pkg) {
		case fae : fieldaccessexpr(faty, target, fname) => 
		  { if (target.typ == clname) target; else fae; }
	};
}

test bool does_not_replace_call_to_unrelated_function() {
	Package inpkg =
	  	package(("C" : class("C", ("f": field("f", "G")),
	  	                          ("m": method("m", "G", [],
	  	                                   returnstmt(
	  	                                      methodcallexpr("G",
	  	                                          fieldaccessexpr("G", var("C", "this"), "f"), "m", []))),
	  	                           "n": method("n", "G", [parameter("d","D")], assignstmt(var("void", "x"),
	  	                                         methodcallexpr("void", fieldaccessexpr("D", var("D", "d"), "f"), "m", [])))), nothing()),
	  	         "G" : class("G", (), ("m": method("m", "G", [],
	  	                                   returnstmt(var("G", "this")))), nothing()),
	  	         "D" : class("D", ("f": field("f", "D")), ("m": method("m", "void", [], block([]))), nothing())));
	Package outpkg =
	  	package(("C" : class("C", (),
		  	                          ("n": method("n", "G", [parameter("d","D")], assignstmt(var("void", "x"),
		  	                             methodcallexpr("void", fieldaccessexpr("D", var("D", "d"), "f"), "m", [])))), just("G")),
		  	         "G" : class("G", (), ("m": method("m", "G", [],
		  	                                   returnstmt(var("G", "this")))), nothing()),
		  	         "D" : class("D", ("f": field("f", "D")), ("m": method("m", "void", [], block([]))), nothing())));
	return replaceDelegationWithInheritance(inpkg, "C", "f") == outpkg;
}

test bool does_not_replace_non_purely_delegating_methods() {
	Package inpkg =
	  	package(("C" : class("C", ("f": field("f", "G")),
	  	                          ("m": method("m", "G", [],
	  	                                   block([assignstmt(var("G", "x"), fieldaccessexpr("G", var("C", "this"), "f")) ,returnstmt(
	  	                                      methodcallexpr("G",
	  	                                          fieldaccessexpr("G", var("C", "this"), "f"), "m", []))])),
	  	                           "n": method("n", "G", [parameter("c","C")], assignstmt(var("G", "x"),
	  	                                         methodcallexpr("G", fieldaccessexpr("G", var("C", "c"), "f"), "m", [])))), nothing()),
	  	         "G" : class("G", (), ("m": method("m", "G", [],
	  	                                   returnstmt(var("G", "this")))), nothing())));
	Package outpkg =
	  	package(("C" : class("C", (),
	  	                          ("m": method("m", "G", [],
	  	                                   block([assignstmt(var("G", "x"), var("G", "super")) ,returnstmt(
	  	                                      methodcallexpr("G", var("G", "super"), "m", []))])),
	  	                           "n": method("n", "G", [parameter("c","C")], assignstmt(var("G", "x"),
	  	                                         methodcallexpr("G", var("C", "c"), "m", [])))), just("G")),
	  	         "G" : class("G", (), ("m": method("m", "G", [],
	  	                                   returnstmt(var("G", "this")))), nothing())));
	return replaceDelegationWithInheritance(inpkg, "C", "f") == outpkg;
}
