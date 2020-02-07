module ExtractSuperclass

data FieldNominal = scf1() | scf2() | c1f1() | c1f2() | c2f1() | c2f2();
data FieldTypeNominal = ftn();
data Package = package(Maybeclass class1, Maybeclass class2, Maybeclass superclass);
data Maybeclassnominal = nothingclnom() | justclnom(ClassNominal val);
data ClassNominal = cl1name() | cl2name() | clsname();
data Class = class(ClassNominal name, map[FieldNominal, Field] fields, map[str, Method] methods, Maybeclassnominal super);
data Maybeclass = nothingclass() | justclass(Class class);
data Field = field(FieldNominal name, FieldTypeNominal typ);
data Method = method(str name, str return_typ, list[Parameter] parameters, Stmt body);
data Parameter = parameter(str typ, str name);
data Stmt = ifstmt(Expr cond, Stmt thenb, Stmt elseb)
          | returnstmt(Expr val)
          | assignstmt(Expr lhs, Expr rhs)
          | block(list[Stmt] stmts)
          ;
data Expr = fieldaccessexpr(str typ, Expr target, FieldNominal fieldname)
          | var(str typ, str name)
          | methodcallexpr(str typ, Expr target, str methodname, list[Expr] args)
          ;

data Exc = precondExc();

Package extractSuperclass(Package pkg, ClassNominal clsupername) {
	assert (pkg.class1.super == nothingclnom()) &&
	       (pkg.class2.super == nothingclnom());
    Class cl1;
    Class cl2;
	switch (pkg.class1) {
        case nothingclass(): throw precondExc();
        case justclass(cl1v): cl1 = cl1v;
	}
	switch (pkg.class2) {
	    case nothingclass(): throw precondExc();
	    case justclass(cl2v): cl2 = cl2v;
	}
	switch (pkg.superclass) {
	    case nothingclass(): ;
	    case justclass(clsv): throw precondExc();
	}
	Class clsuper = class(clsupername, (), (), nothingclnom());
	cl1.super = justclnom(clsupername);
	cl2.super = justclnom(clsupername);
	for (cl1fname <- cl1.fields) {
		for (cl2fname <- cl2.fields) {
		// fields might have been deleted by previous iteration
			if (cl1fname == cl2fname) {
				Field cl1f = cl1.fields[cl1fname];
				Field cl2f = cl2.fields[cl2fname];
				if (cl1f.typ == cl2f.typ) {
					cl1.fields = delete(cl1.fields, cl1fname);
					cl2.fields = delete(cl2.fields, cl2fname);
					clsuper.fields = clsuper.fields + (cl1fname: cl1f);
				};
			};
		};
	};
	pkg.class1 = justclass(cl1);
	pkg.class2 = justclass(cl2);
	pkg.superclass = justclass(clsuper);
	return pkg;
}

