module RenameStructField

data Nominal = nfn() | ofn() | other();
data Package = package(map[str, Struct] structures, map[str, Function] functions);
data Struct = struct(str name, map[Nominal, Field] fields);
data Field = field(Nominal name, str typ);
data Function = function(str name, str return_typ, list[Parameter] parameters, Stmt body);
data Parameter = parameter(str typ, str name);
data Stmt = ifstmt(Expr cond, Stmt thenb, Stmt elseb)
          | returnstmt(Expr val)
          | assignstmt(Expr lhs, Expr rhs)
          | block(list[Stmt] stmts)
          ;
data Expr = fieldaccessexpr(Expr target, Nominal fieldname)
          | varexpr(str name)
          | functioncallexpr(Expr target, str methodname, list[Expr] args)
          ;

Package renameField(Package pkg, str st, Nominal oldFieldName, Nominal newFieldName) {
	assert (st in pkg.structures) &&
	       (oldFieldName in pkg.structures[st].fields) &&
	       (newFieldName notin pkg.structures[st].fields);
	Field fieldDef = pkg.structures[st].fields[oldFieldName];
	fieldDef.name = newFieldName;
	pkg.structures[st].fields = delete(pkg.structures[st].fields, oldFieldName) + (newFieldName: fieldDef);
	return top-down visit(pkg) {
		case fieldaccessexpr(target, oldFieldName) => fieldaccessexpr(target, newFieldName)
	};
}
