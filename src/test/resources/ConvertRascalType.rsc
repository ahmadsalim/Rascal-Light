/**
* Translation from Rascal Core Types to Rascal Types
* Ported from
*/

module ConvertRascalType

// Rascal
data UserType = name(QualifiedName name)
             | parametric(QualifiedName name, list[Type] /* + */ parameters);

data StructuredType = \default(BasicType basicType, list[TypeArg] /* + */ arguments);

data BasicType = \value() | \loc() | \node() | \num() | \type() | \bag() | \int() | rational()
               | relation() | listRelation() | \real() | \tuple() | string() | \bool()
               | \void() | dateTime() | \set() | \map() | \list() ;

data TypeVar = free(str name) | bounded(str name, Type bound);

data QualifiedName = \default(list[str] /* + */ names);

data DataTypeSelector = selector(QualifiedName sort, str production);

data TypeArg = \default(Type \type) | named(Type \type, str name);

data FunctionType = typeArguments(Type \type, list[TypeArg] arguments);

data Class = simpleCharclass(list[Range] ranges)
           | complement(Class charClass)
           | difference(Class lhs, Class rhs)
           | intersection(Class lhs, Class rhs)
           | union(Class lhs, Class rhs)
           | \bracket(Class charClass);

// Can't find Nonterminal and NonterminalLabel
data Nonterminal = mknonterminal(); 
data NonterminalLabel = mknonterminallabel(str label);
data IntegerLiteral = intlit(int i);

data Sym = nonterminal(Nonterminal nonterminal)
         | parameter(Nonterminal nonterminal)
         | parametrized(Nonterminal nonterminal, list[Sym] /* + */ parameters)
         | \start(Nonterminal nonterminal)
         | labeled(Sym symbol, NonterminalLabel label)
         | characterClass(Class charClass)
         | literal(str string)
         | caseInsensitiveLiteral(str cistring)
         | iter(Symbol symbol)
         | iterStar(Sym symbol)
         | iterSep(Sym symbol, Sym sep)
         | iterStarSep(Sym symbol, Sym sep)
         | optional(Sym symbol)
         | alternative(Sym first, list[Sym] /* + */ alternatives)
         | sequence(Sym first, list[Sym] /* + */ sequence)
         | empty()
         | column(Sym symbol, IntegerLiteral i)
         | endOfLine(Sym symbol)
         | startOfLine(Sym symbol)
         | except(Sym symbol, NonterminalLabel label)
         | follow(Sym symbol, Sym match)
         | notFollow(Sym symbol, Sym match)
         | precede(Sym match, Sym symbol)
         | notPrecede(Sym match, Sym symbol)
         | unequal(Sym symbol, Sym match);
         
data Type = \bracket(Type \type)
          | user(UserType user)
          | function(FunctionType function)
          | structured(StructuredType structured)
          | basic(BasicType basic)
          | selector(DataTypeSelector selector)
          | variable(TypeVar typeVar)
          | symbol(Sym symbol)
          ;

// AType
data Keyword = mkkeyword(str fieldName, AType fieldType, Expression defaultExp);
data NamedField  = mknamefield(str fieldName, AType fieldType);
data QName        = qualName(str qualifier, str name);


data AType
    =  aint()
     | abool()
     | areal()
     | arat()
     | astr()
     | anum()
     | anode(list[NamedField] fields)
     | avoid()
     | avalue()
     | aloc()
     | adatetime()
     | alist(AType elmType)
     | aset(AType elmType)
     | abag(AType elmType)
     | atuple(AType elemType)
     | amap(AType keyType, AType valType)
     | arel(AType elemType)
     | alrel(AType elemType)
     | afunc(AType ret, AType formals, list[Keyword] kwFormals, bool varArgs=false, str deprecationMessage="")
     | auser(str uname, list[AType] parameters)
     | aalias(str aname, list[AType] parameters, AType aliased)
     | aanno(str aname, AType onType, AType annoType)

     | aadt(str adtName, list[AType] parameters, bool hasSyntax = false)
     | acons(AType adt, str consName, list[NamedField] fields, list[Keyword] kwFields)

     | amodule(str mname, str deprecationMessage="")
     | aparameter(str pname, AType bound)
     | areified(AType atype)
     | \start(AType symbol)
     | \lit(str string)
     | \cilit(str string)
     | \char-class(list[ACharRange] ranges) 
     | \empty()
     | \opt(AType symbol)
     | \iter(AType symbol)
     | \iter-star(AType symbol)
     | \iter-seps(AType symbol, list[AType] separators)
     | \iter-star-seps(AType symbol, list[AType] separators)
     | \alt(set[AType] alternatives)
     | \seq(list[AType] symbols)
     | \conditional(AType symbol, set[ACondition] conditions);

data ACharRange = range(int begin, int end);

data ACondition
     = \follow(AType atype)
     | \not-follow(AType atype)
     | \precede(AType atype)
     | \not-precede(AType atype)
     | \delete(AType atype)
     | \at-column(int column)
     | \begin-of-line()
     | \end-of-line()
     | \except(str label);

public AType sym2AType(Sym sym) {
  switch (sym) {
    case lang::rascal::\syntax::Rascal::nonterminal(Nonterminal n) :
      return AType::aadt("<n>", [], hasSyntax=true);
    case \start(Nonterminal n) :
       return AType::aadt("<n>", [], hasSyntax=true);   // TODO leave start somewhere
    case literal(StringConstant l):
      return AType::lit(unescape(l));
    case caseInsensitiveLiteral(CaseInsensitiveStringConstant l):
      return AType::cilit(unescape(l));
    case \parametrized(Nonterminal n, {Sym ","}+ syms) :
        return AType::aadt("<n>",separgs2ATypes(syms), hasSyntax=true);
    case labeled(Sym s, NonterminalLabel n) :
      return sym2AType(s)[label="<n>"];
    case optional(Sym s)  :
      return AType::opt(sym2AType(s));
    case characterClass(Class cc):
      return cc2ranges(cc);
    case parameter(Nonterminal n) :
      return AType::\aparameter("<n>", aadt("Tree", []));
    case empty() :
      return AType::\empty();
    case alternative(Sym first, {Sym "|"}+ alts) :
      return alt({sym2AType(first)} + {sym2AType(elem) | elem <- alts});
    case iterStar(Sym s)  :
      return AType::\iter-star(sym2AType(s));
    case iter(Sym s)  :
      return AType::\iter(sym2AType(s));
    case iterStarSep(Sym s, Sym sep)  :
      return AType::\iter-star-seps(sym2AType(s), [sym2AType(sep)]);
    case iterSep(Sym s, Sym sep)  :
      return AType::\iter-seps(sym2AType(s), [sym2AType(sep)]);
    case sequence(Sym first, Sym+ sequence) :
      return seq([sym2AType(first)] + [sym2AType(elem) | elem <- sequence]);
    case startOfLine(Sym s) :
      return conditional(sym2AType(s), {\begin-of-line()});
    case endOfLine(Sym s) :
      return conditional(sym2AType(s), {\end-of-line()});
    case column(Sym s, IntegerLiteral i) :
      return conditional(sym2AType(s), {\at-column(toInt("<i>"))});
    case follow(Sym s, Sym r) :
      return conditional(sym2AType(s), {\follow(sym2AType(r))});
    case notFollow(Sym s, Sym r) :
      return conditional(sym2AType(s), {\not-follow(sym2AType(r))});
    case precede(Sym s, Sym r) :
      return conditional(sym2AType(r), {\precede(sym2AType(s))});
    case notPrecede(Sym s, Sym r) :
      return conditional(sym2AType(r), {\not-precede(sym2AType(s))});
    case unequal(Sym s, Sym r) :
      return conditional(sym2AType(s), {\delete(sym2AType(r))});
    case except(Sym s, NonterminalLabel n):
      return conditional(sym2AType(s), {\except("<n>")});
    default:
      throw "sym2AType, missed a case <sym>";
  }
}

public list[AType] args2ATypes(Sym* args) {
  return [sym2AType(s) | Sym s <- args];
}

public list[AType] separgs2ATypes({Sym ","}+ args) {
  return [sym2AType(s) | Sym s <- args];
}



public AType flatten(AType at) =
  innermost visit(at) {
  // flattening rules for regular expressions
    case \seq([*AType a, \seq(list[AType] b), *AType c]) => \seq(a + b + c)
    case \alt({*AType a, \alt(set[AType] b)}) => \alt(a + b)
  // flattening for conditionals
    case \conditional(\conditional(AType s, set[ACondition] cs1), set[ACondition] cs2) => \conditional(s, cs1 + cs2)
  // if there is a nested conditional, lift the nested conditions toplevel and make the nested AType unconditional.
    
    case \conditional(AType s, set[ACondition] cs) =>
      ({
        if (c <- cs, c has symbol, c.atype is conditional) {
           \conditional(s, {c[symbol=c.symbol.symbol], *c.symbol.conditions, *(cs - {c})}); //SPLICING
        } else fail;
      })
  };


@doc{Convert qualified names into an abstract representation.}
public QName convertName(QualifiedName qn) {
    list[Str] parts = qn.names;
    if(size(parts) == 1){
        part = parts[0];
        return qualName("", part[0] == "\\" ? part[1..] : part);
    }
    list[Str] unescapedParts = [part[0] == "\\" ? part[1..] : part | part <- parts];
    return qualName(intercalate("::", unescapedParts[..-1]), unescapedParts[-1]);
}

@doc{Convert names into an abstract representation.}
public QName convertName(Name n) {
    part = "<n>";
    return qualName("", part[0] == "\\" ? part[1..] : part);
}

/*
public str prettyPrintName(QualifiedName qn){
    if ((QualifiedName)`<{Name "::"}+ nl>` := qn) {
        nameParts = [ (startsWith("<n>","\\") ? substring("<n>",1) : "<n>") | n <- nl ];
        return intercalate("::", nameParts);
    }
    throw "Unexpected syntax for qualified name: <qn>";
}

public str prettyPrintName(Name nm){
    return startsWith("<nm>","\\") ? substring("<nm>",1) : "<nm>";
}

public bool isQualified(QName qn) = !isEmpty(qn.qualifier);

str prettyPrintQName(QName qname) = isEmpty(qname.qualifier) ? qname.name : "<qname.qualifier>::<qname.name>";

@doc{Convert from the concrete to the abstract representations of Rascal basic types.}
public AType convertBasicType(BasicType t, TBuilder tb) {
    switch(t) {
        case (BasicType)`bool` : return abool();
        case (BasicType)`int` : return aint();
        case (BasicType)`rat` : return arat();
        case (BasicType)`real` : return areal();
        case (BasicType)`num` : return anum();
        case (BasicType)`str` : return astr();
        case (BasicType)`value` : return avalue();
        case (BasicType)`node` : return anode([]);
        case (BasicType)`void` : return avoid();
        case (BasicType)`loc` : return aloc();
        case (BasicType)`datetime` : return adatetime();

        case (BasicType)`list` : { tb.reportError(t, "Non-well-formed type, type should have one type argument"); return alist(avoid());  }
        case (BasicType)`set` : { tb.reportError(t, "Non-well-formed type, type should have one type argument"); return aset(avoid()); }
        case (BasicType)`bag` : { tb.reportError(t, "Non-well-formed type, type should have one type argument"); return abag(avoid()); }
        case (BasicType)`map` : { tb.reportError(t, "Non-well-formed type, type should have two type arguments"); return amap(avoid(),avoid()); }
        case (BasicType)`rel` : { tb.reportError(t, "Non-well-formed type, type should have one or more type arguments"); return arel(atypeList([])); }
        case (BasicType)`lrel` : { tb.reportError(t, "Non-well-formed type, type should have one or more type arguments"); return alrel(atypeList([])); }
        case (BasicType)`tuple` : { tb.reportError(t, "Non-well-formed type, type should have one or more type arguments"); return atuple(atypeList([])); }
        case (BasicType)`type` : { tb.reportError(t, "Non-well-formed type, type should have one type argument"); return areified(avoid()); }
    }
}

@doc{Convert from the concrete to the abstract representations of Rascal type arguments.}
public AType convertTypeArg(TypeArg ta, TBuilder tb) {
    switch(ta) {
        case (TypeArg) `<Type t>` : return convertType(t, tb);
        case (TypeArg) `<Type t> <Name n>` :  return convertType(t, tb)[label="<prettyPrintQName(convertName(n))>"];
    }
}

@doc{Convert lists of type arguments.}
public list[AType] convertTypeArgList({TypeArg ","}* tas, TBuilder tb)
    = [convertTypeArg(ta, tb) | ta <- tas];

@doc{Convert structured types, such as list<<int>>. Check here for certain syntactical
conditions, such as: all field names must be distinct in a given type; lists require
exactly one type argument; etc.}
public AType convertStructuredType(StructuredType st, TBuilder tb) {
    switch(st) {
        case (StructuredType) `list [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            if (size(l) == 1) {
                return makeListType(l[0]);
            } else {
                tb.reportError(st, "Non-well-formed type, type should have one type argument");
                return alist(avoid());
            }
        }

        case (StructuredType) `set [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            if (size(l) == 1) {
                return makeSetType(l[0]);
            } else {
                tb.reportError(st, "Non-well-formed type, type should have one type argument");
                return aset(avoid());
            }
        }

        case (StructuredType) `bag [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            if (size(l) == 1) {
                return abag(l[0]);
            } else {
                tb.reportError(st, "Non-well-formed type, type should have one type argument");
                return abag(avoid());
            }
        }

        case (StructuredType) `map [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            if (size(l) == 2) {
                dt = l[0]; rt = l[1];
                if (!isEmpty(dt.label) && !isEmpty(rt.label) && dt.label != rt.label) {
                    return makeMapType(dt, rt);
                } else if (!isEmpty(dt.label) && !isEmpty(rt.label) && dt.label == rt.label) {
                    tb.reportError(st,"Non-well-formed type, labels must be distinct");
                    return makeMapType(unset(dt, "label"),unset(rt,"label"));
                } else if (!isEmpty(dt.label) && isEmpty(rt.label)) {
                    tb.reportWarning(st, "Field name <fmt(dt.label)> ignored, field names must be provided for both fields or for none");
                    return makeMapType(unset(dt, "label"),rt);
                } else if (isEmpty(dt.label) && !isEmpty(rt.label)) {
                   tb.reportWarning(st, "Field name <fmt(rt.label)> ignored, field names must be provided for both fields or for none");
                    return makeMapType(dt, unset(rt, "label"));
                } else {
                    return makeMapType(dt,rt);
                }
            } else {
                tb.reportError(st, "Non-well-formed map type, type should have two type argument");
                return makeMapType(avoid(),avoid());
            }
        }

        case (StructuredType) `rel [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            labelsList = [tp.label | tp <- l];
            nonEmptyLabels = [ lbl | lbl <- labelsList, !isEmpty(lbl) ];
            distinctLabels = toSet(nonEmptyLabels);
            if (size(l) == size(distinctLabels)){
                return makeRelType(l);
            } else if(size(distinctLabels) == 0) {
                return makeRelType(l);
            } else if (size(distinctLabels) != size(nonEmptyLabels)) {
                tb.reportError(st, "Non-well-formed relation type, labels must be distinct");
                return makeRelType([unset(tp, "label") | tp <- l]);
            } else if (size(distinctLabels) > 0) {
                tb.reportWarning(st, "Field name ignored, field names must be provided for all fields or for none");
                return makeRelType([unset(tp, "label") | tp <- l]);
            }
        }

        case (StructuredType) `lrel [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            labelsList = [tp.label | tp <- l];
            nonEmptyLabels = [ lbl | lbl <- labelsList, !isEmpty(lbl) ];
            distinctLabels = toSet(nonEmptyLabels);
            if (size(l) == size(distinctLabels)){
                return makeListRelType(l);
            } else if(size(distinctLabels) == 0) {
                return makeListRelType(l);
            } else if (size(distinctLabels) != size(nonEmptyLabels)) {
                tb.reportError(st, "Non-well-formed list relation type, labels must be distinct");
                return makeListRelType([unset(tp, "label") | tp <- l]);
            } else if (size(distinctLabels) > 0) {
                tb.reportWarning(st, "Field name ignored, field names must be provided for all fields or for none");
                return makeListRelType([unset(tp, "label") | tp <- l]);
            }
        }

         case (StructuredType) `tuple [ < {TypeArg ","}+ tas > ]` : {
            l = convertTypeArgList(tas, tb);
            labelsList = [tp.label | tp <- l];
            nonEmptyLabels = [ lbl | lbl <- labelsList, !isEmpty(lbl) ];
            distinctLabels = toSet(nonEmptyLabels);
            if (size(l) == size(distinctLabels)){
                return makeTupleType(l);
            } else if(size(distinctLabels) == 0) {
                return makeTupleType(l);
            } else if (size(distinctLabels) != size(nonEmptyLabels)) {
                tb.reportError(st, "Non-well-formed tuple type, labels must be distinct");
                return makeTupleType([unset(tp, "label") | tp <- l]);
            } else if (size(distinctLabels) > 0) {
                tb.reportWarning(st, "Field name ignored, field names must be provided for all fields or for none");
                return makeTupleType([unset(tp, "label") | tp <- l]);
            }
        }

        case (StructuredType) `type [ < {TypeArg ","}+ tas > ]` : { // TODO
            l = convertTypeArgList(tas, tb);
            if (size(l) == 1) {
                if (!isEmpty(l[0].label)) {
                    tb.reportWarning(st, "Field name <fmt(l[0].label)> ignored");
                    return areified(l[0]);
                } else {
                    return areified(l[0]);
                }
            } else {
                tb.reportError(st, "Non-well-formed type, type should have one type argument");
                return areified(avoid());
            }
        }

        case (StructuredType) `<BasicType bt> [ < {TypeArg ","}+ tas > ]` : {
                tb.reportError(st, "Type <bt> does not accept type parameters");
                return avoid();
        }
    }
}

@doc{Convert Rascal function types into their abstract representation.}
public AType convertFunctionType(FunctionType ft, TBuilder tb) {
    if ((FunctionType) `<Type t> ( <{TypeArg ","}* tas> )` := ft) {
        l = convertTypeArgList(tas, tb);
        tp = convertType(t, tb);
        if (size(l) == 0) {
            return afunc(tp, atypeList([]), []);
        } else {
            labelsList = [tp.label | tp <- l];;
            nonEmptyLabels = [ lbl | lbl <- labelsList, !isEmpty(lbl) ];
            distinctLabels = toSet(nonEmptyLabels);
            if(size(distinctLabels) == 0)
                return afunc(tp, atypeList(l), []);
            if (size(l) == size(distinctLabels)) {
                return afunc(tp, atypeList(l), []);
            } else if (size(distinctLabels) > 0 && size(distinctLabels) != size(labelsList)) {
                 tb.reportError(ft, "Non-well-formed type, labels must be distinct");
                return afunc(tp, atypeList([unset(tp, "label") | tp <- l]), []);
            } else if (size(labels) > 0) {
                tb.reportWarning(ft, "Field name ignored, field names must be provided for all fields or for none");
                return afunc(tp, atypeList([unset(tp, "label") | tp <- l]), []);
            }
        }
    }
}

@doc{Convert Rascal user types into their abstract representation.}
public AType convertUserType(UserType ut, TBuilder tb) {
    switch(ut) {
        case (UserType) `<QualifiedName n>` : return auser(convertName(n).name,[]);
        case (UserType) `<QualifiedName n>[ <{Type ","}+ ts> ]` : {
            paramTypes = [convertType(ti, tb) | ti <- ts ];
            return auser(convertName(n).name, paramTypes);
        }
    }
}

public AType convertSymbol(Sym sym, TBuilder tb) = sym2AType(sym);

@doc{Convert Rascal type variables into their abstract representation.}
public AType convertTypeVar(TypeVar tv, TBuilder tb) {
    switch(tv) {
        case (TypeVar) `& <Name n>` : return aparameter("<prettyPrintQName(convertName(n))>",avalue());
        case (TypeVar) `& <Name n> \<: <Type tp>` : {
            return aparameter("<n>",convertType(tp, tb));
        }
    }
}

@doc{Convert Rascal data type selectors into an abstract representation.}
@todo{Implement once this is in use.}
public AType convertDataTypeSelector(DataTypeSelector dts, TBuilder tb) {
    switch(dts) {
        case (DataTypeSelector) `<QualifiedName n1> . <Name n2>` : throw "Not implemented";
    }
}

@doc{Main driver routine for converting Rascal types into abstract type representations.}
public AType convertType(Type t, TBuilder tb) {
    switch(t) {
        case (Type) `<BasicType bt>` : return convertBasicType(bt, tb);
        case (Type) `<StructuredType st>` : return convertStructuredType(st, tb);
        case (Type) `<FunctionType ft>` : return convertFunctionType(ft, tb);
        case (Type) `<TypeVar tv>` : return convertTypeVar(tv, tb);
        case (Type) `<UserType ut>` : return convertUserType(ut, tb);
        case (Type) `<DataTypeSelector dts>` : return convertDataTypeSelector(dts, tb);
        case (Type) `<Sym sym>` : return convertSymbol(sym, tb);
        case (Type) `( <Type tp> )` : return convertType(tp, tb);
        default : { throw "Error in convertType, unexpected type syntax: <t>"; }
    }
}*/