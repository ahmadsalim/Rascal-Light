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
data Nonterminal = mknonterminal(str label); 
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

     | aadt(str adtName, list[AType] parameters, bool hasSyntax)
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

data UnexpectedSymbolException = unexpectedsymexc();
public AType sym2AType(Sym sym) {
  switch (sym) {
    case nonterminal(Nonterminal n) :
      return aadt(n.label, [], true);
    case \start(Nonterminal n) :
       return aadt(n.label, [], true);   // TODO leave start somewhere
    case literal(str l):
      return lit(l); //Simplified
    case caseInsensitiveLiteral(str l):
      return cilit(l); //Simplified
    case \parametrized(Nonterminal n, list[Sym] syms) :
        return aadt(n.label,separgs2ATypes(syms), true);
    case labeled(Sym s, NonterminalLabel n): {
      AType at = sym2AType(s);
      at.label = n.label;
      return at;
    }
    case optional(Sym s)  :
      return opt(sym2AType(s));
    case characterClass(Class cc):
      return cc2ranges(cc);
    case parameter(Nonterminal n) :
      return \aparameter(n.label, aadt("Tree", [], false));
    case empty() :
      return \empty();
    case alternative(Sym first, list[Sym] alts) : {
      list[AType] elems = {};
      for (elem <- alts)
        elems = elems + sym2AType(elem);
      return alt({sym2AType(first)} + elems);
    }
    case iterStar(Sym s)  :
      return \iter-star(sym2AType(s));
    case iter(Sym s)  :
      return \iter(sym2AType(s));
    case iterStarSep(Sym s, Sym sep)  :
      return \iter-star-seps(sym2AType(s), [sym2AType(sep)]);
    case iterSep(Sym s, Sym sep)  :
      return \iter-seps(sym2AType(s), [sym2AType(sep)]);
    case sequence(Sym first, list[Sym] sequence): {
      list[AType] elems = [];
      for (elem <- sequence)
        elems = elems + sym2AType(elem);
      return seq([sym2AType(first)] + elems);
    }
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
      return conditional(sym2AType(s), {\except(n.label)});
    default:
      throw unexpectedsymexc();
  }
}

public list[AType] args2ATypes(list[Sym] args) {
  list[AType] types = [];
  for (s <- args)
    types = types + sym2AType(s);
}

public list[AType] separgs2ATypes(list[Sym] args) {
  list[AType] types = [];
  for (s <- args)
    types = types + sym2AType(s);
}

public str intercalate(str sep, list[str] parts) {
  switch (parts) {
     case []: return "";
     case [x, *xs]: {
       str newstr = "";
       for (x2 <- xs)
         newstr = newstr + sep + x2;
       return x + newstr;
    }
  }
}

@doc{Convert qualified names into an abstract representation.}
public QName convertName(QualifiedName qn) {
    return qualName(intercalate("::", qn.names), qn.names); //Simplified
}

@doc{Convert names into an abstract representation.}
public QName convertName(str n) {
    return qualName("", n); //Simplified
}

str prettyPrintQName(QName qname) = isEmpty(qname.qualifier) ? qname.name : (qname.qualifier + "::" + qname.name);

data BasicTypeException = btexc();

@doc{Convert from the concrete to the abstract representations of Rascal basic types.}
public AType convertBasicType(BasicType t/*, TBuilder tb*/) {
    switch(t) {
        case \bool(): return abool();
        case \int(): return aint();
        case rational(): return arat();
        case \real(): return areal();
        case \num(): return anum();
        case string(): return astr();
        case \value(): return avalue();
        case \node(): return anode([]);
        case \void(): return avoid();
        case \loc(): return aloc();
        case dateTime(): return adatetime();

        case \list(): { /*tb.reportError(t, "Non-well-formed type, type should have one type argument");*/ throw btexc(); return alist(avoid());  }
        case \set(): { /*tb.reportError(t, "Non-well-formed type, type should have one type argument");*/ throw btexc(); return aset(avoid()); }
        case \bag(): { /*tb.reportError(t, "Non-well-formed type, type should have one type argument");*/ throw btexc(); return abag(avoid()); }
        case \map(): { /*tb.reportError(t, "Non-well-formed type, type should have two type arguments");*/ throw btexc(); return amap(avoid(),avoid()); }
        case relation(): { /*tb.reportError(t, "Non-well-formed type, type should have one or more type arguments");*/ throw btexc(); return arel(atypeList([])); }
        case listRelation(): { /*tb.reportError(t, "Non-well-formed type, type should have one or more type arguments");*/ throw btexc(); return alrel(atypeList([])); }
        case \tuple(): { /*tb.reportError(t, "Non-well-formed type, type should have one or more type arguments");*/ throw btexc(); return atuple(atypeList([])); }
        case \type(): { /*tb.reportError(t, "Non-well-formed type, type should have one type argument");*/ throw btexc(); return areified(avoid()); }
    }
}

@doc{Convert from the concrete to the abstract representations of Rascal type arguments.}
public AType convertTypeArg(TypeArg ta/*, TBuilder tb*/) {
    switch(ta) {
        case \default(t): return convertType(t/*, tb*/);
        case named(t,n):  { 
           AType at = convertType(t/*, tb*/);
           at.label = prettyPrintQName(convertName(n));
           return at;
        }
    }
}

@doc{Convert lists of type arguments.}
public list[AType] convertTypeArgList(list[TypeArg] tas/*, TBuilder tb*/) {
  list[AType] types = [];
  for (ta <- tas)
    types = types + convertTypeArg(ta/*, tb*/);
}

data LabellingException = labelexc();
data StructuredTypeException = stexc();


// makeXType from here: https://github.com/usethesource/rascal-core/blob/3f7243ac017b3e08d3bc327bfb242334233bf241/src/io/org/rascalmpl/library/lang/rascalcore/check/ATypeUtils.rsc

@doc{Unwraps parameters and conditionals from a type.}
AType unwrapType(AType t) {
  switch(t) {
    case p: aparameter(_,tvb):
      if (p.label?) {
        AType nt = unwrapType(tvb);
        nt.label = p.label;
        return nt;
      } else return unwrapType(tvb);
    case \conditional(AType sym,  set[ACondition] _): return unwrapType(sym);
    case _: return t;
  }
}


@doc{Determine if the given type is a tuple.}
bool isTupleType(AType tp) {
  switch(tp) {
    case aparameter(_,AType tvb): return isTupleType(tvb);
    case atuple(_): return true;
    case _: return false;
  }
}

@doc{Create a new list type, given the element type of the list.}
AType makeListType(AType elementType) {
    return isTupleType(elementType) ? makeListRelTypeFromTuple(elementType) : alist(elementType); 
    // TODO consider converting isTupleType to something that returns a refined shape for better verification
} 

AType makeSetType(AType elementType) {
    return isTupleType(elementType) ? makeRelTypeFromTuple(elementType) : aset(elementType);
}

@doc{Create a new map type, given the types of the domain and range. Check to make sure field names are used consistently.}
AType makeMapType(AType domain, AType range) {
    if(!isEmpty(domain.label) && !isEmpty(range.label)){
        if(domain.label != range.label) return amap(domain, range);
        throw rascalCheckerInternalError("The field names of the map domain and range must be distinct; found <fmt(domain.label)>");
    }
    else if(!isEmpty(domain.label)) return amap(unset(domain,"label"),range);
    else if(!isEmpty(range.label)) return amap(domain,unset(range, "label"));
    return amap(domain, range);
}

@doc{Get the fields of a tuple as a list.}
public list[AType] getTupleFields(AType t) {
    switch(unwrapType(t)) {
      case atuple(atypeList(tas)): return tas; // Potential real error here: Make tool catch it!
      case _: throw rascalCheckerInternalError("Cannot get tuple fields from type <fmt(t)>"); 
    }
}

@doc{Create a new rel type, given the element types of the fields. Check any given labels for consistency.}
AType makeRelType(list[AType] elementTypes) {
    set[str] labels = {};
    for (tp <- elementTypes)
      if (!isEmpty(tp.label))
        labels = labels + tp.label;
    if (size(labels) == 0 || size(labels) == size(elementTypes))
        return arel(atypeList(elementTypes));
    else
        throw rascalCheckerInternalError("For rel types, either all fields much be given a distinct label or no fields should be labeled."); 
}

@doc{Create a new list rel type, given the element types of the fields. Check any given labels for consistency.}
AType makeListRelType(list[AType] elementTypes) {
    set[str] labels = {};
    for (tp <- elementTypes)
      if (!isEmpty(tp.label))
        labels = labels + tp.label;
    if (size(labels) == 0 || size(labels) == size(elementTypes)) 
        return alrel(atypeList(elementTypes));
    else
        throw rascalCheckerInternalError("For lrel types, either all fields much be given a distinct label or no fields should be labeled."); 
}

@doc{Create a new tuple type, given the element types of the fields. Check any given labels for consistency.}
AType makeTupleType(list[AType] elementTypes) {
    set[str] labels = {};
    for (tp <- elementTypes)
      if (!isEmpty(tp.label))
        labels = labels + tp.label;
    if(size(labels) > 0 && size(labels) != size(elementTypes)) {
        list[AType] nets = [];
        for (e <- elementTypes)
          nets = nets + unset(e, "label");
        elementTypes = nets;
    }
    return atuple(atypeList(elementTypes));
}

@doc{Create a new lrel type based on a given tuple type.}
AType makeListRelTypeFromTuple(AType t) = alrel(atypeList(getTupleFields(t)));

@doc{Create a new rel type based on a given tuple type.}
AType makeRelTypeFromTuple(AType t) = arel(atypeList(getTupleFields(t)));


@doc{Convert structured types, such as list<<int>>. Check here for certain syntactical
conditions, such as: all field names must be distinct in a given type; lists require
exactly one type argument; etc.}
public AType convertStructuredType(StructuredType st/*, TBuilder tb*/) {
    switch(st) {
        case \default(\list(), tas): {
            l = convertTypeArgList(tas/*, tb*/);
            switch (l) {
            	case [ta]: return makeListType(ta);
            	case _: {
            	  /*tb.reportError(st, "Non-well-formed type, type should have one type argument");*/ throw stexc();
                  return alist(avoid());
            	}
            }
        }

        case \default(\set(), tas): {
            l = convertTypeArgList(tas/*, tb*/);
            switch (l) {
            	case [ta]: return makeSetType(ta);
            	case _: {
            	  /*tb.reportError(st, "Non-well-formed type, type should have one type argument");*/ throw stexc();
                  return aset(avoid());
            	}
            }
        }

        case \default(\bag(), tas): {
            l = convertTypeArgList(tas/*, tb*/);
             switch (l) {
            	case [ta]: return abag(ta);
            	case _: {
            	  /*tb.reportError(st, "Non-well-formed type, type should have one type argument");*/ throw stexc();
                  return abag(avoid());
            	}
            }
        }

        case \default(\map(), tas): {
            l = convertTypeArgList(tas/*, tb*/);
               switch (l) {
            	case [dt,rt]:
            		if (!isEmpty(dt.label) && !isEmpty(rt.label) && dt.label != rt.label) {
                    	return makeMapType(dt, rt);
	                } else if (!isEmpty(dt.label) && !isEmpty(rt.label) && dt.label == rt.label) {
	                    /*tb.reportError(st,"Non-well-formed type, labels must be distinct");*/ throw labelexc();
	                    return makeMapType(unset(dt, "label"),unset(rt,"label"));
	                } else if (!isEmpty(dt.label) && isEmpty(rt.label)) {
	                    /*tb.reportWarning(st, "Field name <fmt(dt.label)> ignored, field names must be provided for both fields or for none");*/ throw labelexc();
	                    return makeMapType(unset(dt, "label"),rt);
	                } else if (isEmpty(dt.label) && !isEmpty(rt.label)) {
	                    /*tb.reportWarning(st, "Field name <fmt(rt.label)> ignored, field names must be provided for both fields or for none");*/ throw labelexc();
	                    return makeMapType(dt, unset(rt, "label"));
	                } else {
	                    return makeMapType(dt,rt);
	                }
            	case _: {
            	  /*tb.reportError(st, "Non-well-formed map type, type should have two type argument");*/ throw stexc();
                  return return makeMapType(avoid(),avoid());
            	}
            }
        }

        case \default(relation(), tas) : {
            l = convertTypeArgList(tas/*, tb*/);
            list[str] labelsList = [];
            for (tp <- l)
              labelsList = labelsList + tp.label;
            list[str] nonEmptyLabels = [];
            for (lbl <- labelsList)
              if (!isEmpty(lbl))
                nonEmptyLabels = nonEmptyLabels + lbl;
            set[str] distinctLabels = toSet(nonEmptyLabels);
            if (size(l) == size(distinctLabels)){
                return makeRelType(l);
            } else if(size(distinctLabels) == 0) {
                return makeRelType(l);
            } else if (size(distinctLabels) != size(nonEmptyLabels)) {
                /*tb.reportError(st, "Non-well-formed relation type, labels must be distinct");*/ throw labelexc();
                list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
                return makeRelType(types);
            } else if (size(distinctLabels) > 0) {
                /*tb.reportWarning(st, "Field name ignored, field names must be provided for all fields or for none");*/ throw labelexc();
                list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
                return makeRelType(types);
            }
        }

        case \default(listRelation(), tas): {
            l = convertTypeArgList(tas/*, tb*/);
            list[str] labelsList = [];
            for (tp <- l)
              labelsList = labelsList + tp.label;
            list[str] nonEmptyLabels = [];
            for (lbl <- labelsList)
              if (!isEmpty(lbl))
                nonEmptyLabels = nonEmptyLabels + lbl;
            set[str] distinctLabels = toSet(nonEmptyLabels);
            if (size(l) == size(distinctLabels)){
                return makeListRelType(l);
            } else if(size(distinctLabels) == 0) {
                return makeListRelType(l);
            } else if (size(distinctLabels) != size(nonEmptyLabels)) {
                /*tb.reportError(st, "Non-well-formed list relation type, labels must be distinct");*/ throw labelexc();
                list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
                return makeListRelType(types);
            } else if (size(distinctLabels) > 0) {
                /*tb.reportWarning(st, "Field name ignored, field names must be provided for all fields or for none");*/ throw labelexc();
                list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
                return makeListRelType(types);
            }
        }

         case \default(\tuple(), tas): {
            l = convertTypeArgList(tas/*, tb*/);
            list[str] labelsList = [];
            for (tp <- l)
              labelsList = labelsList + tp.label;
            list[str] nonEmptyLabels = [];
            for (lbl <- labelsList)
              if (!isEmpty(lbl))
                nonEmptyLabels = nonEmptyLabels + lbl;
            set[str] distinctLabels = toSet(nonEmptyLabels);
            if (size(l) == size(distinctLabels)){
                return makeTupleType(l);
            } else if(size(distinctLabels) == 0) {
                return makeTupleType(l);
            } else if (size(distinctLabels) != size(nonEmptyLabels)) {
                /*tb.reportError(st, "Non-well-formed tuple type, labels must be distinct");*/ throw labelexc();
                list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
                return makeTupleType(types);
            } else if (size(distinctLabels) > 0) {
                /*tb.reportWarning(st, "Field name ignored, field names must be provided for all fields or for none");*/ throw labelexc();
                list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
                return makeTupleType(types);
            }
        }

        case \default(\type(), tas): { // TODO
            l = convertTypeArgList(tas/*, tb*/);
            switch (l) {
            	case [ta]: 
	            	if (!isEmpty(ta.label)) {
	                    /*tb.reportWarning(st, "Field name <fmt(l[0].label)> ignored");*/
	                    return areified(ta);
	                } else {
	                    return areified(ta);
	                }
            	case _: {
            	  /*tb.reportError(st, "Non-well-formed type, type should have one type argument");*/ throw stexc();
                  return areified(avoid());
            	}
            }
        }

        case \default(bt, tas): {
                /*tb.reportError(st, "Type <bt> does not accept type parameters");*/ throw stexc();
                return avoid();
        }
    }
}

@doc{Convert Rascal function types into their abstract representation.}
public AType convertFunctionType(FunctionType ft/*, TBuilder tb*/) {
	switch(ft) {
	  case typeArguments(t, tas): {
	    l = convertTypeArgList(tas/*, tb*/);
	    tp = convertType(t/*, tb*/);
	    if (size(l) == 0) {
	        return afunc(tp, atypeList([]), []);
	    } else {
	        list[str] labelsList = [];
            for (tp <- l)
              labelsList = labelsList + tp.label;
            list[str] nonEmptyLabels = [];
            for (lbl <- labelsList)
              if (!isEmpty(lbl))
                nonEmptyLabels = nonEmptyLabels + lbl;
            set[str] distinctLabels = toSet(nonEmptyLabels);
	        if(size(distinctLabels) == 0)
	            return afunc(tp, atypeList(l), []);
	        if (size(l) == size(distinctLabels)) {
	            return afunc(tp, atypeList(l), []);
	        } else if (size(distinctLabels) > 0 && size(distinctLabels) != size(labelsList)) {
	            /*tb.reportError(ft, "Non-well-formed type, labels must be distinct");*/ throw labelexc();
	            list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
	            return afunc(tp, atypeList(types), []);
	        } else if (size(labels) > 0) {
	            /*tb.reportWarning(ft, "Field name ignored, field names must be provided for all fields or for none");*/ throw labelexc();
	            list[AType] types = [];
                for (tp <- l)
                  types = types + unset(tp, "label");
	            return afunc(tp, atypeList(types), []);
	        }
	    }
	  }
	}
}

@doc{Convert Rascal user types into their abstract representation.}
public AType convertUserType(UserType ut, TBuilder tb) {
    switch(ut) {
        case name(n): return auser(convertName(n).name,[]);
        case parameteric(n, ts): {
            list[AType] paramTypes = [];
            for (ti <- ts)
              paramTypes = paramTypes + convertType(ti, tb);
            return auser(convertName(n).name, paramTypes);
        }
    }
}

public AType convertSymbol(Sym sym, TBuilder tb) = sym2AType(sym);

@doc{Convert Rascal type variables into their abstract representation.}
public AType convertTypeVar(TypeVar tv, TBuilder tb) {
    switch(tv) {
        case free(n): return aparameter(prettyPrintQName(convertName(n)), avalue());
        case bounded(n, tp): {
            return aparameter(n,convertType(tp, tb));
        }
    }
}

data NotImplementedException = notimplexc();
@doc{Convert Rascal data type selectors into an abstract representation.}
@todo{Implement once this is in use.}
public AType convertDataTypeSelector(DataTypeSelector dts, TBuilder tb) {
    switch(dts) {
        case selector(n1, n2): throw notimplexc();
    }
}

data UnexpectedTypeException = unexpectedtypeexc();

@doc{Main driver routine for converting Rascal types into abstract type representations.}
public AType convertType(Type t/*, TBuilder tb*/) {
    switch(t) {
        case basic(bt): return convertBasicType(bt/*, tb*/);
        case structured(st): return convertStructuredType(st/*, tb*/);
        case function(ft): return convertFunctionType(ft/*, tb*/);
        case variable(tv): return convertTypeVar(tv/*, tb*/);
        case user(ut): return convertUserType(ut/*, tb*/);
        case selector(dts): return convertDataTypeSelector(dts/*, tb*/);
        case symbol(sym): return convertSymbol(sym/*, tb*/);
        case \bracket(tp): return convertType(tp/*, tb*/);
        case _ : throw unexpectedtypeexc();
    }
}