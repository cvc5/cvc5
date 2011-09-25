package cvc3;

import java.util.*;

public class Expr extends Embedded {
    // jni methods
    private static native boolean
	jniEquals(Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native String
	jniToString(Object Expr) throws Cvc3Exception;
    private static native void
	jniPrint(Object Expr, String InputLanguage, boolean dagify) throws Cvc3Exception;
    private static native int
	jniHash(Object Expr) throws Cvc3Exception;

    private static native String
    jniGetKind(Object Expr) throws Cvc3Exception;
    
    private static native boolean
	jniIsFalse(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsTrue(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBoolConst(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsVar(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBoundVar(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsString(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsClosure(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsQuantifier(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsLambda(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsApply(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsSymbol(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsTheorem(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsType(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsTerm(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsAtomic(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsAtomicFormula(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsAbsAtomicFormula(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsLiteral(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsAbsLiteral(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBoolConnective(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsPropAtom(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsPropLiteral(Object Expr) throws Cvc3Exception;
    private static native boolean
    jniIsArrayLiteral(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsEq(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsNot(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsAnd(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsOr(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsITE(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsIff(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsImpl(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsXor(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsForall(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsExists(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsRational(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsUminus(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsPlus(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsMinus(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsMult(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsPow(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsDivide(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsLt(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsLe(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsGt(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsGe(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsSkolem(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsRead(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsWrite(Object Expr) throws Cvc3Exception;

    private static native String
	jniGetName(Object Expr) throws Cvc3Exception;
    private static native String
	jniGetUid(Object Expr) throws Cvc3Exception;
    private static native String
	jniGetString(Object Expr) throws Cvc3Exception;
    private static native Object[]
	jniGetVars(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetExistential(Object Expr) throws Cvc3Exception;
    private static native int
	jniGetBoundIndex(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetBody(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetRational(Object Expr) throws Cvc3Exception;
    private static native Object[][]
    jniGetTriggers(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetTheorem(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetType(Object Expr) throws Cvc3Exception;
    private static native Object
	jniMkOp(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetOp(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetOpExpr(Object Expr) throws Cvc3Exception;

    private static native boolean
	jniIsNull(Object Expr) throws Cvc3Exception;
    private static native int
	jniArity(Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetKid(Object Expr, int i) throws Cvc3Exception;
    private static native Object[]
	jniGetKids(Object Expr) throws Cvc3Exception;

    private static native Object
    jniSubstExpr(Object Expr, Object[] oldExprs, Object[] newExprs) throws Cvc3Exception;

    private static native boolean
	jniIsBvLt(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvLe(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvGt(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvGe(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvPlus(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvSub(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvConst(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvExtract(Object Expr) throws Cvc3Exception;
    private static native boolean
	jniIsBvConcat(Object Expr) throws Cvc3Exception;


    /// Constructor

    public Expr(Object Expr, EmbeddedManager embeddedManager) {
	super(Expr, embeddedManager);
    }


    /// API (immutable)


    // 'Problem' with equals/hashCode:
    // this is based on the wrapped c++ expressions.
    // as a consequence two Expr objects are equal iff
    // the wrapped expression is equal,
    // and are indistinguishable for example in a HashMap.
    
    public boolean equals(Object o) {
	if (this == o) return true;

	if (!(o instanceof Expr)) return false;
	boolean result = false;
	try {
	    result = jniEquals(embedded(), ((Embedded)o).embedded());
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	return result;
    } 

    // must return the same hash code for two objects if equals returns true
    public int hashCode() {
	try {
	    if (!jniIsNull(embedded())) {
		return jniHash(embedded());
	    }
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	assert(false);
	return 0;
    }
    
    public Expr subst(List oldExprs, List newExprs) throws Cvc3Exception {
      assert(JniUtils.listInstanceof(oldExprs, Expr.class));      
      assert(JniUtils.listInstanceof(newExprs, Expr.class));      
      return new Expr(jniSubstExpr(embedded(), JniUtils.unembedList(oldExprs),
        JniUtils.unembedList(newExprs)), embeddedManager());
    }
    
    public String toString() {
	String result = "";
	try {
	    result = jniToString(embedded());
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	return result;
    }

    public void print(InputLanguage lang, boolean dagify) throws Cvc3Exception {
	jniPrint(embedded(), lang.toString(), dagify);
    }

    public void print(boolean dagify) throws Cvc3Exception {
	print(InputLanguage.PRESENTATION, dagify);
    }

    public void print() throws Cvc3Exception {
      print(false);
    }

    public String getKind() throws Cvc3Exception {
      return jniGetKind(embedded());
    }
    
    // Core expression testers


    public boolean isFalse() throws Cvc3Exception {
	return jniIsFalse(embedded());
    }

    public boolean isTrue() throws Cvc3Exception {
	return jniIsTrue(embedded());
    }

    public boolean isBooleanConst() throws Cvc3Exception {
	return jniIsBoolConst(embedded());
    }

    public boolean isVar() throws Cvc3Exception {
	return jniIsVar(embedded());
    }

    public boolean isBoundVar() throws Cvc3Exception {
	return jniIsBoundVar(embedded());
    }

    public boolean isString() throws Cvc3Exception {
	return jniIsString(embedded());
    }

    public boolean isClosure() throws Cvc3Exception {
	return jniIsClosure(embedded());
    }

    public boolean isQuantifier() throws Cvc3Exception {
	return jniIsQuantifier(embedded());
    }

    public boolean isLambda() throws Cvc3Exception {
	return jniIsLambda(embedded());
    }

    public boolean isApply() throws Cvc3Exception {
	return jniIsApply(embedded());
    }

    public boolean isSymbol() throws Cvc3Exception {
	return jniIsSymbol(embedded());
    }

    public boolean isTheorem() throws Cvc3Exception {
	return jniIsTheorem(embedded());
    }

    public boolean isType() throws Cvc3Exception {
	return jniIsType(embedded());
    }




    public boolean isTerm() throws Cvc3Exception {
	return jniIsTerm(embedded());
    }

    public boolean isAtomic() throws Cvc3Exception {
	return jniIsAtomic(embedded());
    }

    public boolean isAtomicFormula() throws Cvc3Exception {
	return jniIsAtomicFormula(embedded());
    }

    public boolean isAbsAtomicFormula() throws Cvc3Exception {
	return jniIsAbsAtomicFormula(embedded());
    }

    public boolean isLiteral() throws Cvc3Exception {
	return jniIsLiteral(embedded());
    }

    public boolean isAbsLiteral() throws Cvc3Exception {
	return jniIsAbsLiteral(embedded());
    }

    public boolean isBoolConnective() throws Cvc3Exception {
	return jniIsBoolConnective(embedded());
    }

    public boolean isPropAtom() throws Cvc3Exception {
	return jniIsPropAtom(embedded());
    }

    public boolean isPropLiteral() throws Cvc3Exception {
	return jniIsPropLiteral(embedded());
    }

    public boolean isArrayLiteral() throws Cvc3Exception {
      return jniIsArrayLiteral(embedded());
    }

    public boolean isEq() throws Cvc3Exception {
	return jniIsEq(embedded());
    }

    public boolean isNot() throws Cvc3Exception {
	return jniIsNot(embedded());
    }


    public boolean isAnd() throws Cvc3Exception {
	return jniIsAnd(embedded());
    }


    public boolean isOr() throws Cvc3Exception {
	return jniIsOr(embedded());
    }


    public boolean isITE() throws Cvc3Exception {
	return jniIsITE(embedded());
    }


    public boolean isIff() throws Cvc3Exception {
	return jniIsIff(embedded());
    }


    public boolean isImpl() throws Cvc3Exception {
	return jniIsImpl(embedded());
    }


    public boolean isXor() throws Cvc3Exception {
	return jniIsXor(embedded());
    }


    public boolean isForall() throws Cvc3Exception {
	return jniIsForall(embedded());
    }


    public boolean isExists() throws Cvc3Exception {
	return jniIsExists(embedded());
    }


    public boolean isRational() throws Cvc3Exception {
	return jniIsRational(embedded());
    }

    public boolean isUminus() throws Cvc3Exception {
	return jniIsUminus(embedded());
    }

    public boolean isPlus() throws Cvc3Exception {
	return jniIsPlus(embedded());
    }

    public boolean isMinus() throws Cvc3Exception {
	return jniIsMinus(embedded());
    }

    public boolean isMult() throws Cvc3Exception {
	return jniIsMult(embedded());
    }

    public boolean isPow() throws Cvc3Exception {
	return jniIsPow(embedded());
    }

    public boolean isDivide() throws Cvc3Exception {
	return jniIsDivide(embedded());
    }

    public boolean isLt() throws Cvc3Exception {
	return jniIsLt(embedded());
    }

    public boolean isLe() throws Cvc3Exception {
	return jniIsLe(embedded());
    }

    public boolean isGt() throws Cvc3Exception {
	return jniIsGt(embedded());
    }

    public boolean isGe() throws Cvc3Exception {
	return jniIsGe(embedded());
    }

    public boolean isSkolem() throws Cvc3Exception {
	return jniIsSkolem(embedded());
    }

    public boolean isRead() throws Cvc3Exception {
	return jniIsRead(embedded());
    }

    public boolean isWrite() throws Cvc3Exception {
	return jniIsWrite(embedded());
    }

    public boolean isBvLe() throws Cvc3Exception {
	return jniIsBvLe(embedded());
    }

    public boolean isBvLt() throws Cvc3Exception {
	return jniIsBvLt(embedded());
    }

    public boolean isBvGe() throws Cvc3Exception {
	return jniIsBvGe(embedded());
    }

    public boolean isBvGt() throws Cvc3Exception {
	return jniIsBvGt(embedded());
    }

    public boolean isBvPlus() throws Cvc3Exception {
	return jniIsBvPlus(embedded());
    }

    public boolean isBvSub() throws Cvc3Exception {
	return jniIsBvSub(embedded());
    }

    public boolean isBvConstant() throws Cvc3Exception {
	return jniIsBvConst(embedded());
    }

    public boolean isBvConcat() throws Cvc3Exception {
	return jniIsBvConcat(embedded());
    }

    public boolean isBvExtract() throws Cvc3Exception {
	return jniIsBvExtract(embedded());
    }


    public String getName() throws Cvc3Exception {
	assert(!jniIsNull(embedded()));
	return jniGetName(embedded());
    }

    public String getUid() throws Cvc3Exception {
	assert(jniIsBoundVar(embedded()));
	return jniGetUid(embedded());
    }

    public String getString() throws Cvc3Exception {
	assert(jniIsString(embedded()));
	return jniGetString(embedded());
    }

    public List getVars() throws Cvc3Exception {
	assert(jniIsClosure(embedded()));
	Object[] vars = jniGetVars(embedded());
	return JniUtils.embedList(vars, Expr.class, embeddedManager());
    }

    public List getTriggers() throws Cvc3Exception {
      assert (jniIsClosure(embedded()));
      return JniUtils.embedListList(jniGetTriggers(embedded()), Expr.class, embeddedManager());
    }
  
    public Expr getExistential() throws Cvc3Exception {
	assert(jniIsSkolem(embedded()));
	return new Expr(jniGetExistential(embedded()), embeddedManager());
    }

    public int getBoundIndex() throws Cvc3Exception {
	assert(jniIsSkolem(embedded()));
	return jniGetBoundIndex(embedded());
    }
 
    public Expr getBody() throws Cvc3Exception {
	assert(jniIsClosure(embedded()));
	return new Expr(jniGetBody(embedded()), embeddedManager());
    }

    public Rational getRational() throws Cvc3Exception {
	assert(isRational());
	return new Rational(jniGetRational(embedded()), embeddedManager());
    }

    public Theorem getTheorem() throws Cvc3Exception {
	assert(jniIsTheorem(embedded()));
	return new Theorem(jniGetTheorem(embedded()), embeddedManager());
    }

    public TypeMut getType() throws Cvc3Exception {
	return new TypeMut(jniGetType(embedded()), embeddedManager());
    }

    public OpMut mkOp() throws Cvc3Exception {
		return new OpMut(jniMkOp(embedded()), embeddedManager());
	}
    
    public OpMut getOp() throws Cvc3Exception {
	return new OpMut(jniGetOp(embedded()), embeddedManager());
    }

    public ExprMut getOpExpr() throws Cvc3Exception {
	return new ExprMut(jniGetOpExpr(embedded()), embeddedManager());
    }

    public boolean isNull() throws Cvc3Exception {
	return jniIsNull(embedded());
    }

    public int arity() throws Cvc3Exception {
	return jniArity(embedded());
    }

    public Expr getChild(int i) throws Cvc3Exception {
	assert(i >= 0 && i < arity());
	return new Expr(jniGetKid(embedded(), i), embeddedManager());
    }

    public List getChildren() throws Cvc3Exception {
        return JniUtils.embedList(jniGetKids(embedded()), Expr.class, embeddedManager());
    }
}
