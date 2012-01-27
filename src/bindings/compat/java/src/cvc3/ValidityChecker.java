package cvc3;

import java.util.*;

import cvc3.Expr;
import cvc3.JniUtils;

public class ValidityChecker extends Embedded {
    // jni methods
    private static native Object
	jniCreate1() throws Cvc3Exception;
    private static native Object
	jniCreate2(Object Flags) throws Cvc3Exception;
    private static native Object
	jniCreateFlags() throws Cvc3Exception;
    private static native Object
	jniGetFlags(Object ValidityChecker) throws Cvc3Exception;


    private static native Object
	jniBoolType(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniRealType(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniIntType(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniSubrangeType(Object ValidityChecker, Object lExpr, Object rExpr) throws Cvc3Exception;
    private static native Object
	jniSubtypeType(Object ValidityChecker, Object predExpr, Object witnessExpr) throws Cvc3Exception;
    private static native Object
	jniTupleType1(Object ValidityChecker, Object Type0, Object Type1) throws Cvc3Exception;
    private static native Object
	jniTupleType2(Object ValidityChecker, Object Type0, Object Type1, Object Type2) throws Cvc3Exception;
    private static native Object
	jniTupleType3(Object ValidityChecker, Object[] Types) throws Cvc3Exception;
    private static native Object
	jniRecordType1(Object ValidityChecker, String field, Object Type) throws Cvc3Exception;
    private static native Object
	jniRecordType2(Object ValidityChecker, String field0, Object Type0,
		       String field1, Object Type1) throws Cvc3Exception;
    private static native Object
	jniRecordType3(Object ValidityChecker, String field0, Object Type0,
		       String field1, Object Type1, String field2, Object Type2) throws Cvc3Exception;
    private static native Object
	jniRecordType4(Object ValidityChecker, Object[] fields, Object[] types) throws Cvc3Exception;
    private static native Object
	jniDataType1(Object ValidityChecker, String name, String constructor,
		     Object[] selectors, Object[] types) throws Cvc3Exception;
    private static native Object
	jniDataType2(Object ValidityChecker, String name, Object[] constructors,
		     Object[] selectors, Object[] types) throws Cvc3Exception;
    private static native Object[]
	jniDataType3(Object ValidityChecker, Object[] names, Object[] constructors,
		     Object[] selectors, Object[] types) throws Cvc3Exception;
    private static native Object
	jniAnyType(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
    jniArrayLiteral(Object ValidityChecker, Object indexVar, Object bodyExpr) throws Cvc3Exception;
    private static native Object
	jniArrayType(Object ValidityChecker, Object TypeIndex, Object TypeData) throws Cvc3Exception;
    private static native Object
	jniBitvecType(Object ValidityChecker, int n) throws Cvc3Exception;
    private static native Object
	jniFunType1(Object ValidityChecker, Object typeDom, Object TypeRan) throws Cvc3Exception;
    private static native Object
	jniFunType2(Object ValidityChecker, Object[] typeDom, Object TypeRan) throws Cvc3Exception;
    private static native Object
	jniCreateType1(Object ValidityChecker, String typeName) throws Cvc3Exception;
    private static native Object
	jniCreateType2(Object ValidityChecker, String typeName, Object TypeDef) throws Cvc3Exception;
    private static native Object
	jniLookupType(Object ValidityChecker, String typeName) throws Cvc3Exception;

    
    private static native Object
	jniGetExprManager(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniNullExpr(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniVarExpr1(Object ValidityChecker, String name, Object Type) throws Cvc3Exception;
    private static native Object
	jniVarExpr2(Object ValidityChecker, String name, Object Type, Object defExpr) throws Cvc3Exception;
    private static native Object
	jniBoundVarExpr(Object ValidityChecker, String name, String uid, Object Type) throws Cvc3Exception;
    /*private static native Object
    jniBoundVarExpr2(Object ValidityChecker, Object Type) throws Cvc3Exception;
    */
    private static native Object
	jniLookupVar(Object ValidityChecker, String name) throws Cvc3Exception;
    private static native Object
	jniLookupOp(Object ValidityChecker, String name) throws Cvc3Exception;
    private static native Object
	jniGetType(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetBaseType1(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetBaseType2(Object ValidityChecker, Object Type) throws Cvc3Exception;
    private static native Object
	jniGetTypePred(Object ValidityChecker, Object Type, Object Expr) throws Cvc3Exception;
    private static native Object
	jniStringExpr(Object ValidityChecker, String str) throws Cvc3Exception;
    private static native Object
	jniIdExpr(Object ValidityChecker, String name) throws Cvc3Exception;
    private static native Object
	jniListExpr1(Object ValidityChecker, Object[] kids) throws Cvc3Exception;
    private static native Object
	jniListExpr2(Object ValidityChecker, Object Expr1) throws Cvc3Exception;
    private static native Object
	jniListExpr3(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniListExpr4(Object ValidityChecker, Object Expr1, Object Expr2, Object Expr3) throws Cvc3Exception;
    private static native Object
	jniListExpr5(Object ValidityChecker, String op, Object[] kids) throws Cvc3Exception;
    private static native Object
	jniListExpr6(Object ValidityChecker, String op, Object Expr1) throws Cvc3Exception;
    private static native Object
	jniListExpr7(Object ValidityChecker, String op, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniListExpr8(Object ValidityChecker, String op, Object Expr1, Object Expr2, Object Expr3) throws Cvc3Exception;
    private static native void
    jniPrintExpr(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniParseExpr(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniParseType(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniImportExpr(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniImportType(Object ValidityChecker, Object Type) throws Cvc3Exception;
    private static native void
    jniCmdsFromString(Object ValidityChecker, String s) throws Cvc3Exception;
    private static native Object
    jniExprFromString(Object ValidityChecker, String s) throws Cvc3Exception;
    private static native Object
	jniTrueExpr(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniFalseExpr(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniNotExpr(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniAndExpr1(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniAndExpr2(Object ValidityChecker, Object[] ExprChildren) throws Cvc3Exception;
    private static native Object
	jniOrExpr1(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniOrExpr2(Object ValidityChecker, Object[] Exprchildren) throws Cvc3Exception;
    private static native Object
	jniImpliesExpr(Object ValidityChecker, Object ExprHyp, Object ExprConc) throws Cvc3Exception;
    private static native Object
	jniIffExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniEqExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
    jniDistinctExpr(Object ValidityChecker, Object[] ExprChildren) throws Cvc3Exception;
	private static native Object
	jniIteExpr(Object ValidityChecker, Object ExprIf, Object ExprThen, Object ExprElse) throws Cvc3Exception;
    private static native Object
	jniCreateOp1(Object ValidityChecker, String name, Object Type) throws Cvc3Exception;
    private static native Object
	jniCreateOp2(Object ValidityChecker, String name, Object Type, Object ExprDef) throws Cvc3Exception;
    private static native Object
	jniEqOp() throws Cvc3Exception;
    private static native Object
	jniLtOp() throws Cvc3Exception;
    private static native Object
	jniLeOp() throws Cvc3Exception;
    private static native Object
	jniGtOp() throws Cvc3Exception;
    private static native Object
	jniGeOp() throws Cvc3Exception;
    private static native Object
	jniPlusOp() throws Cvc3Exception;
    private static native Object
	jniMinusOp() throws Cvc3Exception;
    private static native Object
	jniMultOp() throws Cvc3Exception;
    private static native Object
	jniDivideOp() throws Cvc3Exception;
    private static native Object
	jniFunExpr1(Object ValidityChecker, Object Op, Object Expr) throws Cvc3Exception;
    private static native Object
	jniFunExpr2(Object ValidityChecker, Object Op, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniFunExpr3(Object ValidityChecker, Object Op, Object Expr1, Object Expr2, Object Expr3) throws Cvc3Exception;
    private static native Object
	jniFunExpr4(Object ValidityChecker, Object Op, Object[] ExprChildren) throws Cvc3Exception;
    private static native Object
	jniRatExpr1(Object ValidityChecker, int n, int d) throws Cvc3Exception;
    private static native Object
	jniRatExpr2(Object ValidityChecker, String n, String d, int base) throws Cvc3Exception;
    private static native Object
	jniRatExpr3(Object ValidityChecker, String n, int base) throws Cvc3Exception;
    private static native Object
	jniUminusExpr(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniPlusExpr1(Object ValidityChecker, Object Exprleft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniPlusExpr2(Object ValidityChecker, Object[] kids) throws Cvc3Exception;
    private static native Object
	jniMinusExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniMultExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniPowExpr(Object ValidityChecker, Object ExprX, Object ExprN) throws Cvc3Exception;
    private static native Object
	jniDivideExpr(Object ValidityChecker, Object ExprNumerator, Object ExprDenominator) throws Cvc3Exception;
    private static native Object
	jniLtExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniLeExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniGtExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniGeExpr(Object ValidityChecker, Object ExprLeft, Object ExprRight) throws Cvc3Exception;
    private static native Object
	jniRecordExpr1(Object ValidityChecker, String field, Object Expr) throws Cvc3Exception;
    private static native Object
	jniRecordExpr2(Object ValidityChecker, String field1, Object Expr1,
		   String field2, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniRecordExpr3(Object ValidityChecker, String field1, Object Expr1, String field2, Object Expr2,
		   String field3, Object Expr3) throws Cvc3Exception;
    private static native Object
	jniRecordExpr4(Object ValidityChecker, Object[] StringFields, Object[] Exprs) throws Cvc3Exception;
    private static native Object
	jniRecSelectExpr(Object ValidityChecker, Object ExprRecord, String field) throws Cvc3Exception;
    private static native Object
	jniRecUpdateExpr(Object ValidityChecker, Object ExprRecord, String field,
		      Object ExprNewValue) throws Cvc3Exception;
    private static native Object
	jniReadExpr(Object ValidityChecker, Object ExprArray, Object ExprIndex) throws Cvc3Exception;
    private static native Object
	jniWriteExpr(Object ValidityChecker, Object ExprArray, Object ExprIndex,
		  Object ExprNewValue) throws Cvc3Exception;
    private static native Object
	jniNewBVConstExpr1(Object ValidityChecker, String s, int base) throws Cvc3Exception;
    private static native Object
	jniNewBVConstExpr2(Object ValidityChecker, boolean[] bits) throws Cvc3Exception;
    private static native Object
	jniNewBVConstExpr3(Object ValidityChecker, Object RationalR, int len) throws Cvc3Exception;
    private static native Object
	jniNewConcatExpr1(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewConcatExpr2(Object ValidityChecker, Object[] Exprkids) throws Cvc3Exception;
    private static native Object
	jniNewBVExtractExpr(Object ValidityChecker, Object ExprE, int hi, int low) throws Cvc3Exception;
    private static native Object
	jniNewBVNegExpr(Object ValidityChecker, Object Expr1) throws Cvc3Exception;
    private static native Object
	jniNewBVAndExpr1(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVAndExpr2(Object ValidityChecker, Object[] ExprKids) throws Cvc3Exception;
    private static native Object
	jniNewBVOrExpr1(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVOrExpr2(Object ValidityChecker, Object[] ExprKids) throws Cvc3Exception;
    private static native Object
	jniNewBVXorExpr1(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVXorExpr2(Object ValidityChecker, Object[] ExprKids) throws Cvc3Exception;
    private static native Object
	jniNewBVXnorExpr1(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVXnorExpr2(Object ValidityChecker, Object[] ExprKids) throws Cvc3Exception;
    private static native Object
	jniNewBVNandExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVNorExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVLTExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVLEExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVSLTExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVSLEExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewSXExpr(Object ValidityChecker, Object Expr1, int len) throws Cvc3Exception;
    private static native Object
	jniNewBVUminusExpr(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniNewBVSubExpr(Object ValidityChecker, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
	jniNewBVPlusExpr(Object ValidityChecker, int numbits, Object[] ExprK) throws Cvc3Exception;
    private static native Object
	jniNewBVMultExpr(Object ValidityChecker, int numbits, Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native Object
    jniNewBVUDivExpr(Object ValidityChecker, Object left, Object right) throws Cvc3Exception;
    private static native Object
    jniNewBVURemExpr(Object ValidityChecker, Object left, Object right) throws Cvc3Exception;
    private static native Object
    jniNewBVSDivExpr(Object ValidityChecker, Object left, Object right) throws Cvc3Exception;
    private static native Object
    jniNewBVSRemExpr(Object ValidityChecker, Object left, Object right) throws Cvc3Exception;
    private static native Object
    jniNewBVSModExpr(Object ValidityChecker, Object left, Object right)	throws Cvc3Exception;
    private static native Object
    jniNewBVSHL(Object ValidityChecker, Object left, Object right)	throws Cvc3Exception;
    private static native Object
    jniNewBVLSHR(Object ValidityChecker, Object left, Object right)	throws Cvc3Exception;
    private static native Object
    jniNewBVASHR(Object ValidityChecker, Object left, Object right)	throws Cvc3Exception;
    private static native Object
	jniNewFixedLeftShiftExpr(Object ValidityChecker, Object Expr1, int r) throws Cvc3Exception;
    private static native Object
	jniNewFixedConstWidthLeftShiftExpr(Object ValidityChecker, Object Expr1, int r) throws Cvc3Exception;
    private static native Object
	jniNewFixedRightShiftExpr(Object ValidityChecker, Object Expr1, int r) throws Cvc3Exception;
    private static native Object
        jniComputeBVConst(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniTupleExpr(Object ValidityChecker, Object[] Exprs) throws Cvc3Exception;
    private static native Object
	jniTupleSelectExpr(Object ValidityChecker, Object ExprTuple, int index) throws Cvc3Exception;
    private static native Object
	jniTupleUpdateExpr(Object ValidityChecker, Object ExprTuple, int index,
			   Object ExprNewValue) throws Cvc3Exception;
    private static native Object
	jniDatatypeConsExpr(Object ValidityChecker, String constructor, Object[] ExprArgs) throws Cvc3Exception;
    private static native Object
	jniDatatypeSelExpr(Object ValidityChecker, String selector, Object ExprArg) throws Cvc3Exception;
    private static native Object
	jniDatatypeTestExpr(Object ValidityChecker, String constructor, Object ExprArg) throws Cvc3Exception;
    private static native Object
	jniForallExpr1(Object ValidityChecker, Object[] ExprVars, Object ExprBody) throws Cvc3Exception;
    private static native Object
	jniForallExpr2(Object ValidityChecker, Object[] ExprVars, Object ExprBody,
		      Object ExprTrigger) throws Cvc3Exception;
    private static native Object
    jniForallExpr3(Object ValidityChecker, Object[] ExprVars, Object ExprBody,
              Object[] ExprTriggers) throws Cvc3Exception;
    private static native Object
	jniForallExpr4(Object ValidityChecker, Object[] ExprVars, Object ExprBody,
		      Object[][] ExprTriggers) throws Cvc3Exception;
    private static native void
	jniSetTrigger(Object ValidityChecker, Object ExprClosure, Object ExprTrigger) throws Cvc3Exception;
    private static native void
	jniSetTriggers(Object ValidityChecker, Object ExprClosure, Object[] ExprTriggers) throws Cvc3Exception;
    private static native void
    jniSetTriggers2(Object ValidityChecker, Object ExprClosure, Object[][] ExprTriggers) throws Cvc3Exception;
    private static native void
    jniSetMultiTrigger(Object ValidityChecker, Object ExprClosure, Object[] ExprMultiTrigger) throws Cvc3Exception;
    private static native Object
	jniExistsExpr(Object ValidityChecker, Object[] ExprVars, Object ExprBody) throws Cvc3Exception;
    private static native Object
	jniLambdaExpr(Object ValidityChecker, Object[] ExprVars, Object ExprBody) throws Cvc3Exception;
    private static native Object
	jniTransClosure(Object ValidityChecker, Object Op) throws Cvc3Exception;
    private static native Object
	jniSimulateExpr(Object ValidityChecker, Object ExprF, Object ExprS,
		     Object[] ExprInputs, Object ExprN) throws Cvc3Exception;

    private static native void
    jniSetResourceLimit(Object ValidityChecker, int limit) throws Cvc3Exception;
    private static native void
	jniAssertFormula(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native void
	jniRegisterAtom(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native Object
	jniGetImpliedLiteral(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniSimplify(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native String
	jniQuery(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native String
	jniCheckUnsat(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native String
	jniCheckContinue(Object ValidityChecker) throws Cvc3Exception;
    private static native String
	jniRestart(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native void
	jniReturnFromCheck(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniGetUserAssumptions(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniGetInternalAssumptions(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniGetAssumptions(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniGetAssumptionsUsed(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniGetCounterExample(Object ValidityChecker, boolean inOrder) throws Cvc3Exception;
    private static native Object[]
	jniGetConcreteModel(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniGetValue(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native String
	jniValue(Object ValidityChecker, Object Expr) throws Cvc3Exception;
    private static native boolean
	jniInconsistent1(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniInconsistent2(Object ValidityChecker) throws Cvc3Exception;
    private static native boolean
	jniIncomplete1(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniIncomplete2(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniGetProof(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniGetTCC(Object ValidityChecker) throws Cvc3Exception;
    private static native Object[]
	jniGetAssumptionsTCC(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniGetProofTCC(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniGetClosure(Object ValidityChecker) throws Cvc3Exception;
    private static native Object
	jniGetProofClosure(Object ValidityChecker) throws Cvc3Exception;
    
    private static native int
	jniStackLevel(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPush(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPop(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPopTo(Object ValidityChecker, int stackLevel) throws Cvc3Exception;
    private static native int
	jniScopeLevel(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPushScope(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPopScope(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPopToScope(Object ValidityChecker, int scopeLevel) throws Cvc3Exception;
    private static native Object
	jniGetCurrentContext(Object ValidityChecker) throws Cvc3Exception;

    private static native void
	jniLoadFile1(Object ValidityChecker, String fileName, String lang) throws Cvc3Exception;

    private static native Object
	jniGetStatistics(Object ValidityChecker) throws Cvc3Exception;
    private static native void
	jniPrintStatistics(Object ValidityChecker) throws Cvc3Exception;

    private static native void
	jniSetTimeLimit(Object ValidityChecker, int limit) throws Cvc3Exception;



    // delete ValidityChecker, all expressions created using it,
    // and all embedded objects registered with its embeddedManager
    public synchronized void delete() throws Cvc3Exception {
	if (isDeleted()) return;

	//:TEST:
	embeddedManager().cleanUp();

	embeddedManager().delete();
	EmbeddedManager.jniDelete(embedded());
	d_embedded = null;
    }

    // ensure that all embedded objects are deallocated eventually
    public void finalize() throws Throwable {
	try {
	    if (!isDeleted()) {
		assert(false);
//		System.out.println("ValidityChecker.Finalizer: should never be called");
		throw new Error("ValidityChecker.Finalizer: should never be called");
	    }
	} finally {
	    super.finalize();
	}
    }

    /// Constructor

    // create embedded object
    protected ValidityChecker(Object ValidityChecker) {
	super(ValidityChecker, new EmbeddedManager());
    }


    /// API: ValidityChecker


    // Creation

    // delete must be called before ValidityChecker is garbage collected
    public static ValidityChecker create() throws Cvc3Exception {
	return new ValidityChecker(jniCreate1());
    }

    // delete must be called before ValidityChecker is garbage collected
    public static ValidityChecker create(Flags flags) throws Cvc3Exception {
	return new ValidityChecker(jniCreate2(flags.embedded()));
    }


    // Flags

    // if embeddedManger is null then delete must be called before
    // the returned Flags is garbage collected
    public static FlagsMut createFlags(EmbeddedManager embeddedManager) throws Cvc3Exception {
	return new FlagsMut(jniCreateFlags(), embeddedManager);
    }

    public FlagsMut getFlags() throws Cvc3Exception {
	return new FlagsMut(jniGetFlags(embedded()), embeddedManager());
    }



    // Type-related methods

    public TypeMut boolType() throws Cvc3Exception {
	return new TypeMut(jniBoolType(embedded()), embeddedManager());
    }
    
    public TypeMut realType() throws Cvc3Exception {
	return new TypeMut(jniRealType(embedded()), embeddedManager());
    }

    public TypeMut intType() throws Cvc3Exception {
	return new TypeMut(jniIntType(embedded()), embeddedManager());
    }

    public TypeMut subrangeType(Expr l, Expr r) throws Cvc3Exception {
	return new TypeMut(
	  jniSubrangeType(embedded(), l.embedded(), r.embedded()),
	  embeddedManager());
    }

    public TypeMut subtypeType(Expr pred, Expr witness) throws Cvc3Exception {
	return new TypeMut(
	  jniSubtypeType(embedded(), pred.embedded(), witness.embedded()),
	  embeddedManager());
    }

    public TypeMut tupleType(Type type0, Type type1) throws Cvc3Exception {
	return new TypeMut(
	  jniTupleType1(embedded(), type0.embedded(), type1.embedded()),
	  embeddedManager());
    }

    public TypeMut tupleType(Type type0, Type type1, Type type2) throws Cvc3Exception {
	return new TypeMut(
	  jniTupleType2(embedded(), type0.embedded(), type1.embedded(), type2.embedded()),
	  embeddedManager());
    }

    public TypeMut tupleType(List types) throws Cvc3Exception {
	return new TypeMut(
	  jniTupleType3(embedded(), JniUtils.unembedList(types)),
	  embeddedManager());
    }

    public TypeMut recordType(String field, Type type) throws Cvc3Exception {
	return new TypeMut(
	  jniRecordType1(embedded(), field, type.embedded()),
	  embeddedManager());
    }

    public TypeMut recordType(String field0, Type type0, String field1, Type type1) throws Cvc3Exception {
	return new TypeMut(
	  jniRecordType2(embedded(), field0, type0.embedded(), field1, type1.embedded()),
	  embeddedManager());
    }

    public TypeMut recordType(String field0, Type type0, String field1, Type type1,
			    String field2, Type type2) throws Cvc3Exception {
	return new TypeMut(
	  jniRecordType3(embedded(), field0, type0.embedded(), field1, type1.embedded(),
			 field2, type2.embedded()),
	  embeddedManager());
    }

    public TypeMut recordType(List fields, List types) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(fields, String.class));
	return new TypeMut(
	  jniRecordType4(embedded(), JniUtils.toArray(fields), JniUtils.unembedList(types)),
	  embeddedManager());
    }
   
    public TypeMut dataType(String name, String constructor,
			  List selectors, List types) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(selectors, String.class));
	assert(JniUtils.listInstanceof(types, Expr.class));
	return new TypeMut(
	  jniDataType1(embedded(), name, constructor,
		       JniUtils.toArray(selectors), JniUtils.unembedList(types)),
	  embeddedManager());
    }

    public TypeMut dataType(String name, String[] constructors,
			  String[][] selectors, Expr[][] types) throws Cvc3Exception {
	return new TypeMut(
          jniDataType2(embedded(), name, constructors, selectors, JniUtils.unembedArrayArray(types)),
	  embeddedManager());
    }

    public TypeMut dataType(String name, List constructors,
			  List selectors, List types) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(constructors, String.class));
	assert(JniUtils.listListInstanceof(selectors, String.class));
	assert(JniUtils.listListInstanceof(types, Expr.class));
	return new TypeMut(
	  jniDataType2(embedded(), name, JniUtils.toArray(constructors),
		       JniUtils.toArrayArray(selectors), JniUtils.unembedListList(types)),
	  embeddedManager());
    }

    public List dataType(List names, List constructors,
			  List selectors, List types) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(names, String.class));
	assert(JniUtils.listListInstanceof(constructors, String.class));
	assert(JniUtils.listListListInstanceof(selectors, String.class));
	assert(JniUtils.listListListInstanceof(types, Expr.class));
	Object[] dataTypes =
	  jniDataType3(embedded(), JniUtils.toArray(names), JniUtils.toArrayArray(constructors),
		       JniUtils.toArrayArrayArray(selectors), JniUtils.unembedListListList(types));
	return JniUtils.embedList(dataTypes, TypeMut.class, embeddedManager());
    }

    public ExprMut arrayLiteral(Expr var, Expr body) throws Cvc3Exception {
      return new ExprMut(jniArrayLiteral(embedded(), var.embedded(), body.embedded()),embeddedManager());
    }

  public TypeMut anyType() throws Cvc3Exception {
    return new TypeMut(jniAnyType(embedded()),embeddedManager());
  }
    
    public TypeMut arrayType(Type typeIndex, Type typeData) throws Cvc3Exception {
	return new TypeMut(
	  jniArrayType(embedded(), typeIndex.embedded(), typeData.embedded()),
	  embeddedManager());
    }

    public TypeMut bitvecType(int n) throws Cvc3Exception {
	return new TypeMut(
	  jniBitvecType(embedded(), n),
	  embeddedManager());
    }

    public TypeMut funType(Type typeDom, Type typeRange) throws Cvc3Exception {
	return new TypeMut(
	  jniFunType1(embedded(), typeDom.embedded(), typeRange.embedded()),
	  embeddedManager());
    }

    public TypeMut funType(List typeDom, Type typeRange) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(typeDom, Type.class));
	return new TypeMut(
          jniFunType2(embedded(), JniUtils.unembedList(typeDom), typeRange.embedded()),
	  embeddedManager());
    }

    public TypeMut createType(String typeName) throws Cvc3Exception {
	return new TypeMut(
	  jniCreateType1(embedded(), typeName),
	  embeddedManager());
    }

    public TypeMut createType(String typeName, Type typeDef) throws Cvc3Exception {
	return new TypeMut(
          jniCreateType2(embedded(), typeName, typeDef.embedded()),
	  embeddedManager());
    }

    public TypeMut lookupType(String typeName) throws Cvc3Exception {
	return new TypeMut(
	  jniLookupType(embedded(), typeName),
	  embeddedManager());
    }



    // Expressions

    public ExprManagerMut getExprManager() throws Cvc3Exception {
	return new ExprManagerMut(jniGetExprManager(embedded()), embeddedManager());
    }

    public Expr nullExpr() throws Cvc3Exception {
	return new Expr(jniNullExpr(embedded()), embeddedManager());
    }

    public ExprMut varExpr(String name, Type type) throws Cvc3Exception {
	return new ExprMut(
	  jniVarExpr1(embedded(), name, type.embedded()),
	  embeddedManager());
    }

    public ExprMut varExpr(String name, Type type, Expr def) throws Cvc3Exception {
	return new ExprMut(
	  jniVarExpr2(embedded(), name, type.embedded(), def.embedded()),
	  embeddedManager());
    }

    public ExprMut boundVarExpr(String name, String uid, Type type) throws Cvc3Exception {
	return new ExprMut(
	  jniBoundVarExpr(embedded(), name, uid, type.embedded()),
	  embeddedManager());
    }
    
/*    public ExprMut boundVarExpr(Type type) throws Cvc3Exception {
      return new ExprMut(
        jniBoundVarExpr(embedded(), type.embedded()),
        embeddedManager());
      }*/

    public ExprMut lookupVar(String name) throws Cvc3Exception {
	return new ExprMut(
	  jniLookupVar(embedded(), name),
	  embeddedManager());
    }

    public OpMut lookupOp(String name) throws Cvc3Exception {
	return new OpMut(
	  jniLookupOp(embedded(), name),
	  embeddedManager());
    }

    public TypeMut getType(Expr expr) throws Cvc3Exception {
	return new TypeMut(
	  jniGetType(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public TypeMut getBaseType(Expr expr) throws Cvc3Exception {
	return new TypeMut(
	  jniGetBaseType1(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public TypeMut getBaseType(Type type) throws Cvc3Exception {
	return new TypeMut(
	  jniGetBaseType2(embedded(), type.embedded()),
	  embeddedManager());
    }

    public ExprMut getTypePred(Type type, Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniGetTypePred(embedded(), type.embedded(), expr.embedded()),
	  embeddedManager());
    }

    public ExprMut stringExpr(String str) throws Cvc3Exception {
	return new ExprMut(
	  jniStringExpr(embedded(), str),
	  embeddedManager());
    }

    public ExprMut idExpr(String name) throws Cvc3Exception {
	return new ExprMut(
	  jniIdExpr(embedded(), name),
	  embeddedManager());
    }

    public ExprMut listExpr(List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniListExpr1(embedded(), JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut listExpr(Expr expr1) throws Cvc3Exception {
	return new ExprMut(
	  jniListExpr2(embedded(), expr1.embedded()),
	  embeddedManager());
    }

    public ExprMut listExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniListExpr3(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut listExpr(Expr expr1, Expr expr2, Expr expr3) throws Cvc3Exception {
	return new ExprMut(
	  jniListExpr4(embedded(), expr1.embedded(), expr2.embedded(), expr3.embedded()),
	  embeddedManager());
    }

    public ExprMut listExpr(String op, List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniListExpr5(embedded(), op, JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut listExpr(String op, Expr expr1) throws Cvc3Exception {
	return new ExprMut(
	  jniListExpr6(embedded(), op, expr1.embedded()),
	  embeddedManager());
    }

    public ExprMut listExpr(String op, Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniListExpr7(embedded(), op, expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut listExpr(String op, Expr expr1, Expr expr2, Expr expr3) throws Cvc3Exception {
	return new ExprMut(
	  jniListExpr8(embedded(), op, expr1.embedded(), expr2.embedded(), expr3.embedded()),
	  embeddedManager());
    }

    public void printExpr(Expr expr) throws Cvc3Exception {
      jniPrintExpr(embedded(), expr.embedded());
    }
    
    public ExprMut parseExpr(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniParseExpr(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public TypeMut parseType(Expr expr) throws Cvc3Exception {
	return new TypeMut(
	  jniParseType(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public ExprMut importExpr(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniImportExpr(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public TypeMut importType(Type type) throws Cvc3Exception {
	return new TypeMut(
	  jniImportType(embedded(), type.embedded()),
	  embeddedManager());
    }

    public void cmdsFromString(String s) throws Cvc3Exception {
      jniCmdsFromString(embedded(), s);
    }

    public ExprMut exprFromString(String s) throws Cvc3Exception {
      return new ExprMut( jniExprFromString(embedded(), s), embeddedManager() );
    }
    
    
    public ExprMut trueExpr() throws Cvc3Exception {
	return new ExprMut(jniTrueExpr(embedded()), embeddedManager());
    }

    public ExprMut falseExpr() throws Cvc3Exception {
	return new ExprMut(jniFalseExpr(embedded()), embeddedManager());
    }

    public ExprMut notExpr(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniNotExpr(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public ExprMut andExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniAndExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut andExpr(List children) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(children, Expr.class));
	return new ExprMut(
	  jniAndExpr2(embedded(), JniUtils.unembedList(children)),
	  embeddedManager());
    }

    public ExprMut orExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniOrExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut orExpr(List children) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(children, Expr.class));
	return new ExprMut(
	  jniOrExpr2(embedded(), JniUtils.unembedList(children)),
	  embeddedManager());
    }

    public ExprMut impliesExpr(Expr hyp, Expr conc) throws Cvc3Exception {
	return new ExprMut(
	  jniImpliesExpr(embedded(), hyp.embedded(), conc.embedded()),
	  embeddedManager());
    }

    public ExprMut iffExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniIffExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut eqExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniEqExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut distinctExpr(List children) throws Cvc3Exception {
    assert(JniUtils.listInstanceof(children, Expr.class));
    return new ExprMut(
    	jniDistinctExpr(embedded(), JniUtils.unembedList(children)), embeddedManager());
    }    
    
    public ExprMut iteExpr(Expr ifPart, Expr thenPart, Expr elsePart) throws Cvc3Exception {
	return new ExprMut(
	  jniIteExpr(embedded(), ifPart.embedded(), thenPart.embedded(), elsePart.embedded()),
	  embeddedManager());
    }

    public OpMut createOp(String name, Type type) throws Cvc3Exception {
	return new OpMut(
	  jniCreateOp1(embedded(), name, type.embedded()),
	  embeddedManager());
    }

    public OpMut createOp(String name, Type type, Expr expr) throws Cvc3Exception {
	return new OpMut(
	  jniCreateOp2(embedded(), name, type.embedded(), expr.embedded()),
	  embeddedManager());
    }

    // '='
    public OpMut eqOp() throws Cvc3Exception {
	return new OpMut(jniEqOp(), embeddedManager());
    }

    // '<'
    public OpMut ltOp() throws Cvc3Exception {
	return new OpMut(jniLtOp(), embeddedManager());
    }

    // '<='
    public OpMut leOp() throws Cvc3Exception {
	return new OpMut(jniLeOp(), embeddedManager());
    }

    // '>'
    public OpMut gtOp() throws Cvc3Exception {
	return new OpMut(jniGtOp(), embeddedManager());
    }

    // '>='
    public OpMut geOp() throws Cvc3Exception {
	return new OpMut(jniGeOp(), embeddedManager());
    }

    // '+'
    public OpMut plusOp() throws Cvc3Exception {
	return new OpMut(jniPlusOp(), embeddedManager());
    }

    // '-'
    public OpMut minusOp() throws Cvc3Exception {
	return new OpMut(jniMinusOp(), embeddedManager());
    }

    // '*'
    public OpMut multOp() throws Cvc3Exception {
	return new OpMut(jniMultOp(), embeddedManager());
    }

    // '/' for rationals
    public OpMut divideOp() throws Cvc3Exception {
	return new OpMut(jniDivideOp(), embeddedManager());
    }

    public ExprMut funExpr(Op op, Expr expr1) throws Cvc3Exception {
	return new ExprMut(
	  jniFunExpr1(embedded(), op.embedded(), expr1.embedded()),
	  embeddedManager());
    }

    public ExprMut funExpr(Op op, Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniFunExpr2(embedded(), op.embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut funExpr(Op op, Expr expr1, Expr expr2, Expr expr3) throws Cvc3Exception {
	return new ExprMut(
	  jniFunExpr3(embedded(), op.embedded(), expr1.embedded(), expr2.embedded(), expr3.embedded()),
	  embeddedManager());
    }

    public ExprMut funExpr(Op op, List children) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(children, Expr.class));
	return new ExprMut(
	  jniFunExpr4(embedded(), op.embedded(), JniUtils.unembedList(children)),
	  embeddedManager());
    }

    public ExprMut ratExpr(int n) throws Cvc3Exception {
	return ratExpr(n, 1);
    }

    public ExprMut ratExpr(int n, int d) throws Cvc3Exception {
	return new ExprMut(
	  jniRatExpr1(embedded(), n, d),
	  embeddedManager());
    }

    public ExprMut ratExpr(String n, String d, int base) throws Cvc3Exception {
	return new ExprMut(
	  jniRatExpr2(embedded(), n, d, base),
	  embeddedManager());
    }

    public ExprMut ratExpr(String n) throws Cvc3Exception {
	return ratExpr(n, 10);
    }

    public ExprMut ratExpr(String n, int base) throws Cvc3Exception {
	return new ExprMut(
	  jniRatExpr3(embedded(), n, base),
	  embeddedManager());
    }

    public ExprMut uminusExpr(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniUminusExpr(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public ExprMut plusExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniPlusExpr1(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }
    
    public ExprMut plusExpr(List kids) throws Cvc3Exception {
    return new ExprMut(
      jniPlusExpr2(embedded(), JniUtils.unembedList(kids)),
      embeddedManager());
    }

    public ExprMut minusExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniMinusExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut multExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniMultExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut powExpr(Expr x, Expr n) throws Cvc3Exception {
	return new ExprMut(
	  jniPowExpr(embedded(), x.embedded(), n.embedded()),
	  embeddedManager());
    }

    public ExprMut divideExpr(Expr numerator, Expr denominator) throws Cvc3Exception {
	return new ExprMut(
	  jniDivideExpr(embedded(), numerator.embedded(), denominator.embedded()),
	  embeddedManager());
    }

    public ExprMut ltExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniLtExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut leExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniLeExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut gtExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniGtExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut geExpr(Expr left, Expr right) throws Cvc3Exception {
	return new ExprMut(
	  jniGeExpr(embedded(), left.embedded(), right.embedded()),
	  embeddedManager());
    }

    public ExprMut recordExpr(String field, Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniRecordExpr1(embedded(), field, expr.embedded()),
	  embeddedManager());
    }

    public ExprMut recordExpr(String field1, Expr expr1, String field2, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniRecordExpr2(embedded(), field1, expr1.embedded(), field2, expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut recordExpr(String field1, Expr expr1, String field2, Expr expr2,
			      String field3, Expr expr3) throws Cvc3Exception {
	return new ExprMut(
	  jniRecordExpr3(embedded(), field1, expr1.embedded(), field2, expr2.embedded(),
			 field3, expr3.embedded()),
	  embeddedManager());
    }

    public ExprMut recordExpr(List fields, List exprs) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(fields, String.class));
	assert(JniUtils.listInstanceof(exprs, Expr.class));
	return new ExprMut(
	  jniRecordExpr4(embedded(), JniUtils.toArray(fields), JniUtils.unembedList(exprs)),
	  embeddedManager());
    }

    public ExprMut recSelectExpr(Expr record, String field) throws Cvc3Exception {
	return new ExprMut(
	  jniRecSelectExpr(embedded(), record.embedded(), field),
	  embeddedManager());
    }

    public ExprMut recUpdateExpr(Expr record, String field, Expr newValue) throws Cvc3Exception {
	return new ExprMut(
	  jniRecUpdateExpr(embedded(), record.embedded(), field, newValue.embedded()),
	  embeddedManager());
    }

    public ExprMut readExpr(Expr array, Expr index) throws Cvc3Exception {
	return new ExprMut(
	  jniReadExpr(embedded(), array.embedded(), index.embedded()),
	  embeddedManager());
    }

    public ExprMut writeExpr(Expr array, Expr index, Expr newValue) throws Cvc3Exception {
	return new ExprMut(
	  jniWriteExpr(embedded(), array.embedded(), index.embedded(), newValue.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVConstExpr(String s) throws Cvc3Exception {
	return newBVConstExpr(s, 2);
    }

    public ExprMut newBVConstExpr(String s, int base) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVConstExpr1(embedded(), s, base),
	  embeddedManager());
    }

    public ExprMut newBVConstExpr(boolean[] bits) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVConstExpr2(embedded(), bits),
	  embeddedManager());
    }

    public ExprMut newBVConstExpr(Rational r, int len) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVConstExpr3(embedded(), r.embedded(), len),
	  embeddedManager());
    }

    public ExprMut newConcatExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewConcatExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newConcatExpr(List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniNewConcatExpr2(embedded(), JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut newBVExtractExpr(Expr e, int hi, int low) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVExtractExpr(embedded(), e.embedded(), hi, low),
	  embeddedManager());
    }

    public ExprMut newBVNegExpr(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVNegExpr(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVAndExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVAndExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVAndExpr(List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniNewBVAndExpr2(embedded(), JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut newBVOrExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVOrExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVOrExpr(List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniNewBVOrExpr2(embedded(), JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut newBVXorExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVXorExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVXorExpr(List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniNewBVXorExpr2(embedded(), JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut newBVXnorExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVXnorExpr1(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVXnorExpr(List kids) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(kids, Expr.class));
	return new ExprMut(
	  jniNewBVXnorExpr2(embedded(), JniUtils.unembedList(kids)),
	  embeddedManager());
    }

    public ExprMut newBVNandExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVNandExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVNorExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVNorExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVLTExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVLTExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVLEExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVLEExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVSLTExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVSLTExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVSLEExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVSLEExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newSXExpr(Expr expr, int len) throws Cvc3Exception {
	return new ExprMut(
	  jniNewSXExpr(embedded(), expr.embedded(), len),
	  embeddedManager());
    }

    public ExprMut newBVUminusExpr(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVUminusExpr(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVSubExpr(Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVSubExpr(embedded(), expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }

    public ExprMut newBVPlusExpr(int numbits, List exprs) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(exprs, Expr.class));
	return new ExprMut(
	  jniNewBVPlusExpr(embedded(), numbits, JniUtils.unembedList(exprs)),
	  embeddedManager());
    }

    public ExprMut newBVMultExpr(int numbits, Expr expr1, Expr expr2) throws Cvc3Exception {
	return new ExprMut(
	  jniNewBVMultExpr(embedded(), numbits, expr1.embedded(), expr2.embedded()),
	  embeddedManager());
    }
       
    public ExprMut newBVUDivExpr(Expr left, Expr right) throws Cvc3Exception {
   	return new ExprMut(
   	  jniNewBVUDivExpr(embedded(), left.embedded(), right.embedded()),
   	  embeddedManager());
    }
        
    public ExprMut newBVURemExpr(Expr left, Expr right) throws Cvc3Exception {
   	return new ExprMut(
  	  jniNewBVURemExpr(embedded(), left.embedded(), right.embedded()),
   	  embeddedManager());
    }

    public ExprMut newBVSDivExpr(Expr left, Expr right) throws Cvc3Exception {
  	return new ExprMut(
  	  jniNewBVSDivExpr(embedded(), left.embedded(), right.embedded()),
   	  embeddedManager());
    }

    public ExprMut newBVSRemExpr(Expr left, Expr right) throws Cvc3Exception {
    return new ExprMut(
  	  jniNewBVSRemExpr(embedded(), left.embedded(), right.embedded()),
   	  embeddedManager());
    }    
    
    public ExprMut newBVSModExpr(Expr left, Expr right) throws Cvc3Exception {
    return new ExprMut(
      jniNewBVSModExpr(embedded(), left.embedded(), right.embedded()),
      embeddedManager());
    }

    public ExprMut newBVSHL(Expr left, Expr right) throws Cvc3Exception {
    return new ExprMut(
      jniNewBVSHL(embedded(), left.embedded(), right.embedded()),
      embeddedManager());
    }

    public ExprMut newBVLSHR(Expr left, Expr right) throws Cvc3Exception {
    return new ExprMut(
      jniNewBVLSHR(embedded(), left.embedded(), right.embedded()),
      embeddedManager());
    }

    public ExprMut newBVASHR(Expr left, Expr right) throws Cvc3Exception {
    return new ExprMut(
      jniNewBVASHR(embedded(), left.embedded(), right.embedded()),
      embeddedManager());
    }

    public ExprMut newFixedLeftShiftExpr(Expr expr, int r) throws Cvc3Exception {
	return new ExprMut(
	  jniNewFixedLeftShiftExpr(embedded(), expr.embedded(), r),
	  embeddedManager());
    }

    public ExprMut newFixedConstWidthLeftShiftExpr(Expr expr, int r) throws Cvc3Exception {
	return new ExprMut(
	  jniNewFixedConstWidthLeftShiftExpr(embedded(), expr.embedded(), r),
	  embeddedManager());
    }

    public ExprMut newFixedRightShiftExpr(Expr expr, int r) throws Cvc3Exception {
	return new ExprMut(
	  jniNewFixedRightShiftExpr(embedded(), expr.embedded(), r),
	  embeddedManager());
    }

    public Rational computeBVConst(Expr expr) {
        Rational rat = new Rational(
            jniComputeBVConst(embedded(),expr.embedded()), 
            embeddedManager());
        assert( rat.isInteger() );
        return rat;
    }

    public ExprMut tupleExpr(List exprs) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(exprs, Expr.class));
	return new ExprMut(
	  jniTupleExpr(embedded(), JniUtils.unembedList(exprs)),
	  embeddedManager());
    }

    public ExprMut tupleSelectExpr(Expr tuple, int index) throws Cvc3Exception {
	return new ExprMut(
	  jniTupleSelectExpr(embedded(), tuple.embedded(), index),
	  embeddedManager());
    }

    public ExprMut tupleUpdateExpr(Expr tuple, int index, Expr newValue) throws Cvc3Exception {
	return new ExprMut(
	  jniTupleUpdateExpr(embedded(), tuple.embedded(), index, newValue.embedded()),
	  embeddedManager());
    }

    public ExprMut datatypeConsExpr(String constructor, List exprs) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(exprs, Expr.class));
	return new ExprMut(
	  jniDatatypeConsExpr(embedded(), constructor, JniUtils.unembedList(exprs)),
	  embeddedManager());
    }

    public ExprMut datatypeSelExpr(String selector, Expr arg) throws Cvc3Exception {
	return new ExprMut(
	  jniDatatypeSelExpr(embedded(), selector, arg.embedded()),
	  embeddedManager());
    }

    public ExprMut datatypeTestExpr(String constructor, Expr arg) throws Cvc3Exception {
	return new ExprMut(
	  jniDatatypeTestExpr(embedded(), constructor, arg.embedded()),
	  embeddedManager());
    }

    public ExprMut forallExpr(List vars, Expr body) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(vars, Expr.class));
	return new ExprMut(
	  jniForallExpr1(embedded(), JniUtils.unembedList(vars), body.embedded()),
	  embeddedManager());
    }

    public ExprMut forallExpr(List vars, Expr body, Expr trigger) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(vars, Expr.class));
	return new ExprMut(
	  jniForallExpr2(embedded(), JniUtils.unembedList(vars), body.embedded(),
                         trigger.embedded()),
	  embeddedManager());
    }

    public ExprMut forallExpr(List vars, Expr body, List triggers) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(vars, Expr.class));
	assert(JniUtils.listInstanceof(triggers, Expr.class));
	return new ExprMut(
	  jniForallExpr3(embedded(), JniUtils.unembedList(vars), body.embedded(),
			JniUtils.unembedList(triggers)),
	  embeddedManager());
    }

    public ExprMut forallExprMultiTriggers(List vars, Expr body, List multiTriggers)
      throws Cvc3Exception {
    assert (JniUtils.listInstanceof(vars, Expr.class));
    assert (JniUtils.listListInstanceof(multiTriggers, Expr.class));
    return new ExprMut(jniForallExpr4(embedded(), JniUtils.unembedList(vars),
        body.embedded(), JniUtils.unembedListList(multiTriggers)),
        embeddedManager());
    }

    public void setTrigger(Expr closure, Expr trigger) throws Cvc3Exception {
      jniSetTrigger(embedded(), closure.embedded(), trigger.embedded());
    }

    public void setTriggers(Expr closure, List triggers) throws Cvc3Exception {
      jniSetTriggers(embedded(), closure.embedded(), JniUtils.unembedList(triggers));
    }

    public void setMultiTrigger(Expr closure, List multiTrigger) throws Cvc3Exception {
      jniSetMultiTrigger(embedded(), closure.embedded(), JniUtils.unembedList(multiTrigger));
    }

    public void setMultiTriggers(Expr closure, List triggers) throws Cvc3Exception {
      jniSetTriggers2(embedded(), closure.embedded(), JniUtils.unembedListList(triggers));
    }

    public ExprMut existsExpr(List vars, Expr body) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(vars, Expr.class));
	return new ExprMut(
	  jniExistsExpr(embedded(), JniUtils.unembedList(vars), body.embedded()),
	  embeddedManager());
    }

    public OpMut lambdaExpr(List vars, Expr body) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(vars, Expr.class));
	return new OpMut(
	  jniLambdaExpr(embedded(), JniUtils.unembedList(vars), body.embedded()),
	  embeddedManager());
    }

    public OpMut transClosure(Op p) throws Cvc3Exception {
	return new OpMut(
	  jniTransClosure(embedded(), p.embedded()),
	  embeddedManager());
    }

    public ExprMut simulateExpr(Expr f, Expr s, List inputs, Expr n) throws Cvc3Exception {
	assert(JniUtils.listInstanceof(inputs, Expr.class));
	return new ExprMut(
	  jniSimulateExpr(embedded(), f.embedded(), s.embedded(), JniUtils.unembedList(inputs), n.embedded()),
	  embeddedManager());
    }


    public void setResourceLimit(int limit) throws Cvc3Exception {
      jniSetResourceLimit(embedded(), limit);
    }
    
    // Validity checking methods

    public void assertFormula(Expr expr) throws Cvc3Exception {
	embeddedManager().cleanUp();
	jniAssertFormula(embedded(), expr.embedded());
	embeddedManager().cleanUp();
    }

    public void registerAtom(Expr expr) throws Cvc3Exception {
	jniRegisterAtom(embedded(), expr.embedded());
    }

    public ExprMut getImpliedLiteral() throws Cvc3Exception {
	return new ExprMut(
	  jniGetImpliedLiteral(embedded()),
	  embeddedManager());
    }

    public ExprMut simplify(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniSimplify(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public QueryResult query(Expr expr) throws Cvc3Exception {
	embeddedManager().cleanUp();
	QueryResult result = QueryResult.get(jniQuery(embedded(), expr.embedded()));

	//:TEST:
	embeddedManager().cleanUp();
	return result;
    }

    public SatResult checkUnsat(Expr expr) throws Cvc3Exception {
	embeddedManager().cleanUp();
	SatResult result = SatResult.get(jniCheckUnsat(embedded(), expr.embedded()));

	//:TEST:
	embeddedManager().cleanUp();
	return result;
    }

    public QueryResult checkContinue() throws Cvc3Exception {
	embeddedManager().cleanUp();
	QueryResult result = QueryResult.get(jniCheckContinue(embedded()));

	//:TEST:
	embeddedManager().cleanUp();
	return result;
    }

    public QueryResult restart(Expr expr) throws Cvc3Exception {
	embeddedManager().cleanUp();
	QueryResult result = QueryResult.get(jniRestart(embedded(), expr.embedded()));

	//:TEST:
	embeddedManager().cleanUp();
	return result;
    }

    public void returnFromCheck() throws Cvc3Exception {
	jniReturnFromCheck(embedded());

	//:TEST:
	embeddedManager().cleanUp();
    }

    public List getUserAssumptions() throws Cvc3Exception {
	Object[] assumptions = jniGetUserAssumptions(embedded());
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public List getInternalAssumptions() throws Cvc3Exception {
	Object[] assumptions = jniGetInternalAssumptions(embedded());
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public List getAssumptions() throws Cvc3Exception {
	Object[] assumptions = jniGetAssumptions(embedded());
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public List getAssumptionsUsed() throws Cvc3Exception {
	Object[] assumptions = jniGetAssumptionsUsed(embedded());
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public List getCounterExample() throws Cvc3Exception {
	return getCounterExample(true);
    }

    public List getCounterExample(boolean inOrder) throws Cvc3Exception {
	Object[] assumptions = jniGetCounterExample(embedded(), inOrder);
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public HashMap getConcreteModel() throws Cvc3Exception {
	Object[] model = jniGetConcreteModel(embedded());
	return JniUtils.embedHashMap(model, Expr.class, Expr.class, embeddedManager());
    }

    public FormulaValue value(Expr expr) throws Cvc3Exception {
	return FormulaValue.get(jniValue(embedded(), expr.embedded()));
    }

    public Expr getValue(Expr expr) throws Cvc3Exception {
	return new ExprMut(
	  jniGetValue(embedded(), expr.embedded()),
	  embeddedManager());
    }

    public boolean inconsistent() throws Cvc3Exception {
	return jniInconsistent1(embedded());
    }

    // makes only sense if inconsistent is true
    public List inconsistentReasons() throws Cvc3Exception {
	Object[] assumptions = jniInconsistent2(embedded());
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public boolean incomplete() throws Cvc3Exception {
	return jniIncomplete1(embedded());
    }

    // makes only sense if incomplete is true
    public List incompleteReasons() throws Cvc3Exception {
	Object[] assumptions = jniIncomplete2(embedded());
	return JniUtils.embedList(assumptions, String.class, embeddedManager());
    }

    public ProofMut getProof() throws Cvc3Exception {
	return new ProofMut(
	  jniGetProof(embedded()),
	  embeddedManager());
    }

    public ExprMut getTCC() throws Cvc3Exception {
	return new ExprMut(
	  jniGetTCC(embedded()),
	  embeddedManager());
    }

    public List getAssumptionsTCC() throws Cvc3Exception {
	Object[] assumptions = jniGetAssumptionsTCC(embedded());
	return JniUtils.embedList(assumptions, ExprMut.class, embeddedManager());
    }

    public ProofMut getProofTCC() throws Cvc3Exception {
	return new ProofMut(
	  jniGetProofTCC(embedded()),
	  embeddedManager());
    }

    public ExprMut getClosure() throws Cvc3Exception {
	return new ExprMut(
	  jniGetClosure(embedded()),
	  embeddedManager());
    }

    public ProofMut getProofClosure() throws Cvc3Exception {
	return new ProofMut(
	  jniGetProofClosure(embedded()),
	  embeddedManager());
    }




    // Context Methods

    public int stackLevel() throws Cvc3Exception {
	return jniStackLevel(embedded());
    }

    public void push() throws Cvc3Exception {
	jniPush(embedded());
    }

    public void pop() throws Cvc3Exception {
	jniPop(embedded());
	//:TEST:
	embeddedManager().cleanUp();
    }

    public void popTo(int stackLevel) throws Cvc3Exception {
	jniPopTo(embedded(), stackLevel);
	//:TEST:
	embeddedManager().cleanUp();
    }

    public int scopeLevel() throws Cvc3Exception {
	return jniScopeLevel(embedded());
    }

    public void pushScope() throws Cvc3Exception {
	jniPushScope(embedded());
    }

    public void popScope() throws Cvc3Exception {
	jniPopScope(embedded());
    }

    public void popToScope(int scopeLevel) throws Cvc3Exception {
	jniPopToScope(embedded(), scopeLevel);
    }

    public ContextMut getCurrentContext() throws Cvc3Exception {
	return new ContextMut(
	  jniGetCurrentContext(embedded()),
	  embeddedManager());
    }




    // Reading Files

    public void loadFile(String fileName) throws Cvc3Exception {
	loadFile(fileName, InputLanguage.PRESENTATION);
    }

    public void loadFile(String fileName, InputLanguage lang) throws Cvc3Exception {
	jniLoadFile1(embedded(), fileName, lang.toString());
    }

    // Reporting Statistics
    
    public void printStatistics() throws Cvc3Exception {
	jniPrintStatistics(embedded());
    }

    public StatisticsMut getStatistics() throws Cvc3Exception {
	return new StatisticsMut(
	  jniGetStatistics(embedded()),
	  embeddedManager());
    }

    public void setTimeLimit(int limit) throws Cvc3Exception {
        jniSetTimeLimit(embedded(), limit);
    }
}
