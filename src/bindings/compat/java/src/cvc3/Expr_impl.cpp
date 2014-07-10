//INCLUDE: <expr.h>
//INCLUDE: <theory_array.h>
//INCLUDE: <theory_arith.h>
//INCLUDE: <theory_bitvector.h>

DEFINITION: Java_cvc3_Expr_jniEquals
jboolean c Expr expr1 c Expr expr2
return *expr1 == *expr2;

DEFINITION: Java_cvc3_Expr_jniToString
jstring c Expr expr
return toJava(env, expr->toString());

DEFINITION: Java_cvc3_Expr_jniPrint
void c Expr expr n string lang n bool dagify
dagify ? expr->pprint() : expr->pprintnodag();

DEFINITION: Java_cvc3_Expr_jniHash
jint c Expr expr
return expr->hash();

DEFINITION: Java_cvc3_Expr_jniGetKind
jstring c Expr expr
return toJava(env, expr->getEM()->getKindName( expr->getKind() ));

DEFINITION: Java_cvc3_Expr_jniIsFalse
jboolean c Expr expr
return expr->isFalse();

DEFINITION: Java_cvc3_Expr_jniIsTrue
jboolean c Expr expr
return expr->isTrue();

DEFINITION: Java_cvc3_Expr_jniIsBoolConst
jboolean c Expr expr
return expr->isBoolConst();

DEFINITION: Java_cvc3_Expr_jniIsVar
jboolean c Expr expr
return expr->isVar();

DEFINITION: Java_cvc3_Expr_jniIsBoundVar
jboolean c Expr expr
return expr->isBoundVar();

DEFINITION: Java_cvc3_Expr_jniIsString
jboolean c Expr expr
return expr->isString();

DEFINITION: Java_cvc3_Expr_jniIsClosure
jboolean c Expr expr
return expr->isClosure();

DEFINITION: Java_cvc3_Expr_jniIsQuantifier
jboolean c Expr expr
return expr->isQuantifier();

DEFINITION: Java_cvc3_Expr_jniIsLambda
jboolean c Expr expr
return expr->isLambda();

DEFINITION: Java_cvc3_Expr_jniIsApply
jboolean c Expr expr
return expr->isApply();

DEFINITION: Java_cvc3_Expr_jniIsSymbol
jboolean c Expr expr
return expr->isSymbol();

DEFINITION: Java_cvc3_Expr_jniIsTheorem
jboolean c Expr expr
return expr->isTheorem();

DEFINITION: Java_cvc3_Expr_jniIsType
jboolean c Expr expr
return expr->isType();



DEFINITION: Java_cvc3_Expr_jniIsTerm
jboolean c Expr expr
return expr->isTerm();

DEFINITION: Java_cvc3_Expr_jniIsAtomic
jboolean c Expr expr
return expr->isAtomic();

DEFINITION: Java_cvc3_Expr_jniIsAtomicFormula
jboolean c Expr expr
return expr->isAtomicFormula();

DEFINITION: Java_cvc3_Expr_jniIsAbsAtomicFormula
jboolean c Expr expr
return expr->isAbsAtomicFormula();

DEFINITION: Java_cvc3_Expr_jniIsLiteral
jboolean c Expr expr
return expr->isLiteral();

DEFINITION: Java_cvc3_Expr_jniIsAbsLiteral
jboolean c Expr expr
return expr->isAbsLiteral();

DEFINITION: Java_cvc3_Expr_jniIsBoolConnective
jboolean c Expr expr
return expr->isBoolConnective();

DEFINITION: Java_cvc3_Expr_jniIsPropAtom
jboolean c Expr expr
return expr->isPropAtom();

DEFINITION: Java_cvc3_Expr_jniIsPropLiteral
jboolean c Expr expr
return expr->isPropLiteral();

DEFINITION: Java_cvc3_Expr_jniIsArrayLiteral
jboolean c Expr expr
return CVC3::isArrayLiteral(*expr);


DEFINITION: Java_cvc3_Expr_jniIsEq
jboolean c Expr expr
return expr->isEq();

DEFINITION: Java_cvc3_Expr_jniIsNot
jboolean c Expr expr
return expr->isNot();

DEFINITION: Java_cvc3_Expr_jniIsAnd
jboolean c Expr expr
return expr->isAnd();

DEFINITION: Java_cvc3_Expr_jniIsOr
jboolean c Expr expr
return expr->isOr();

DEFINITION: Java_cvc3_Expr_jniIsITE
jboolean c Expr expr
return expr->isITE();

DEFINITION: Java_cvc3_Expr_jniIsIff
jboolean c Expr expr
return expr->isIff();

DEFINITION: Java_cvc3_Expr_jniIsImpl
jboolean c Expr expr
return expr->isImpl();

DEFINITION: Java_cvc3_Expr_jniIsXor
jboolean c Expr expr
return expr->isXor();

DEFINITION: Java_cvc3_Expr_jniIsForall
jboolean c Expr expr
return expr->isForall();

DEFINITION: Java_cvc3_Expr_jniIsExists
jboolean c Expr expr
return expr->isExists();

DEFINITION: Java_cvc3_Expr_jniIsRational
jboolean c Expr expr
return expr->isRational();

DEFINITION: Java_cvc3_Expr_jniIsUminus
jboolean c Expr expr
return expr->getKind() == UMINUS;

DEFINITION: Java_cvc3_Expr_jniIsPlus
jboolean c Expr expr
return expr->getKind() == PLUS;

DEFINITION: Java_cvc3_Expr_jniIsMinus
jboolean c Expr expr
return expr->getKind() == MINUS;

DEFINITION: Java_cvc3_Expr_jniIsMult
jboolean c Expr expr
return expr->getKind() == MULT;

DEFINITION: Java_cvc3_Expr_jniIsPow
jboolean c Expr expr
return expr->getKind() == POW;

DEFINITION: Java_cvc3_Expr_jniIsDivide
jboolean c Expr expr
return expr->getKind() == DIVIDE;

DEFINITION: Java_cvc3_Expr_jniIsLt
jboolean c Expr expr
return expr->getKind() == LT;

DEFINITION: Java_cvc3_Expr_jniIsLe
jboolean c Expr expr
return expr->getKind() == LE;

DEFINITION: Java_cvc3_Expr_jniIsGt
jboolean c Expr expr
return expr->getKind() == GT;

DEFINITION: Java_cvc3_Expr_jniIsGe
jboolean c Expr expr
return expr->getKind() == GE;

DEFINITION: Java_cvc3_Expr_jniIsSkolem
jboolean c Expr expr
return expr->isSkolem();


DEFINITION: Java_cvc3_Expr_jniIsRead
jboolean c Expr expr
return expr->getKind() == READ;

DEFINITION: Java_cvc3_Expr_jniIsWrite
jboolean c Expr expr
return expr->getKind() == WRITE;


DEFINITION: Java_cvc3_Expr_jniGetName
jstring c Expr expr
return toJava(env, expr->getName());

DEFINITION: Java_cvc3_Expr_jniGetUid
jstring c Expr expr
return toJava(env, expr->getUid());

DEFINITION: Java_cvc3_Expr_jniGetString
jstring c Expr expr
return toJava(env, expr->getString());

DEFINITION: Java_cvc3_Expr_jniGetVars
jobjectArray c Expr expr
return toJavaVConstRef(env, expr->getVars());

DEFINITION: Java_cvc3_Expr_jniGetExistential
jobject c Expr expr
return embed_copy<Expr>(env, expr->getExistential());

DEFINITION: Java_cvc3_Expr_jniGetBoundIndex
jint c Expr expr
return expr->getBoundIndex();

DEFINITION: Java_cvc3_Expr_jniGetBody
jobject c Expr expr
return embed_copy<Expr>(env, expr->getBody());

DEFINITION: Java_cvc3_Expr_jniGetRational
jobject c Expr expr
return embed_const_ref<Rational>(env, &expr->getRational());

DEFINITION: Java_cvc3_Expr_jniGetTriggers
jobjectArray c Expr expr
return toJavaVVConstRef(env, expr->getTriggers());

DEFINITION: Java_cvc3_Expr_jniGetTheorem
jobject c Expr expr
return embed_copy<Theorem>(env, expr->getTheorem());

DEFINITION: Java_cvc3_Expr_jniGetType
jobject c Expr expr
return embed_copy<Type>(env, expr->getType());

DEFINITION: Java_cvc3_Expr_jniMkOp
jobject c Expr expr
return embed_copy<Op>(env, expr->mkOp());

DEFINITION: Java_cvc3_Expr_jniGetOp
jobject c Expr expr
return embed_copy<Op>(env, expr->getOp());

DEFINITION: Java_cvc3_Expr_jniGetOpExpr
jobject c Expr expr
return embed_copy<Expr>(env, expr->getOpExpr());

DEFINITION: Java_cvc3_Expr_jniIsNull
jboolean c Expr expr
return expr->isNull();

DEFINITION: Java_cvc3_Expr_jniArity
jint c Expr expr
return expr->arity();

DEFINITION: Java_cvc3_Expr_jniGetKid
jobject c Expr expr n int i
return embed_copy<Expr>(env, (*expr)[ji]);

DEFINITION: Java_cvc3_Expr_jniGetKids
jobjectArray c Expr expr
return toJavaVConstRef(env, expr->getKids());

DEFINITION: Java_cvc3_Expr_jniSubstExpr
jobject c Expr e cv Expr oldExprs cv Expr newExprs
return embed_copy(env, e->substExpr(oldExprs,newExprs));

DEFINITION: Java_cvc3_Expr_jniIsBvLt
jboolean c Expr expr
return expr->getKind() == BVLT;

DEFINITION: Java_cvc3_Expr_jniIsBvLe
jboolean c Expr expr
return expr->getKind() == BVLE;

DEFINITION: Java_cvc3_Expr_jniIsBvGt
jboolean c Expr expr
return expr->getKind() == BVGT;

DEFINITION: Java_cvc3_Expr_jniIsBvGe
jboolean c Expr expr
return expr->getKind() == BVGE;

DEFINITION: Java_cvc3_Expr_jniIsBvPlus
jboolean c Expr expr
return expr->getKind() == BVPLUS;

DEFINITION: Java_cvc3_Expr_jniIsBvSub
jboolean c Expr expr
return expr->getKind() == BVSUB;

DEFINITION: Java_cvc3_Expr_jniIsBvConst
jboolean c Expr expr
return expr->getKind() == BVCONST;

DEFINITION: Java_cvc3_Expr_jniIsBvExtract
jboolean c Expr expr
return expr->getKind() == EXTRACT;

DEFINITION: Java_cvc3_Expr_jniIsBvConcat
jboolean c Expr expr
return expr->getKind() == CONCAT;
