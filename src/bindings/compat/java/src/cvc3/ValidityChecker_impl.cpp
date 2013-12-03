INCLUDE: <sstream>
//INCLUDE: <theory_arith.h>
//INCLUDE: <theory_array.h>

DEFINITION: Java_cvc3_ValidityChecker_jniCreate1
jobject
return embed_own<ValidityChecker>(env, ValidityChecker::create());

DEFINITION: Java_cvc3_ValidityChecker_jniCreate2
jobject c CLFlags flags
return embed_own<ValidityChecker>(env, ValidityChecker::create(*flags));



DEFINITION: Java_cvc3_ValidityChecker_jniCreateFlags
jobject
return embed_copy(env, ValidityChecker::createFlags());

DEFINITION: Java_cvc3_ValidityChecker_jniGetFlags
jobject c ValidityChecker vc
return embed_mut_ref(env, &vc->getFlags());



DEFINITION: Java_cvc3_ValidityChecker_jniBoolType
jobject m ValidityChecker vc
return embed_copy(env, vc->boolType());

DEFINITION: Java_cvc3_ValidityChecker_jniRealType
jobject m ValidityChecker vc
return embed_copy(env, vc->realType());

DEFINITION: Java_cvc3_ValidityChecker_jniIntType
jobject m ValidityChecker vc
return embed_copy(env, vc->intType());

DEFINITION: Java_cvc3_ValidityChecker_jniSubrangeType
jobject m ValidityChecker vc c Expr l c Expr r
return embed_copy(env, vc->subrangeType(*l, *r));

DEFINITION: Java_cvc3_ValidityChecker_jniSubtypeType
jobject m ValidityChecker vc c Expr pred c Expr witness
return embed_copy(env, vc->subtypeType(*pred, *witness));

DEFINITION: Java_cvc3_ValidityChecker_jniTupleType1
jobject m ValidityChecker vc c Type type0 c Type type1
return embed_copy(env, vc->tupleType(*type0, *type1));

DEFINITION: Java_cvc3_ValidityChecker_jniTupleType2
jobject m ValidityChecker vc c Type type0 c Type type1 c Type type2
return embed_copy(env, vc->tupleType(*type0, *type1, *type2));

DEFINITION: Java_cvc3_ValidityChecker_jniTupleType3
jobject m ValidityChecker vc cv Type types
return embed_copy(env, vc->tupleType(types));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordType1
jobject m ValidityChecker vc n string field c Type type
return embed_copy(env, vc->recordType(field, *type));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordType2
jobject m ValidityChecker vc n string field0 c Type type0 n string field1 c Type type1
return embed_copy(env, vc->recordType(field0, *type0, field1, *type1));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordType3
jobject m ValidityChecker vc n string field0 c Type type0 n string field1 c Type type1 n string field2 c Type type2
return embed_copy(env, vc->recordType(field0, *type0, field1, *type1, field2, *type2));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordType4
jobject m ValidityChecker vc nv string fields cv Type types
return embed_copy(env, vc->recordType(fields, types));

DEFINITION: Java_cvc3_ValidityChecker_jniDataType1
jobject m ValidityChecker vc n string name n string constructor nv string selectors cv Expr types
return embed_copy(env, vc->dataType(name, constructor, selectors, types));

DEFINITION: Java_cvc3_ValidityChecker_jniDataType2
jobject m ValidityChecker vc n string name nv string constructors nvv string selectors cvv Expr types
return embed_copy(env, vc->dataType(name, constructors, selectors, types));

DEFINITION: Java_cvc3_ValidityChecker_jniDataType3
jobjectArray m ValidityChecker vc nv string names nvv string constructors nvvv string selectors cvvv Expr types
vector<Type> result;
vc->dataType(names, constructors, selectors, types, result);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniAnyType
jobject m ValidityChecker vc
assert(false);// Unimplemented
return NULL;

DEFINITION: Java_cvc3_ValidityChecker_jniArrayLiteral
jobject m ValidityChecker vc c Expr indexVar c Expr bodyExpr
assert(false);// Unimplemented
return NULL;

DEFINITION: Java_cvc3_ValidityChecker_jniArrayType
jobject m ValidityChecker vc c Type typeIndex c Type typeData
return embed_copy(env, vc->arrayType(*typeIndex, *typeData));

DEFINITION: Java_cvc3_ValidityChecker_jniBitvecType
jobject m ValidityChecker vc n int n
return embed_copy(env, vc->bitvecType(n));

DEFINITION: Java_cvc3_ValidityChecker_jniFunType1
jobject m ValidityChecker vc c Type typeDom c Type typeRange
return embed_copy(env, vc->funType(*typeDom, *typeRange));

DEFINITION: Java_cvc3_ValidityChecker_jniFunType2
jobject m ValidityChecker vc cv Type typeDom c Type typeRange
return embed_copy(env, vc->funType(typeDom, *typeRange));

DEFINITION: Java_cvc3_ValidityChecker_jniCreateType1
jobject m ValidityChecker vc n string typeName
return embed_copy(env, vc->createType(typeName));

DEFINITION: Java_cvc3_ValidityChecker_jniCreateType2
jobject m ValidityChecker vc n string typeName c Type typeDef
return embed_copy(env, vc->createType(typeName, *typeDef));

DEFINITION: Java_cvc3_ValidityChecker_jniLookupType
jobject m ValidityChecker vc n string typeName
return embed_copy(env, vc->lookupType(typeName));



DEFINITION: Java_cvc3_ValidityChecker_jniGetExprManager
jobject m ValidityChecker vc
return embed_mut_ref(env, vc->getEM());

DEFINITION: Java_cvc3_ValidityChecker_jniNullExpr
jobject m ValidityChecker vc
return embed_copy(env, Expr());

DEFINITION: Java_cvc3_ValidityChecker_jniVarExpr1
jobject m ValidityChecker vc n string name c Type type
return embed_copy(env, vc->varExpr(name, *type));

DEFINITION: Java_cvc3_ValidityChecker_jniVarExpr2
jobject m ValidityChecker vc n string name c Type type c Expr def
return embed_copy(env, vc->varExpr(name, *type, *def));

DEFINITION: Java_cvc3_ValidityChecker_jniBoundVarExpr
jobject m ValidityChecker vc n string name n string uid c Type type
return embed_copy(env, vc->boundVarExpr(name, uid, *type));

DEFINITION: Java_cvc3_ValidityChecker_jniLookupVar
jobject m ValidityChecker vc n string name 
Type* type = new Type;
jobject result = embed_copy(env, vc->lookupVar(name, type));
delete type;
return result;

DEFINITION: Java_cvc3_ValidityChecker_jniLookupOp
jobject m ValidityChecker vc n string name
Type* type = new Type;
jobject result = embed_copy(env, vc->lookupOp(name, type));
delete type;
return result;

DEFINITION: Java_cvc3_ValidityChecker_jniGetType
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->getType(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniGetBaseType1
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->getBaseType(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniGetBaseType2
jobject m ValidityChecker vc c Type type
return embed_copy(env, vc->getBaseType(*type));

DEFINITION: Java_cvc3_ValidityChecker_jniGetTypePred
jobject m ValidityChecker vc c Type type c Expr expr
return embed_copy(env, vc->getTypePred(*type, *expr));

DEFINITION: Java_cvc3_ValidityChecker_jniStringExpr
jobject m ValidityChecker vc n string str
return embed_copy(env, vc->stringExpr(str));

DEFINITION: Java_cvc3_ValidityChecker_jniIdExpr
jobject m ValidityChecker vc n string name
return embed_copy(env, vc->idExpr(name));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr1
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->listExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr2
jobject m ValidityChecker vc c Expr expr1
return embed_copy(env, vc->listExpr(*expr1));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr3
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->listExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr4
jobject m ValidityChecker vc c Expr expr1 c Expr expr2 c Expr expr3
return embed_copy(env, vc->listExpr(*expr1, *expr2, *expr3));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr5
jobject m ValidityChecker vc n string op cv Expr kids
return embed_copy(env, vc->listExpr(op, kids));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr6
jobject m ValidityChecker vc n string op c Expr expr1
return embed_copy(env, vc->listExpr(op, *expr1));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr7
jobject m ValidityChecker vc n string op c Expr expr1 c Expr expr2
return embed_copy(env, vc->listExpr(op, *expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniListExpr8
jobject m ValidityChecker vc n string op c Expr expr1 c Expr expr2 c Expr expr3
return embed_copy(env, vc->listExpr(op, *expr1, *expr2, *expr3));


DEFINITION: Java_cvc3_ValidityChecker_jniPrintExpr
void m ValidityChecker vc c Expr expr
vc->printExpr(*expr);

DEFINITION: Java_cvc3_ValidityChecker_jniParseExpr
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->parseExpr(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniParseType
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->parseType(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniImportExpr
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->importExpr(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniImportType
jobject m ValidityChecker vc c Type type
return embed_copy(env, vc->importType(*type));

DEFINITION: Java_cvc3_ValidityChecker_jniCmdsFromString
void m ValidityChecker vc n string s
vc->cmdsFromString(s);

DEFINITION: Java_cvc3_ValidityChecker_jniExprFromString
jobject m ValidityChecker vc n string s
return embed_copy<Expr>(env, vc->exprFromString(s));

DEFINITION: Java_cvc3_ValidityChecker_jniTrueExpr
jobject m ValidityChecker vc
return embed_copy<Expr>(env, vc->trueExpr());

DEFINITION: Java_cvc3_ValidityChecker_jniFalseExpr
jobject m ValidityChecker vc
return embed_copy<Expr>(env, vc->falseExpr());

DEFINITION: Java_cvc3_ValidityChecker_jniNotExpr
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->notExpr(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniAndExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->andExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniAndExpr2
jobject m ValidityChecker vc cv Expr children
return embed_copy(env, vc->andExpr(children));

DEFINITION: Java_cvc3_ValidityChecker_jniOrExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->orExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniOrExpr2
jobject m ValidityChecker vc cv Expr children
return embed_copy(env, vc->orExpr(children));

DEFINITION: Java_cvc3_ValidityChecker_jniImpliesExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->impliesExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniIffExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->iffExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniEqExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->eqExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniDistinctExpr
jobject m ValidityChecker vc cv Expr children
return embed_copy(env, vc->distinctExpr(children));

DEFINITION: Java_cvc3_ValidityChecker_jniIteExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2 c Expr expr3
return embed_copy(env, vc->iteExpr(*expr1, *expr2, *expr3));

DEFINITION: Java_cvc3_ValidityChecker_jniCreateOp1
jobject m ValidityChecker vc n string name c Type type
return embed_copy(env, vc->createOp(name, *type));

DEFINITION: Java_cvc3_ValidityChecker_jniCreateOp2
jobject m ValidityChecker vc n string name c Type type c Expr expr
return embed_copy(env, vc->createOp(name, *type, *expr));

DEFINITION: Java_cvc3_ValidityChecker_jniEqOp
jobject
return embed_copy<Op>(env, Op(EQ));

DEFINITION: Java_cvc3_ValidityChecker_jniLtOp
jobject
return embed_copy<Op>(env, Op(LT));

DEFINITION: Java_cvc3_ValidityChecker_jniLeOp
jobject
return embed_copy<Op>(env, Op(LE));

DEFINITION: Java_cvc3_ValidityChecker_jniGtOp
jobject
return embed_copy<Op>(env, Op(GT));

DEFINITION: Java_cvc3_ValidityChecker_jniGeOp
jobject
return embed_copy<Op>(env, Op(GE));

DEFINITION: Java_cvc3_ValidityChecker_jniPlusOp
jobject
return embed_copy<Op>(env, Op(PLUS));

DEFINITION: Java_cvc3_ValidityChecker_jniMinusOp
jobject
return embed_copy<Op>(env, Op(MINUS));

DEFINITION: Java_cvc3_ValidityChecker_jniMultOp
jobject
return embed_copy<Op>(env, Op(MULT));

DEFINITION: Java_cvc3_ValidityChecker_jniDivideOp
jobject
return embed_copy<Op>(env, Op(DIVIDE));


DEFINITION: Java_cvc3_ValidityChecker_jniFunExpr1
jobject m ValidityChecker vc c Op op c Expr expr1
return embed_copy(env, vc->funExpr(*op, *expr1));

DEFINITION: Java_cvc3_ValidityChecker_jniFunExpr2
jobject m ValidityChecker vc c Op op c Expr expr1 c Expr expr2
return embed_copy(env, vc->funExpr(*op, *expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniFunExpr3
jobject m ValidityChecker vc c Op op c Expr expr1 c Expr expr2 c Expr expr3
return embed_copy(env, vc->funExpr(*op, *expr1, *expr2, *expr3));

DEFINITION: Java_cvc3_ValidityChecker_jniFunExpr4
jobject m ValidityChecker vc c Op op cv Expr children
return embed_copy(env, vc->funExpr(*op, children));

DEFINITION: Java_cvc3_ValidityChecker_jniRatExpr1
jobject m ValidityChecker vc n int n n int d
return embed_copy(env, vc->ratExpr(n, d));

DEFINITION: Java_cvc3_ValidityChecker_jniRatExpr2
jobject m ValidityChecker vc n string n n string d n int base
return embed_copy(env, vc->ratExpr(n, d, base));

DEFINITION: Java_cvc3_ValidityChecker_jniRatExpr3
jobject m ValidityChecker vc n string n n int base
return embed_copy(env, vc->ratExpr(n, base));

DEFINITION: Java_cvc3_ValidityChecker_jniUminusExpr
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->uminusExpr(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniPlusExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->plusExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniPlusExpr2
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->plusExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniMinusExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->minusExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniMultExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->multExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniPowExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->powExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniDivideExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->divideExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniLtExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->ltExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniLeExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->leExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniGtExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->gtExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniGeExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->geExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordExpr1
jobject m ValidityChecker vc n string field c Expr expr
return embed_copy(env, vc->recordExpr(field, *expr));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordExpr2
jobject m ValidityChecker vc n string field1 c Expr expr1 n string field2 c Expr expr2
return embed_copy(env, vc->recordExpr(field1, *expr1, field2, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordExpr3
jobject m ValidityChecker vc n string field1 c Expr expr1 n string field2 c Expr expr2 n string field3 c Expr expr3
return embed_copy(env, vc->recordExpr(field1, *expr1, field2, *expr2, field3, *expr3));

DEFINITION: Java_cvc3_ValidityChecker_jniRecordExpr4
jobject m ValidityChecker vc nv string fields cv Expr exprs
return embed_copy(env, vc->recordExpr(fields, exprs));

DEFINITION: Java_cvc3_ValidityChecker_jniRecSelectExpr
jobject m ValidityChecker vc c Expr record n string field
return embed_copy(env, vc->recSelectExpr(*record, field));

DEFINITION: Java_cvc3_ValidityChecker_jniRecUpdateExpr
jobject m ValidityChecker vc c Expr record n string field c Expr update
return embed_copy(env, vc->recUpdateExpr(*record, field, *update));

DEFINITION: Java_cvc3_ValidityChecker_jniReadExpr
jobject m ValidityChecker vc c Expr array c Expr index
return embed_copy(env, vc->readExpr(*array, *index));

DEFINITION: Java_cvc3_ValidityChecker_jniWriteExpr
jobject m ValidityChecker vc c Expr array c Expr index c Expr value
return embed_copy(env, vc->writeExpr(*array, *index, *value));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVConstExpr1
jobject m ValidityChecker vc n string s n int base
return embed_copy(env, vc->newBVConstExpr(s, jbase));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVConstExpr2
jobject m ValidityChecker vc nv bool bits
return embed_copy(env, vc->newBVConstExpr(bits));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVConstExpr3
jobject m ValidityChecker vc c Rational rational n int len
return embed_copy(env, vc->newBVConstExpr(*rational, len));

DEFINITION: Java_cvc3_ValidityChecker_jniNewConcatExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newConcatExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewConcatExpr2
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->newConcatExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVExtractExpr
jobject m ValidityChecker vc c Expr expr n int hi n int low
return embed_copy(env, vc->newBVExtractExpr(*expr, hi, low));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVNegExpr
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->newBVNegExpr(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVAndExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVAndExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVAndExpr2
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->newBVAndExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVOrExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVOrExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVOrExpr2
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->newBVOrExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVXorExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVXorExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVXorExpr2
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->newBVXorExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVXnorExpr1
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVXnorExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVXnorExpr2
jobject m ValidityChecker vc cv Expr kids
return embed_copy(env, vc->newBVXnorExpr(kids));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVNandExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVNandExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVNorExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVNorExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVLTExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVLTExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVLEExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVLEExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSLTExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSLTExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSLEExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSLEExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewSXExpr
jobject m ValidityChecker vc c Expr expr n int len
return embed_copy(env, vc->newSXExpr(*expr, len));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVUminusExpr
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->newBVUminusExpr(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSubExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSubExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVPlusExpr
jobject m ValidityChecker vc n int numbits cv Expr exprs
return embed_copy(env, vc->newBVPlusExpr(numbits, exprs));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVMultExpr
jobject m ValidityChecker vc n int numbits c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVMultExpr(numbits, *expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVUDivExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVUDivExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVURemExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVURemExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSDivExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSDivExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSRemExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSRemExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSModExpr
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSModExpr(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVSHL
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVSHL(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVLSHR
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVLSHR(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewBVASHR
jobject m ValidityChecker vc c Expr expr1 c Expr expr2
return embed_copy(env, vc->newBVASHR(*expr1, *expr2));

DEFINITION: Java_cvc3_ValidityChecker_jniNewFixedLeftShiftExpr
jobject m ValidityChecker vc c Expr expr n int r
return embed_copy(env, vc->newFixedLeftShiftExpr(*expr, r));

DEFINITION: Java_cvc3_ValidityChecker_jniNewFixedConstWidthLeftShiftExpr
jobject m ValidityChecker vc c Expr expr n int r
return embed_copy(env, vc->newFixedConstWidthLeftShiftExpr(*expr, r));

DEFINITION: Java_cvc3_ValidityChecker_jniNewFixedRightShiftExpr
jobject m ValidityChecker vc c Expr expr n int r
return embed_copy(env, vc->newFixedRightShiftExpr(*expr, r));

DEFINITION: Java_cvc3_ValidityChecker_jniComputeBVConst
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->computeBVConst(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniTupleExpr
jobject m ValidityChecker vc cv Expr exprs
return embed_copy(env, vc->tupleExpr(exprs));

DEFINITION: Java_cvc3_ValidityChecker_jniTupleSelectExpr
jobject m ValidityChecker vc c Expr tuple n int index
return embed_copy(env, vc->tupleSelectExpr(*tuple, index));

DEFINITION: Java_cvc3_ValidityChecker_jniTupleUpdateExpr
jobject m ValidityChecker vc c Expr tuple n int index c Expr value
return embed_copy(env, vc->tupleUpdateExpr(*tuple, index, *value));

DEFINITION: Java_cvc3_ValidityChecker_jniDatatypeConsExpr
jobject m ValidityChecker vc n string constructor cv Expr exprs
return embed_copy(env, vc->datatypeConsExpr(constructor, exprs));

DEFINITION: Java_cvc3_ValidityChecker_jniDatatypeSelExpr
jobject m ValidityChecker vc n string selector c Expr expr
return embed_copy(env, vc->datatypeSelExpr(selector, *expr));

DEFINITION: Java_cvc3_ValidityChecker_jniDatatypeTestExpr
jobject m ValidityChecker vc n string constructor c Expr expr
return embed_copy(env, vc->datatypeTestExpr(constructor, *expr));

DEFINITION: Java_cvc3_ValidityChecker_jniForallExpr1
jobject m ValidityChecker vc cv Expr vars c Expr body
return embed_copy(env, vc->forallExpr(vars, *body));

DEFINITION: Java_cvc3_ValidityChecker_jniForallExpr2
jobject m ValidityChecker vc cv Expr vars c Expr body c Expr trigger
return embed_copy(env, vc->forallExpr(vars, *body, *trigger));

DEFINITION: Java_cvc3_ValidityChecker_jniForallExpr3
jobject m ValidityChecker vc cv Expr vars c Expr body cv Expr triggers
return embed_copy(env, vc->forallExpr(vars, *body, triggers));

DEFINITION: Java_cvc3_ValidityChecker_jniForallExpr4
jobject m ValidityChecker vc cv Expr vars c Expr body cvv Expr triggers
return embed_copy(env, vc->forallExpr(vars, *body, triggers));

DEFINITION: Java_cvc3_ValidityChecker_jniSetTrigger
void m ValidityChecker vc c Expr closure c Expr trigger
vc->setTrigger(*closure, *trigger);

DEFINITION: Java_cvc3_ValidityChecker_jniSetTriggers
void m ValidityChecker vc c Expr closure cv Expr triggers
vc->setTriggers(*closure, triggers);

DEFINITION: Java_cvc3_ValidityChecker_jniSetTriggers2
void m ValidityChecker vc c Expr closure cvv Expr triggers
vc->setTriggers(*closure, triggers);

DEFINITION: Java_cvc3_ValidityChecker_jniSetMultiTrigger
void m ValidityChecker vc c Expr closure cv Expr multiTrigger
vc->setMultiTrigger(*closure, multiTrigger);

DEFINITION: Java_cvc3_ValidityChecker_jniExistsExpr
jobject m ValidityChecker vc cv Expr vars c Expr body
return embed_copy(env, vc->existsExpr(vars, *body));

DEFINITION: Java_cvc3_ValidityChecker_jniLambdaExpr
jobject m ValidityChecker vc cv Expr vars c Expr body
return embed_copy(env, vc->lambdaExpr(vars, *body));

DEFINITION: Java_cvc3_ValidityChecker_jniTransClosure
jobject m ValidityChecker vc c Op p
return embed_copy(env, vc->transClosure(*p));

DEFINITION: Java_cvc3_ValidityChecker_jniSimulateExpr
jobject m ValidityChecker vc c Expr f c Expr s cv Expr inputs c Expr n
return embed_copy(env, vc->simulateExpr(*f, *s, inputs, *n));


DEFINITION: Java_cvc3_ValidityChecker_jniSetResourceLimit
void m ValidityChecker vc n int limit
vc->setResourceLimit(limit);

DEFINITION: Java_cvc3_ValidityChecker_jniAssertFormula
void m ValidityChecker vc c Expr expr
vc->assertFormula(*expr);

DEFINITION: Java_cvc3_ValidityChecker_jniRegisterAtom
void m ValidityChecker vc c Expr expr
vc->registerAtom(*expr);

DEFINITION: Java_cvc3_ValidityChecker_jniGetImpliedLiteral
jobject m ValidityChecker vc
return embed_copy(env, vc->getImpliedLiteral());

DEFINITION: Java_cvc3_ValidityChecker_jniSimplify
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->simplify(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniQuery
jstring m ValidityChecker vc c Expr expr
return toJava(env, vc->query(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniCheckUnsat
jstring m ValidityChecker vc c Expr expr
return toJava(env, vc->checkUnsat(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniCheckContinue
jstring m ValidityChecker vc
return toJava(env, vc->checkContinue());

DEFINITION: Java_cvc3_ValidityChecker_jniRestart
jstring m ValidityChecker vc c Expr expr
return toJava(env, vc->restart(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniReturnFromCheck
void m ValidityChecker vc
vc->returnFromCheck();

DEFINITION: Java_cvc3_ValidityChecker_jniGetUserAssumptions
jobjectArray m ValidityChecker vc
vector<Expr> result;
vc->getUserAssumptions(result);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniGetInternalAssumptions
jobjectArray m ValidityChecker vc
vector<Expr> result;
vc->getInternalAssumptions(result);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniGetAssumptions
jobjectArray m ValidityChecker vc
vector<Expr> result;
vc->getAssumptions(result);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniGetAssumptionsUsed
jobjectArray m ValidityChecker vc
vector<Expr> result;
vc->getAssumptionsUsed(result);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniGetCounterExample
jobjectArray m ValidityChecker vc n bool inOrder
vector<Expr> result;
vc->getCounterExample(result, inOrder);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniValue
jstring m ValidityChecker vc c Expr expr
return toJava(env, vc->value(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniGetValue
jobject m ValidityChecker vc c Expr expr
return embed_copy(env, vc->getValue(*expr));

DEFINITION: Java_cvc3_ValidityChecker_jniGetConcreteModel
jobjectArray m ValidityChecker vc
ExprMap<Expr> result;
vc->getConcreteModel(result);
return toJavaHCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniInconsistent1
jboolean m ValidityChecker vc
return vc->inconsistent();

DEFINITION: Java_cvc3_ValidityChecker_jniInconsistent2
jobjectArray m ValidityChecker vc
vector<Expr> result;
bool inconsistent = vc->inconsistent(result);
assert(inconsistent);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniIncomplete1
jboolean m ValidityChecker vc
return vc->incomplete();

DEFINITION: Java_cvc3_ValidityChecker_jniIncomplete2
jobjectArray m ValidityChecker vc
vector<std::string> result;
bool incomplete = vc->incomplete(result);
assert(incomplete);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniGetProof
jobject m ValidityChecker vc
return embed_copy(env, vc->getProof());

DEFINITION: Java_cvc3_ValidityChecker_jniGetTCC
jobject m ValidityChecker vc
return embed_copy(env, vc->getTCC());

DEFINITION: Java_cvc3_ValidityChecker_jniGetAssumptionsTCC
jobjectArray m ValidityChecker vc
vector<Expr> result;
vc->getAssumptionsTCC(result);
return toJavaVCopy(env, result);

DEFINITION: Java_cvc3_ValidityChecker_jniGetProofTCC
jobject m ValidityChecker vc
return embed_copy(env, vc->getProofTCC());

DEFINITION: Java_cvc3_ValidityChecker_jniGetClosure
jobject m ValidityChecker vc
return embed_copy(env, vc->getClosure());

DEFINITION: Java_cvc3_ValidityChecker_jniGetProofClosure
jobject m ValidityChecker vc
return embed_copy(env, vc->getProofClosure());






DEFINITION: Java_cvc3_ValidityChecker_jniStackLevel
jint m ValidityChecker vc
return vc->stackLevel();

DEFINITION: Java_cvc3_ValidityChecker_jniPush
void m ValidityChecker vc
vc->push();

DEFINITION: Java_cvc3_ValidityChecker_jniPop
void m ValidityChecker vc
vc->pop();

DEFINITION: Java_cvc3_ValidityChecker_jniPopTo
void m ValidityChecker vc n int stackLevel
vc->popto(stackLevel);

DEFINITION: Java_cvc3_ValidityChecker_jniScopeLevel
jint m ValidityChecker vc
return vc->scopeLevel();

DEFINITION: Java_cvc3_ValidityChecker_jniPushScope
void m ValidityChecker vc
vc->pushScope();

DEFINITION: Java_cvc3_ValidityChecker_jniPopScope
void m ValidityChecker vc
vc->popScope();

DEFINITION: Java_cvc3_ValidityChecker_jniPopToScope
void m ValidityChecker vc n int stackLevel
vc->poptoScope(stackLevel);

DEFINITION: Java_cvc3_ValidityChecker_jniGetCurrentContext
jobject m ValidityChecker vc
return embed_mut_ref(env, vc->getCurrentContext());





DEFINITION: Java_cvc3_ValidityChecker_jniLoadFile1
void m ValidityChecker vc n string fileName n string lang
vc->loadFile(fileName, toCppInputLanguage(env, lang), false);


DEFINITION: Java_cvc3_ValidityChecker_jniGetStatistics
jobject m ValidityChecker vc
return embed_copy(env, vc->getStatistics());

DEFINITION: Java_cvc3_ValidityChecker_jniPrintStatistics
void m ValidityChecker vc
vc->printStatistics();


DEFINITION: Java_cvc3_ValidityChecker_jniSetTimeLimit
void m ValidityChecker vc n int n
vc->setTimeLimit((unsigned int)n);
