//INCLUDE: "kinds.h"
//INCLUDE: "type.h"
//INCLUDE: "theory_array.h"
//INCLUDE: "theory_bitvector.h"
//INCLUDE: "theory_datatype.h"

DEFINITION: Java_cvc3_Type_jniConstr
jobject c Expr expr
return embed_copy<Type>(env, Type(*expr));

DEFINITION: Java_cvc3_Type_jniIsAny
jboolean c Type type
return type->getExpr().getKind() == ANY_TYPE;

DEFINITION: Java_cvc3_Type_jniIsArray
jboolean c Type type
return type->getExpr().getKind() == ARRAY;

DEFINITION: Java_cvc3_Type_jniIsBitvector
jboolean c Type type
return type->getExpr().getKind() == BITVECTOR;

DEFINITION: Java_cvc3_Type_jniIsBool
jboolean c Type type
return type->isBool();

DEFINITION: Java_cvc3_Type_jniIsDatatype
jboolean c Type type
return ::isDatatype(*type);

DEFINITION: Java_cvc3_Type_jniIsFunction
jboolean c Type type
return type->isFunction();

DEFINITION: Java_cvc3_Type_jniIsNull
jboolean c Type type
return type->isNull();

DEFINITION: Java_cvc3_Type_jniIsSubtype
jboolean c Type type
return type->isSubtype();



DEFINITION: Java_cvc3_Type_jniGetExpr
jobject c Type type
return embed_const_ref<Expr>(env, &type->getExpr());

DEFINITION: Java_cvc3_Type_jniArity
jint c Type type
return type->arity();

DEFINITION: Java_cvc3_Type_jniGetChild
jobject c Type type n int i
return embed_copy<Type>(env, (*type)[i]);




DEFINITION: Java_cvc3_Type_jniEquals
jboolean c Type type1 c Type type2
return *type1 == *type2;

DEFINITION: Java_cvc3_Type_jniToString
jstring c Type type
return toJava(env, type->toString());

