INCLUDE: <expr_op.h>

DEFINITION: Java_cvc3_Op_jniEquals
jboolean c Op op1 c Op op2
return *op1 == *op2;
 
DEFINITION: Java_cvc3_Op_jniToString
jstring c Op op
return toJava(env, op->toString());
 

DEFINITION: Java_cvc3_Op_jniGetExpr
jobject c Op op
return embed_const_ref<Expr>(env, &op->getExpr());

DEFINITION: Java_cvc3_Op_jniIsNull
jboolean c Op op
return op->isNull();
