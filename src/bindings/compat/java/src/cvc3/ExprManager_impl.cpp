DEFINITION: Java_cvc3_ExprManager_jniGetInputLanguage
jstring c ExprManager exprManager
return toJava(env, exprManager->getInputLang());

DEFINITION: Java_cvc3_ExprManager_jniGetOutputLanguage
jstring c ExprManager exprManager
return toJava(env, exprManager->getOutputLang());
