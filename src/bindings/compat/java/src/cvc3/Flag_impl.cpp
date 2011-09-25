DEFINITION: Java_cvc3_Flag_jniIsNull
jboolean c CLFlag flag
return (flag->getType() == CLFLAG_NULL);

DEFINITION: Java_cvc3_Flag_jniIsBool
jboolean c CLFlag flag
return (flag->getType() == CLFLAG_BOOL);

DEFINITION: Java_cvc3_Flag_jniIsInt
jboolean c CLFlag flag
return (flag->getType() == CLFLAG_INT);

DEFINITION: Java_cvc3_Flag_jniIsString
jboolean c CLFlag flag
return (flag->getType() == CLFLAG_STRING);

DEFINITION: Java_cvc3_Flag_jniIsStringVec
jboolean c CLFlag flag
return (flag->getType() == CLFLAG_STRVEC);


DEFINITION: Java_cvc3_Flag_jniGetBool
jboolean c CLFlag flag
return flag->getBool();

DEFINITION: Java_cvc3_Flag_jniGetInt
jint c CLFlag flag
return flag->getInt();

DEFINITION: Java_cvc3_Flag_jniGetString
jstring c CLFlag flag
return toJava(env, flag->getString());

DEFINITION: Java_cvc3_Flag_jniGetHelp
jstring c CLFlag flag
return toJava(env, flag->getHelp());
