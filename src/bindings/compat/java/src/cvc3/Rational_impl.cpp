INCLUDE: <rational.h>

DEFINITION: Java_cvc3_Rational_jniRational1
jobject n int n n int d
return embed_copy(env, Rational(n, d));

DEFINITION: Java_cvc3_Rational_jniRational2
jobject n string n n int d
return embed_copy(env, Rational(n, d));

DEFINITION: Java_cvc3_Rational_jniRational3
jobject n string n n string d n int base
return embed_copy(env, Rational(n, d, base));



DEFINITION: Java_cvc3_Rational_jniEquals
jboolean c Rational r1 c Rational r2
return *r1 == *r2;

DEFINITION: Java_cvc3_Rational_jniToString
jstring c Rational r
return toJava(env, r->toString());

DEFINITION: Java_cvc3_Rational_jniHash
jint c Rational r
return r->hash();



DEFINITION: Java_cvc3_Rational_jniIsLt
jboolean c Rational r1 c Rational r2
return *r1 < *r2;

DEFINITION: Java_cvc3_Rational_jniIsLe
jboolean c Rational r1 c Rational r2
return *r1 <= *r2;

DEFINITION: Java_cvc3_Rational_jniIsGt
jboolean c Rational r1 c Rational r2
return *r1 > *r2;

DEFINITION: Java_cvc3_Rational_jniIsGe
jboolean c Rational r1 c Rational r2
return *r1 >= *r2;



DEFINITION: Java_cvc3_Rational_jniPlus
jobject c Rational r1 c Rational r2
return embed_copy(env, *r1 + *r2);

DEFINITION: Java_cvc3_Rational_jniMinus
jobject c Rational r1 c Rational r2
return embed_copy(env, *r1 + *r2);

DEFINITION: Java_cvc3_Rational_jniMult
jobject c Rational r1 c Rational r2
return embed_copy(env, *r1 + *r2);

DEFINITION: Java_cvc3_Rational_jniDivide
jobject c Rational r1 c Rational r2
return embed_copy(env, *r1 + *r2);

DEFINITION: Java_cvc3_Rational_jniMod
jobject c Rational r1 c Rational r2
return embed_copy(env, *r1 % *r2);



DEFINITION: Java_cvc3_Rational_jniGetNumerator
jobject c Rational r
return embed_copy(env, r->getNumerator());

DEFINITION: Java_cvc3_Rational_jniGetDenominator
jobject c Rational r
return embed_copy(env, r->getDenominator());

DEFINITION: Java_cvc3_Rational_jniIsInteger
jboolean c Rational r
return r->isInteger();

DEFINITION: Java_cvc3_Rational_jniGetInteger
jint c Rational r
return r->getInt();

DEFINITION: Java_cvc3_Rational_jniGcd
jobject c Rational r1 c Rational r2
return embed_copy(env, gcd(*r1, *r2));

DEFINITION: Java_cvc3_Rational_jniLcm
jobject c Rational r1 c Rational r2
return embed_copy(env, lcm(*r1, *r2));

DEFINITION: Java_cvc3_Rational_jniAbs
jobject c Rational r
return embed_copy(env, abs(*r));

DEFINITION: Java_cvc3_Rational_jniFloor
jobject c Rational r
return embed_copy(env, floor(*r));

DEFINITION: Java_cvc3_Rational_jniCeil
jobject c Rational r
return embed_copy(env, ceil(*r));
