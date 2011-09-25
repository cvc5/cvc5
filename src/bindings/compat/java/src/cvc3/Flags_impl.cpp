DEFINITION: Java_cvc3_Flags_jniGetFlags
jobjectArray c CLFlags flags n string prefix
    
// get flag names
vector<string> names;
flags->countFlags(prefix, names);
return toJavaV(env, names);


DEFINITION: Java_cvc3_Flags_jniGetFlag
jobject c CLFlags flags n string name
const CLFlag& flag = flags->getFlag(name);
return embed_const_ref(env, &flag);
