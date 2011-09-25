DEFINITION: Java_cvc3_FlagsMut_jniSetFlag1
void m CLFlags flags n string name n bool value
flags->setFlag(name, value);

DEFINITION: Java_cvc3_FlagsMut_jniSetFlag2
void m CLFlags flags n string name n int value
flags->setFlag(name, value);

DEFINITION: Java_cvc3_FlagsMut_jniSetFlag3
void m CLFlags flags n string name n string value
flags->setFlag(name, value);

DEFINITION: Java_cvc3_FlagsMut_jniSetFlag4
void m CLFlags flags n string map n string name n bool value
flags->setFlag(map, std::make_pair(name, value));
