#!/usr/bin/env python

import sys
import os
import re


### output cpp file

# qualifiers:
# c   : embedded constant
# m   : embedded mutable
# n   : native
# plus:
# v   : vector
# vv  : vector vector
# vvv : vector vector vector

# types:
# - native: void, bool, int, string
# - objects: the rest

def is_native(arg_qual):
    return (arg_qual[0] == 'n')

def is_mutable(arg_qual):
    return (arg_qual[0] == 'm')

def is_const(arg_qual):
    return (arg_qual[0] == 'c')

def forall(p, s):
    for x in s:
        if not p(s):
            return False

    return True

def check_arg_qual(arg_qual):
    return \
        (is_native(arg_qual) or is_mutable(arg_qual) or is_const(arg_qual)) \
        and \
        forall(lambda q: q == 'v', arg_qual[1:])
    
def is_vector(arg_qual):
    return (len(arg_qual) > 1 and arg_qual[1] == 'v')

def is_vector2(arg_qual):
    return (is_vector(arg_qual) and len(arg_qual) > 2 and arg_qual[2] == 'v')

def is_vector3(arg_qual):
    return (is_vector2(arg_qual) and len(arg_qual) > 3 and arg_qual[3] == 'v')


# returns the jni type corresponding to the pseudo type signature
def arg_type_to_java((arg_qual, arg_type, arg_name)):
    check_arg_qual(arg_qual);
    if arg_type == "jobject":
        if (not is_native(arg_qual)) or is_vector(arg_qual):
            print("Error: native defined in implementation with qualifier: " + arg_qual)
            sys.exit(1)
        return "jobject"
    elif arg_type == "bool":
        if not is_native(arg_qual):
            print("Error: bool defined in implementation with qualifier: " + arg_qual)
            sys.exit(1)
        if is_vector(arg_qual):
            return "jbooleanArray"
        else:
            return "jboolean"
    elif arg_type == "int":
        if not is_native(arg_qual):
            print("Error: int defined in implementation with qualifier: " + arg_qual)
            sys.exit(1)
        if is_vector(arg_qual):
            return "jintArray"
        else:
            return "jint"
    elif arg_type == "string":
        if not is_native(arg_qual):
            print("Error: string defined in implementation with qualifier: " + arg_qual)
            sys.exit(1)
        if is_vector(arg_qual):
            return "jobjectArray"
        else:
            return "jstring"
    else:
        if is_vector(arg_qual):
            return "jobjectArray"
        else:
            return "jobject"

def print_unembed_arg(cpp_file, (arg_qual, arg_type, arg_name)):
    check_arg_qual(arg_qual);
    if arg_type == "jobject":
        ()
    elif arg_type == "bool":
        if is_vector3(arg_qual):
            cpp_file.write("    vector<vector<vector<bool> > > " + arg_name \
                               + "(toCppVVV(env, j" + arg_name + "));\n");
        elif is_vector2(arg_qual):
            cpp_file.write("    vector<vector<bool> > " + arg_name \
                               + "(toCppVV(env, j" + arg_name + "));\n");
        elif is_vector(arg_qual):
            cpp_file.write("    vector<bool> " + arg_name \
                               + "(toCppV(env, j" + arg_name + "));\n");
        else:
            cpp_file.write("    bool " + arg_name + "(j" + arg_name + ");\n");
    elif arg_type == "int":
        if is_vector3(arg_qual):
            cpp_file.write("    vector<vector<vector<int> > > " + arg_name \
                               + "(toCppVVV(env, j" + arg_name + "));\n");
        elif is_vector2(arg_qual):
            cpp_file.write("    vector<vector<int> > " + arg_name \
                               + "(toCppVV(env, j" + arg_name + "));\n");
        elif is_vector(arg_qual):
            cpp_file.write("    vector<int> " + arg_name \
                               + "(toCppV(env, j" + arg_name + "));\n");
        else:
            cpp_file.write("    int " + arg_name + "(j" + arg_name + ");\n");
    elif arg_type == "string":
        if is_vector3(arg_qual):
            cpp_file.write("    vector<vector<vector<string> > > " + arg_name \
                               + "(toCppVVV(env, j" + arg_name + "));\n");
        elif is_vector2(arg_qual):
            cpp_file.write("    vector<vector<string> > " + arg_name \
                               + "(toCppVV(env, j" + arg_name + "));\n");
        elif is_vector(arg_qual):
            cpp_file.write("    vector<string> " + arg_name \
                               + "(toCppV(env, j" + arg_name + "));\n");
        else:
            cpp_file.write("    string " + arg_name + "(toCpp(env, j" + arg_name + "));\n");
    else:
        if is_vector3(arg_qual):
            cpp_file.write("    vector<vector<vector<" + arg_type + "> > > " + arg_name \
                               + "(toCppVVV<" + arg_type + ">(env, j" + arg_name + "));\n");
        elif is_vector2(arg_qual):
            cpp_file.write("    vector<vector<" + arg_type + "> > " + arg_name \
                               + "(toCppVV<" + arg_type + ">(env, j" + arg_name + "));\n");
        elif is_vector(arg_qual):
            cpp_file.write("    vector<" + arg_type + "> " + arg_name \
                               + "(toCppV<" + arg_type + ">(env, j" + arg_name + "));\n");
        elif is_const(arg_qual):
            cpp_file.write("    const " + arg_type + "* " + arg_name \
                               + " = unembed_const<" + arg_type + ">(env, j" + arg_name + ");\n");
        else:
            cpp_file.write("    " + arg_type + "* " + arg_name \
                               + " = unembed_mut<" + arg_type + ">(env, j" + arg_name + ");\n");

def print_unembed_args(cpp_file, args):
    for arg in args:
        print_unembed_arg(cpp_file, arg)


# check hat declaration and definition signatures match
def match_signatures((decl_result, decl_args), (def_result, def_args, _)):
    if decl_result != def_result or len(decl_args) != len(def_args):
        return False
    for i in xrange(0, len(decl_args)):
        java_type = arg_type_to_java(def_args[i])
        #print java_type
        if decl_args[i] != java_type:
            return False
    return True

def print_header(cpp_file, includes):
    cpp_file.writelines(map(lambda name: "#include " + name + "\n", includes))

    cpp_file.writelines(
        [
            "#include \"JniUtils.h\"\n",
            "\n",
            "using namespace std;\n",
            "using namespace Java_cvc3_JniUtils;\n",
            "using namespace CVC3;\n",
            "\n"
            ])

def print_signature(cpp_file, name, result, args):
    arg_strings = ["JNIEnv* env", "jclass"]
    arg_strings.extend( \
        map(lambda (argQual, argType, argName): \
                arg_type_to_java((argQual, argType, argName)) \
                + " j" + argName, args))
    cpp_file.writelines([
            "JNIEXPORT " + result + " JNICALL " + name + "\n",
            "(" + ", ".join(arg_strings) + ")\n"])

def print_definition(cpp_file, name, (result, args, body)):
    cpp_file.writelines(["extern \"C\"\n"])
    print_signature(cpp_file, name, result, args)
    cpp_file.writelines([
        "{\n",
        "  try {\n"])
    print_unembed_args(cpp_file, args)
    cpp_file.writelines([
            "    " + "    ".join(body),
            "  } catch (const Exception& e) {\n",
            "    toJava(env, e);\n"])
    if result in [ "jobject", "jobjectArray", "jstring" ]:
        cpp_file.writelines(["    return NULL;\n"])
    elif result == "jboolean":
        cpp_file.writelines(["    return false;\n"])
    elif result == "jint":
        cpp_file.writelines(["    return -1;\n"])
    elif result <> "void":
        print("BUG: return type " + result + " is not handled in print_definition")
        sys.exit(1)
    cpp_file.writelines(["  };\n",
					     "}\n\n"])

def print_cpp(cpp_name, declarations, definitions, includes):
    try:
        cpp_file = open(cpp_name, 'w')

        print_header(cpp_file, includes)

        #names = declarations.keys()
        #names.sort()
        for name in declarations[0]:
            if not definitions.has_key(name):
                #continue
                print("Error: " + name + " is declared in header" \
                          + " but not defined in implementation.")
                sys.exit(1)

            declaration = declarations[1][name]
            definition = definitions[name]
            definitions.pop(name)
            if not match_signatures(declaration, definition):
                print("Error: signature for " + name \
                      + " in definition and implementation do not match:")
                print declaration
                print (definition[0], definition[1])
                sys.exit(1)

            print_definition(cpp_file, name, definition)

        if not len(definitions) == 0:
            print("Error: found definitions in implementation" \
                      " without declaration in header file:")
            print definitions
            sys.exit(1)
            
    
    except IOError, (error_nr, error_string):
        print ("Couldn't open " + cpp_name + ": " + error_string)
        sys.exit(0)


### header file function declarations

# header file function declaration:
# - name: function name
# - result: result type
# - args: list of argument types, except for the first two (JNIEnv*, jclass)
def register_declaration(declarations, name, result, args):
    assert(not declarations[1].has_key(name));
    declarations[0].append(name)
    declarations[1][name] = (result, args)

# extract function signatures from generated JNI header file
def read_header(header_name):
    # 0.: names of declared functions in same order as in input
    # 1.: map from names to signature
    declarations = ([], {})
    try:
        header_file = open(header_name)

        line = header_file.readline()
        while (line):
            # look for start of signature
            # declaration will look like:
            # JNIEXPORT <result> JNICALL <name> (JNIENV *env, jclass, jobject);
            # with an optional linebreak before the parameter list, and
            # perhaps missing the "env"
            if re.search("^JNIEXPORT", line):
                # extract name and return type
                elements = re.sub('[,();]+',' ',line).split(); 
                assert(elements[0] == "JNIEXPORT");
                assert(elements[2] == "JNICALL");
                name = elements[3]
                result = elements[1] 

                # If there are no more elements on this line,
                # read and tokenize the next line
                if len(elements) > 4:
                    elements = elements[4:]
                else:
                    line = header_file.readline ()
                    elements = re.sub('[,();]+',' ',line).split(); 
                    
                # extract argument types
                assert(elements[0] == "JNIEnv");
                assert(elements[1] == "*" or elements[1] == "*env");
                assert(elements[2] == "jclass")
                args = elements[3:]

                register_declaration(declarations, name, result, args)

            line = header_file.readline ()

        header_file.close()


    except IOError, (error_nr, error_string):
        print ("Couldn't open " + header_name + ": " + error_string)
        sys.exit(0)

    return declarations
    



# function definitions:

# cpp file function definition:
# - name: function name
# - result: result type
# - args: list of pairs of argument types and argument names,
#   except for the first two (JNIEnv*, jclass)
def register_definition(definitions, name, result, args, body):
    if definitions.has_key(name):
        print("Error: redefinition of " + name + " in implementation.")
        sys.exit(1)

    definitions[name] = (result, args, body)
    #print_definition(name, declarations[name])

# extract function definition from implementation file
def read_impl(impl_name):
    definitions = {}
    includes = []
    try:
        impl_file = open(impl_name)

        line = impl_file.readline()
        while (line):
            # look for include
            if re.search("^INCLUDE:", line):
                elements = line.split();
                assert(len(elements) == 2);
                assert(elements[0] == "INCLUDE:")
                includes.append(elements[1])
                line = impl_file.readline()

            #print line
            # look for start of definition
            elif re.search("^DEFINITION:", line):
                #print line,
                # get name
                elements = line.split();
                if not (len(elements) == 2):
                    print("Error: misformed signature: " + line)
                    sys.exit(1)

                assert(elements[0] == "DEFINITION:")
                name = elements[1]

                # get signature
                line = impl_file.readline ()
                elements = line.split();
                assert(len(elements) > 0);
                if not (len(elements) % 3 == 1):
                    print("Error: misformed signature for: " + name)
                    print(line)
                    sys.exit(1)
                result = elements.pop(0)
                args = []
                while len(elements) > 0:
                    argQual = elements.pop(0)
                    argType = elements.pop(0)
                    argName = elements.pop(0)
                    args.append((argQual, argType, argName))

                # get body
                body = []
                line = impl_file.readline ()
                while line and not re.search("^DEFINITION:", line):
                    body.append(line)
                    line = impl_file.readline()

                while body and body[len(body) - 1] == "\n":
                    body.pop(len(body) - 1)
                assert(len(body) > 0)

                register_definition(definitions, name, result, args, body)

            else:
                line = impl_file.readline()

        impl_file.close()

    except IOError, (error_nr, error_string):
        print ("Couldn't open " + impl_name + ": " + error_string)
        sys.exit(0)

    return definitions, includes


# read name of input file
if (len(sys.argv) != 4):
    print("Expected path to header, implementation, and target file.")
    print("")
    print("./create_impl.py <H_FILE> <IMPL_FILE> <CPP_FILE>")

    sys.exit(0)

else:
    #print(sys.argv)
    header_name = sys.argv[1]
    impl_name = sys.argv[2]
    cpp_file = sys.argv[3]

    # extract information from header
    declarations = read_header(header_name)
    #print declarations
    
    # extract information from template
    definitions, includes = read_impl(impl_name)
    #print definitions
    
    # create implementation
    print_cpp(cpp_file, declarations, definitions, includes)
