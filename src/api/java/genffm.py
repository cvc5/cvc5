#!/usr/bin/env python
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##
"""
Generate io/github/cvc5/CApi.java, the raw bindings of the cvc5 C API for the
Java Foreign Function & Memory API, from the C API headers.

For every function declared with CVC5_EXPORT, CApi.java gets a static method
of the same name that calls the C function through a downcall method handle,
created on first use. Handles and other pointers are passed as Java longs.
After the call, the method checks the C API's thread-local error state and
turns an error into a Java exception (see Native.checkError()).
"""

import argparse
import os
import re
import sys

# Functions that query or modify the error state themselves.
NO_ERROR_CHECK = {
    "cvc5_has_error",
    "cvc5_get_error_message",
    "cvc5_get_error_kind",
    "cvc5_reset_error",
    "cvc5_set_callback_error",
}

# Trivially short functions that never call back into Java.
CRITICAL = {"cvc5_has_error", "cvc5_get_error_kind"}

JAVA_KEYWORDS = {
    "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
    "class", "const", "continue", "default", "do", "double", "else", "enum",
    "extends", "final", "finally", "float", "for", "goto", "if", "implements",
    "import", "instanceof", "int", "interface", "long", "native", "new",
    "package", "private", "protected", "public", "return", "short", "static",
    "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
    "transient", "try", "void", "volatile", "while", "var", "record", "yield",
}

# (Java type, value layout) of C scalar types.
SCALARS = {
    "bool": ("boolean", "JAVA_BOOLEAN"),
    "int": ("int", "JAVA_INT"),
    "int32_t": ("int", "JAVA_INT"),
    "uint32_t": ("int", "JAVA_INT"),
    "int64_t": ("long", "JAVA_LONG"),
    "uint64_t": ("long", "JAVA_LONG"),
    "size_t": ("long", "JAVA_LONG"),
    "double": ("double", "JAVA_DOUBLE"),
}
POINTER = ("long", "JAVA_LONG")


def strip_comments(src):
    src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
    return re.sub(r"//[^\n]*", " ", src)


def split_params(params):
    depth, cur, out = 0, "", []
    for ch in params:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [p.strip() for p in out if p.strip() not in ("", "void")]


class CType:
    """Maps a C type to a Java type and a value layout."""

    def __init__(self, handles, enums):
        self.handles = handles
        self.enums = enums

    def map(self, ctype):
        t = re.sub(r"\bconst\b|\bstruct\b", " ", ctype)
        if "*" in t or "[" in t or "(" in t:
            return POINTER
        t = t.strip()
        if t in SCALARS:
            return SCALARS[t]
        if t in self.handles:
            return POINTER
        if t in self.enums:
            return ("int", "JAVA_INT")
        raise ValueError("unsupported C type: " + ctype)


def parse_param(param):
    """Return (C type, name or None) of a parameter declaration."""
    if "(" in param:  # function pointer
        m = re.search(r"\(\s*\*\s*(\w+)\s*\)", param)
        return param, m.group(1) if m else None
    array = param.endswith("[]")
    p = param[:-2].strip() if array else param
    m = re.match(r"(.*?[\s\*])(\w+)$", p)
    if m and m.group(1).strip() not in ("", "const", "struct"):
        ctype, name = m.group(1).strip(), m.group(2)
    else:
        ctype, name = p, None
    return ctype + ("[]" if array else ""), name


def parse_header(path, functions, handles, enums):
    src = strip_comments(open(path).read())
    src = re.sub(r"__attribute__\s*\(\(.*?\)\)\s*(?=[\w;,)])", " ", src,
                 flags=re.S)
    for m in re.finditer(r"typedef\s+struct\s+\w+\s*\*\s*(\w+)\s*;", src):
        handles.add(m.group(1))
    for m in re.finditer(r"typedef\s+enum\s*\{[^}]*\}\s*(\w+)\s*;", src):
        enums.add(m.group(1))
    for m in re.finditer(r"CVC5_EXPORT\s+([^;{]*?\))\s*;", src, flags=re.S):
        decl = " ".join(m.group(1).split())
        fm = re.match(r"(.*?)\b(cvc5_\w+)\s*\((.*)\)$", decl)
        if not fm:
            raise ValueError("cannot parse declaration: " + decl)
        ret, name, params = fm.groups()
        functions.append((ret.strip(), name, split_params(params), decl))


def collect_enums(include_dir, enums):
    # Enums shared with the C++ API are declared as `enum ENUM(Name)`.
    for root, _, files in os.walk(include_dir):
        for f in files:
            if f.endswith(".h"):
                src = open(os.path.join(root, f)).read()
                for m in re.finditer(r"enum\s+ENUM\((\w+)\)", src):
                    enums.add("Cvc5" + m.group(1))


def generate(functions, ctypes):
    out = []
    w = out.append
    w("/" + "*" * 78)
    w(" * This file is part of the cvc5 project.")
    w(" *")
    w(" * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS")
    w(" * in the top-level source directory and their institutional affiliations.")
    w(" * All rights reserved.  See the file COPYING in the top-level source")
    w(" * directory for licensing information.")
    w(" * " + "*" * 76)
    w(" *")
    w(" * Generated by src/api/java/genffm.py from the cvc5 C API headers.")
    w(" * Do not edit.")
    w(" */")
    w("")
    w("package io.github.cvc5;")
    w("")
    w("import static java.lang.foreign.ValueLayout.*;")
    w("")
    w("import java.lang.foreign.FunctionDescriptor;")
    w("import java.lang.foreign.Linker;")
    w("import java.lang.invoke.MethodHandle;")
    w("")
    w("/**")
    w(" * Raw bindings of the cvc5 C API.")
    w(" *")
    w(" * <p>Each method calls the C function of the same name. Handles and other")
    w(" * pointers are passed as {@code long}s. After the call, the C API's error")
    w(" * state is checked, and an error is raised as a Java exception, see")
    w(" * {@link Native#checkError()}.</p>")
    w(" */")
    w("final class CApi")
    w("{")
    w("  private CApi() {}")
    for ret, name, params, decl in functions:
        if "wchar_t" in decl:
            continue  # deprecated; the char32_t variants are used instead
        jret, lret = (None, None) if ret == "void" else ctypes.map(ret)
        args = []
        for i, p in enumerate(params):
            ctype, pname = parse_param(p)
            jtype, layout = ctypes.map(ctype)
            pname = pname or "arg%d" % i
            if pname in JAVA_KEYWORDS:
                pname += "_"
            args.append((jtype, layout, pname))
        layouts = ", ".join(a[1] for a in args)
        if jret is None:
            fd = "FunctionDescriptor.ofVoid(%s)" % layouts
        else:
            fd = "FunctionDescriptor.of(%s)" % ", ".join(
                [lret] + [a[1] for a in args])
        opts = ", Linker.Option.critical(false)" if name in CRITICAL else ""
        holder = "H_" + name
        sig = ", ".join("%s %s" % (a[0], a[2]) for a in args)
        call = ", ".join(a[2] for a in args)
        w("")
        w("  private static final class %s" % holder)
        w("  {")
        w("    static final MethodHandle MH = Native.downcall(\"%s\", %s%s);" %
          (name, fd, opts))
        w("  }")
        w("")
        w("  /** {@code %s} */" % decl.replace("*/", "* /"))
        w("  static %s %s(%s)" % (jret or "void", name, sig))
        w("  {")
        invoke = "%s.MH.invokeExact(%s)" % (holder, call)
        check = name not in NO_ERROR_CHECK
        if jret is None:
            w("    try")
            w("    {")
            w("      %s;" % invoke)
            w("    }")
            w("    catch (Throwable ex__)")
            w("    {")
            w("      throw Native.unexpected(ex__);")
            w("    }")
            if check:
                w("    Native.checkError();")
        else:
            w("    %s res__;" % jret)
            w("    try")
            w("    {")
            w("      res__ = (%s) %s;" % (jret, invoke))
            w("    }")
            w("    catch (Throwable ex__)")
            w("    {")
            w("      throw Native.unexpected(ex__);")
            w("    }")
            if check:
                rtype = re.sub(r"\bconst\b", " ", ret).strip()
                if rtype in ctypes.handles:
                    # Handles are NULL on error, so the error state only needs
                    # to be checked for NULL (which may also be a null object).
                    w("    if (res__ == 0)")
                    w("    {")
                    w("      Native.checkError();")
                    w("    }")
                else:
                    w("    Native.checkError();")
            w("    return res__;")
        w("  }")
    w("}")
    return "\n".join(out) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-dir", required=True,
                        help="the include directory of cvc5 (containing cvc5/c)")
    parser.add_argument("--java-api-path", required=True,
                        help="the output directory (containing io/github/cvc5)")
    args = parser.parse_args()
    functions, handles, enums = [], set(), set()
    collect_enums(args.include_dir, enums)
    for h in ("cvc5.h", "cvc5_parser.h"):
        parse_header(os.path.join(args.include_dir, "cvc5", "c", h), functions,
                     handles, enums)
    out_dir = os.path.join(args.java_api_path, "io", "github", "cvc5")
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, "CApi.java")
    code = generate(functions, CType(handles, enums))
    with open(out, "w") as f:
        f.write(code)


if __name__ == "__main__":
    sys.exit(main())
