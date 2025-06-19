###############################################################################
# Top contributors (to current version):
#   José Neto, Morgan Deters
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Generate the metakind.[h,cpp] and node_manager.[h,cpp] implementations.
#
##
import argparse
import os
import re
import sys
from datetime import date
from theory_validator import TheoryValidator

try:
    import tomllib
except ImportError:
    import tomli as tomllib


class CodeGenerator:

    def __init__(self, template, output_file, command):
        self.metakind_operatorKinds = ""
        self.metakind_ubchildren = ""
        self.metakind_lbchildren = ""
        self.metakind_constDeleters = ""
        self.metakind_constPrinters = ""
        self.metakind_compares = ""
        self.metakind_constHashes = ""
        self.metakind_kinds = ""
        self.metakind_constantMaps = ""
        self.metakind_includes = ""
        self.metakind_mkConst = ""
        self.metakind_mkConstDelete = ""
        self.metakind_fwd_decls = ""
        self.template_data = ""
        self.command = command

        current_year = date.today().year
        self.copyright = f"2010-{current_year}"

        self.copyright_replacement_pattern = b'${copyright}'
        self.generation_command_replacement_pattern = b'${generation_command}'
        self.template_file_path_replacement_pattern = b'${template_file_path}'
        self.metakind_fwd_decls_replacement_pattern = b'${metakind_fwd_decls}'
        self.metakind_mkConstDelete_replacement_pattern = b'${metakind_mkConstDelete}'
        self.metakind_mkConst_replacement_pattern = b'${metakind_mkConst}'
        self.metakind_includes_replacement_pattern = b'${metakind_includes}'
        self.metakind_constantMaps_replacement_pattern = b'${metakind_constantMaps}'
        self.metakind_kinds_replacement_pattern = b'${metakind_kinds}'
        self.metakind_constHashes_replacement_pattern = b'${metakind_constHashes}'
        self.metakind_compares_replacement_pattern = b'${metakind_compares}'
        self.metakind_constPrinters_replacement_pattern = b'${metakind_constPrinters}'
        self.metakind_constDeleters_replacement_pattern = b'${metakind_constDeleters}'
        self.metakind_lbchildren_replacement_pattern = b'${metakind_lbchildren}'
        self.metakind_ubchildren_replacement_pattern = b'${metakind_ubchildren}'
        self.metakind_operatorKinds_replacement_pattern = b'${metakind_operatorKinds}'

        self.payload_seen = []
        self.metakind_includes_array = []

        self.template = template
        self.output_file = output_file
        self.register_kind_counter = 0

    def read_template_data(self):
        with open(self.template, "rb") as f:
            self.template_data = f.read()

    def generate_file_header(self):
        self.fill_template(self.copyright_replacement_pattern, self.copyright)
        self.fill_template(self.generation_command_replacement_pattern,
                           self.command)
        self.fill_template(self.template_file_path_replacement_pattern,
                           self.template)

    def register_constant(self, constant, filename):
        name = constant["name"]
        constant_F = constant["class_key"]
        constant_T = constant["cpp_type"]
        class_name = constant_T
        hasher = constant["hasher"]
        header = constant["header"]
        comment = constant.get("comment")

        if not re.match(r'::.*', hasher):
            print(
                f"{filename}: warning: constant {name} hasher `{hasher}` isn't fully-qualified (e.g., ::cvc5::internal::RationalHashFunction)"
            )

        if class_name.endswith('+'):
            # Remove last character
            class_name = class_name[:-1]
            skip_const_map = True
        else:
            skip_const_map = False

        payload_seen = class_name in self.payload_seen
        if not payload_seen:
            self.payload_seen.append(class_name)

        if constant_F != "skip":
            self.metakind_fwd_decls += f"{constant_F} {class_name};\n"

        if header and f"#include \"{header}\"" not in self.metakind_includes_array:
            self.metakind_includes_array.append(f"#include \"{header}\"")
            self.metakind_includes += f"#include \"{header}\"\n"

        self.register_metakind("CONSTANT", name, 0, filename)

        # metakind_constantMaps
        if not payload_seen:
            self.metakind_constantMaps += f"""
// The reinterpret_cast of d_children to \"{class_name} const*\"
// flags a \"strict aliasing\" warning; it's okay, because we never access
// the embedded constant as a NodeValue* child, and never access an embedded
// NodeValue* child as a constant.
#pragma GCC diagnostic ignored \"-Wstrict-aliasing\"

template <>
{class_name} const& NodeValue::getConst< {class_name} >() const {{
  //AssertArgument(getKind() == ::cvc5::internal::Kind::{name}, *this,
  //               "Improper kind for getConst<{class_name}>()");
  // To support non-inlined CONSTANT-kinded NodeValues (those that are
  // "constructed" when initially checking them against the NodeManager
  // pool), we must check d_nchildren here.
  return d_nchildren == 0
    ? *reinterpret_cast<{class_name} const*>(d_children)
    : *reinterpret_cast<{class_name} const*>(d_children[0]);
}}

// re-enable the warning
#pragma GCC diagnostic warning \"-Wstrict-aliasing\"

"""

        if not skip_const_map:
            self.metakind_mkConst += f"""
template<>
Node NodeManager::mkConst<{class_name}>(const {class_name}& val)
{{
  return mkConstInternal<Node, {class_name}>(::cvc5::internal::Kind::{name}, val);
}}
"""
            self.metakind_mkConst += f"""
template<>
Node NodeManager::mkConst(Kind k, const {class_name}& val)
{{
  return mkConstInternal<Node, {class_name}>(k, val);
}}
"""
        elif not payload_seen:
            self.metakind_mkConstDelete += f"\ntemplate<>\nNode NodeManager::mkConst<{class_name}>(const {class_name}& val) = delete;\n"
            self.metakind_mkConst += f"""
template<>
Node NodeManager::mkConst(Kind k, const {class_name}& val)
{{
  return mkConstInternal<Node, {class_name}>(k, val);
}}
"""

        self.metakind_compares += f"""
    case Kind::{name}:
        return NodeValueConstCompare<Kind::{name}, {class_name}, pool>::compare(nv1, nv2);
"""

        self.metakind_constHashes += f"""
    case Kind::{name}:
        return {hasher}()(nv->getConst< {class_name} >());
        """

        self.metakind_constPrinters += f"""
    case Kind::{name}:
        out << nv->getConst< {class_name} >();
        break;
"""

        self.metakind_constDeleters += f"""
    case Kind::{name}:
        std::destroy_at(reinterpret_cast< {class_name}* >(nv->d_children));
        break;
"""

    def register_variable(self, variable, filename):
        name = variable["name"]
        comment = variable.get("comment")
        self.register_metakind("VARIABLE", name, 0, filename)

    def register_operator(self, operator, filename):
        name = operator["name"]
        children = operator["children"]
        self.register_metakind("OPERATOR", name, children, filename)

    def register_parameterized(self, parameterized, filename):
        K1 = parameterized["K1"]
        K2 = parameterized["K2"]
        children = parameterized["children"]
        self.register_metakind("PARAMETERIZED", K1, children, filename)

        if not re.match(r'\[.*\]', K2):
            self.metakind_operatorKinds += f"\n    case Kind::{K2}: return Kind::{K1};"

    def register_nullary_operator(self, nullary_operator, filename):
        name = nullary_operator["name"]
        self.register_metakind("NULLARY_OPERATOR", name, 0, filename)

    def register_metakind(self, mk, k, nc, filename):
        self.metakind_kinds += f"      metakind::{mk}, /* {k} */\n"

        nc = str(nc) if type(nc) is not str else nc
        if re.match(r'^[0-9][0-9]*$', nc):
            lb = int(nc)
            ub = int(nc)
        elif re.match(r'^[0-9][0-9]*:$', nc):
            lb = int(nc.split(':')[0])
            ub = "expr::NodeValue::MAX_CHILDREN"
        elif re.match(r'^[0-9][0-9]*:[0-9][0-9]*$', nc):
            lb, ub = map(int, nc.split(':'))
            if ub < lb:
                print(
                    f"{filename}: error in range `{nc}': LB < UB (in definition of {k})",
                    file=sys.stderr)
                exit(1)
        else:
            print(f"{filename}: can't parse range `{nc}' in definition of {k}",
                  file=sys.stderr)
            exit(1)

        self.metakind_lbchildren += f"\n      {lb}, /* {k} */"
        self.metakind_ubchildren += f"\n      {ub}, /* {k} */"

    def register_kinds(self, kinds, filename):
        self.metakind_kinds += f"\n      /* from {filename} */\n"
        self.metakind_operatorKinds += f"\n\n    /* from {filename} */"
        if not kinds:
            return

        for kind in kinds:
            kind_type = kind["type"]
            if kind_type == "constant":
                self.register_constant(kind, filename)
            elif kind_type == "variable":
                self.register_variable(kind, filename)
            elif kind_type == "operator":
                self.register_operator(kind, filename)
            elif kind_type == "parameterized":
                self.register_parameterized(kind, filename)
            elif kind_type == "nullaryoperator":
                self.register_nullary_operator(kind, filename)

    def add_header_template_data(self, theory, file_basename):
        theory_class = theory.get("base_class")
        self.metakind_includes += f"// #include \"theory/{file_basename}/{theory_class}\"\n"

    def fill_header_template_data(self):
        self.fill_template(self.metakind_includes_replacement_pattern,
                           self.metakind_includes)

    def fill_register_constant_template_data(self):
        self.fill_template(self.metakind_fwd_decls_replacement_pattern,
                           self.metakind_fwd_decls)
        self.fill_template(self.metakind_mkConst_replacement_pattern,
                           self.metakind_mkConst)
        self.fill_template(self.metakind_mkConstDelete_replacement_pattern,
                           self.metakind_mkConstDelete)
        self.fill_template(self.metakind_constantMaps_replacement_pattern,
                           self.metakind_constantMaps)
        self.fill_template(self.metakind_compares_replacement_pattern,
                           self.metakind_compares)
        self.fill_template(self.metakind_constHashes_replacement_pattern,
                           self.metakind_constHashes)
        self.fill_template(self.metakind_constPrinters_replacement_pattern,
                           self.metakind_constPrinters)
        self.fill_template(self.metakind_constDeleters_replacement_pattern,
                           self.metakind_constDeleters)

    def fill_register_metakinds_template_data(self):
        self.fill_template(self.metakind_kinds_replacement_pattern,
                           self.metakind_kinds)
        self.fill_template(self.metakind_lbchildren_replacement_pattern,
                           self.metakind_lbchildren)
        self.fill_template(self.metakind_ubchildren_replacement_pattern,
                           self.metakind_ubchildren)
        self.fill_template(self.metakind_operatorKinds_replacement_pattern,
                           self.metakind_operatorKinds)

    def fill_template(self, target_pattern, replacement_string):
        self.template_data = self.template_data.replace(
            target_pattern, str.encode(replacement_string))

    def write_output_data(self):
        with open(self.output_file, 'wb') as f:
            f.write(self.template_data)


def mkmetakind_main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--kinds',
                        nargs='+',
                        help='List of input TOML files',
                        required=True,
                        type=str)
    parser.add_argument('--template',
                        help='Path to the template',
                        required=True,
                        type=str)
    parser.add_argument('--output', help='Output path', required=True)

    args = parser.parse_args()
    template_path = args.template
    output_path = args.output
    kinds_files = args.kinds

    command = ' '.join(sys.argv)

    cg = CodeGenerator(template_path, output_path, command)
    cg.read_template_data()
    cg.generate_file_header()

    tv = TheoryValidator()

    # Check if given kinds files exist.
    for file in kinds_files:
        if not os.path.exists(file):
            exit(f"Kinds file '{file}' does not exist")

    # Parse and check toml files
    for filename in kinds_files:
        try:
            with open(filename, "rb") as f:
                kinds_data = tomllib.load(f)
                file_basename = filename.split('/')[-2]

                tv.validate_theory(filename, kinds_data)

                theory = kinds_data["theory"]
                cg.add_header_template_data(theory, file_basename)
                theory_id = kinds_data["theory"]["id"]

                kinds = kinds_data.get("kinds", [])
                cg.register_kinds(kinds, file_basename)

        except Exception as e:
            print(f"Could not parse file {filename}")
            print(e)
            exit(1)

    cg.fill_header_template_data()
    cg.fill_register_constant_template_data()
    cg.fill_register_metakinds_template_data()
    cg.write_output_data()


if __name__ == "__main__":
    mkmetakind_main()
    exit(0)
