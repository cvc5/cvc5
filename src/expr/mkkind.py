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
# Generate the kind.[h,cpp] and type_properties.[h,cpp] implementations.
#
##
import argparse
import sys
import os
from datetime import date
from theory_validator import TheoryValidator

try:
    import tomllib
except ImportError:
    import tomli as tomllib


class CodeGenerator:

    def __init__(self, template, output_file, command):
        self.type_groundterms = ""
        self.type_constant_groundterms = ""
        self.type_wellfoundednesses = ""
        self.type_constant_wellfoundednesses = ""
        self.type_cardinalities = ""
        self.type_constant_cardinalities = ""
        self.type_properties_includes = ""
        self.type_constant_to_theory_id = ""
        self.type_constant_descriptions = ""
        self.kind_to_theory_id = ""
        self.kind_printers = ""
        self.kinds_enum_header = ""
        self.type_constant_list = ""
        self.template_data = ""
        self.command = command

        current_year = date.today().year
        self.copyright = f"2010-{current_year}"

        self.copyright_replacement_pattern = b'${copyright}'
        self.generation_command_replacement_pattern = b'${generation_command}'
        self.template_file_path_replacement_pattern = b'${template_file_path}'
        self.kinds_enum_header_replacement_pattern = b'${kind_decls}'
        self.type_constant_list_replacement_pattern = b'${type_constant_list}'
        self.kind_printers_replacement_pattern = b'${kind_printers}'
        self.kind_to_theory_id_replacement_pattern = b'${kind_to_theory_id}'
        self.type_constant_descriptions_replacement_pattern = b'${type_constant_descriptions}'
        self.type_constant_to_theory_id_replacement_pattern = b'${type_constant_to_theory_id}'
        self.type_properties_includes_replacement_pattern = b'${type_properties_includes}'
        self.type_constant_cardinalities_replacement_pattern = b'${type_constant_cardinalities}'
        self.type_cardinalities_replacement_pattern = b'${type_cardinalities}'
        self.type_constant_wellfoundednesses_replacement_pattern = b'${type_constant_wellfoundednesses}'
        self.type_wellfoundednesses_replacement_pattern = b'${type_wellfoundednesses}'
        self.type_constant_groundterms_replacement_pattern = b'${type_constant_groundterms}'
        self.type_groundterms_replacement_pattern = b'${type_groundterms}'

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

    def add_header_comment(self, kinds_file_base_name):
        self.kinds_enum_header += f"  /* from {kinds_file_base_name} */\n"
        self.kind_printers += f"    /* from {kinds_file_base_name} */\n"

    def add_header_linebreak(self):
        self.kinds_enum_header = f"{self.kinds_enum_header}\n"
        self.kind_printers = f"{self.kind_printers}\n"

    def register_kind(self,
                      kinds,
                      theory_id,
                      filename,
                      name_property="name",
                      comment_property="comment"):

        general_kind_case_types = [
            "variable", "operator", "parameterized", "constant",
            "nullaryoperator"
        ]

        if not kinds:
            return

        for kind in kinds:
            kind_type = kind["type"]
            processed_name_property = "K1" if kind_type == "parameterized" else name_property
            kind_name = kind[processed_name_property]

            if kind_type in general_kind_case_types:
                kind_comment = kind.get(comment_property, "")
                self.register_kind_counter += 1

                self.kinds_enum_header += f"  {kind_name}, /**< {kind_comment} ({self.register_kind_counter}) */\n"
                self.kind_printers += f"    case Kind::{kind_name}: return \"{kind_name}\";\n"
                self.kind_to_theory_id += f"    case Kind::{kind_name}: return {theory_id};\n"
            elif kind_type == "sort":
                self.register_sort(kind, theory_id)

            if "cardinality" in kind and kind_type != "sort":
                self.register_cardinality(kind["cardinality"], kind_name)

            if "well-founded" in kind:
                self.register_wellfounded(kind["well-founded"], filename,
                                          kind_name)

    def register_wellfounded(self, wellfounded, filename, kind_name):
        name = kind_name
        computer = wellfounded["wellfoundedness-computer"]
        if isinstance(computer, bool):
            computer = "true" if computer else "false"

        computer = computer.replace('%TYPE%', 'typeNode')
        groundterm_computer = wellfounded.get("ground-term-computer")
        header = wellfounded.get("header")

        if header:
            self.type_properties_includes += f"#include \"{header}\"\n"

        # "false" is a special well-foundedness computer that doesn't
        # require an associated groundterm-computer; anything else does
        if computer != 'false':
            if not groundterm_computer:
                print(
                    f"{filename}: error: ground-term computer missing in command \"well-founded\""
                )
                exit(1)
        else:
            if groundterm_computer:
                print(
                    f"{filename}: error: ground-term computer specified for not-well-founded type"
                )
                exit(1)

        if groundterm_computer:
            groundterm_computer = groundterm_computer.replace(
                '%TYPE%', 'typeNode')
            self.type_groundterms += f"    case Kind::{name}: return {groundterm_computer};\n"
        else:
            self.type_groundterms += f"    case Kind::{name}: Unhandled() << typeNode;\n"

        self.type_wellfoundednesses += f"    case Kind::{name}: return {computer};\n"

    def register_cardinality(self, cardinality, kind_name):
        # cardinality K cardinality-computer [header]
        cardinality_name = kind_name
        cardinality_computer = cardinality["computer"].replace(
            '%TYPE%', 'typeNode')
        cardinality_header = cardinality.get("header")

        self.type_cardinalities += f"    case Kind::{cardinality_name}: return {cardinality_computer};\n"

        if cardinality_header:
            self.type_properties_includes += f"#include \"{cardinality_header}\"\n"

    def register_sort(self, sort, theory_id):
        # sort TYPE cardinality [well-founded ground-term header | not-well-founded] ["comment"]
        sort_name = sort["name"]
        sort_cardinality = sort["cardinality"]
        sort_well_founded = sort["well_founded"]
        sort_comment = sort.get("comment", "")

        sort_well_founded_string = "true" if sort_well_founded else "false"
        self.type_constant_list += f"  {sort_name}, /**< {sort_comment}*/\n"
        self.type_constant_wellfoundednesses += f"    case {sort_name}: return {sort_well_founded_string};\n"
        self.type_constant_cardinalities += f"    case {sort_name}: return Cardinality({sort_cardinality});\n"

        if sort_well_founded:
            sort_ground_term = sort["ground-term"]
            self.type_constant_groundterms += f"    case {sort_name}: return {sort_ground_term};\n"
            sort_header = sort.get("header")
            if sort_header:
                self.type_properties_includes += f"#include \"{sort_header}\"\n"
        else:
            self.type_constant_groundterms += f"    case {sort_name}: Unhandled() << tc;\n"

        self.type_constant_descriptions += f"    case {sort_name}: return \"{sort_comment}\";\n"
        self.type_constant_to_theory_id += f"    case {sort_name}: return {theory_id};\n"

    def fill_register_kind_template_data(self):
        self.fill_template(self.kinds_enum_header_replacement_pattern,
                           self.kinds_enum_header)
        self.fill_template(self.kind_printers_replacement_pattern,
                           self.kind_printers)
        self.fill_template(self.kind_to_theory_id_replacement_pattern,
                           self.kind_to_theory_id)

    def fill_register_sort_template_data(self):
        self.fill_template(self.type_constant_descriptions_replacement_pattern,
                           self.type_constant_descriptions)
        self.fill_template(self.type_constant_to_theory_id_replacement_pattern,
                           self.type_constant_to_theory_id)
        self.fill_template(
            self.type_constant_wellfoundednesses_replacement_pattern,
            self.type_constant_wellfoundednesses)
        self.fill_template(
            self.type_constant_cardinalities_replacement_pattern,
            self.type_constant_cardinalities)
        self.fill_template(self.type_constant_groundterms_replacement_pattern,
                           self.type_constant_groundterms)

    def fill_register_cardinality_template_data(self):
        self.fill_template(self.type_properties_includes_replacement_pattern,
                           self.type_properties_includes)
        self.fill_template(self.type_cardinalities_replacement_pattern,
                           self.type_cardinalities)

    def fill_register_wellfoundedness_template_data(self):
        self.fill_template(self.type_wellfoundednesses_replacement_pattern,
                           self.type_wellfoundednesses)
        self.fill_template(self.type_groundterms_replacement_pattern,
                           self.type_groundterms)

    def fill_constant_list_header_template_data(self):
        self.fill_template(self.type_constant_list_replacement_pattern,
                           self.type_constant_list)

    def fill_template(self, target_pattern, replacement_string):
        self.template_data = self.template_data.replace(
            target_pattern, str.encode(replacement_string))

    def write_output_data(self):
        with open(self.output_file, 'wb') as f:
            f.write(self.template_data)


def mkkind_main():
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

    input_command = ' '.join(sys.argv)

    cg = CodeGenerator(template_path, output_path, input_command)
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
                theory_id = kinds_data["theory"]["id"]

                cg.add_header_comment(file_basename)

                input_kinds = kinds_data["kinds"]
                cg.register_kind(input_kinds, theory_id, filename)

                cg.add_header_linebreak()

        except Exception as e:
            print(f"Could not parse file {filename}")
            print(e)
            exit(1)

    cg.fill_register_kind_template_data()
    cg.fill_constant_list_header_template_data()
    cg.fill_register_sort_template_data()
    cg.fill_register_cardinality_template_data()
    cg.fill_register_wellfoundedness_template_data()
    cg.write_output_data()


if __name__ == "__main__":
    mkkind_main()
    exit(0)
