import argparse
import sys
import os
from datetime import date

try:
    import tomllib
except ImportError:
    import tomli as tomllib

class CodeGenerator:
    def __init__(self, type_checker_template, type_checker_template_output, input_command):
        self.typerules             = ""
        self.pre_typerules         = ""
        self.const_rules           = ""
        self.type_checker_includes = ""
        self.template_data         = ""
        self.input_command         = input_command
        
        current_year               = date.today().year
        self.copyright             = f"2010-{current_year}"
        
        self.copyright_replacement_pattern          = b'${copyright}'
        self.generation_command_replacement_pattern = b'${generation_command}'
        self.template_file_path_replacement_pattern = b'${template_file_path}'
        self.typerules_replacement_pattern          = b'${typerules}'
        self.pre_typerules_replacement_pattern      = b'${pretyperules}'
        self.const_rules_replacement_pattern        = b'${construles}'
        self.typechecker_header_replacement_pattern = b'${typechecker_includes}'
        
        self.file_header                  = f"""/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) {self.copyright} by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This file was automatically generated by:
 *
 *     {self.input_command}
 *
 * for the cvc5 project.
 */
 
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */

/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */
/* THIS FILE IS AUTOMATICALLY GENERATED, DO NOT EDIT ! */

/* Edit the template file instead:                     */
/* {type_checker_template} */\n
""".encode('ascii')
        self.type_checker_template        = type_checker_template
        self.type_checker_template_output = type_checker_template_output
        
    
    def read_template_data(self):
        with open(self.type_checker_template, "rb") as f:
            self.template_data = f.read()
    
    def generate_file_header(self):
        self.fill_template(self.template_file_path_replacement_pattern, self.type_checker_template )

    def generate_code_for_typerules(self, input_kinds):
        for input_kind in input_kinds:
            if "typerule" not in input_kind:
                continue

            input_kind_type = input_kind["type"]
            input_typerule_name = input_kind["K1"] if input_kind_type == 'parameterized' else input_kind["name"]
            input_typerule_type_checker_class = input_kind["typerule"]["type_checker_class"]

            self.typerules = f"""{self.typerules}
    case Kind::{input_typerule_name}:
        typeNode = {input_typerule_type_checker_class}::computeType(nodeManager, n, check, errOut);
        break;
            """
            
            self.pre_typerules = f"""{self.pre_typerules}
    case Kind::{input_typerule_name}:
        typeNode = {input_typerule_type_checker_class}::preComputeType(nodeManager, n);
        break;
            """

    def generate_code_for_type_checker_includes(self, type_checker_include):
        self.type_checker_includes = f"{self.type_checker_includes}\n#include \"{type_checker_include}\""
    
    def generate_code_for_const_rules(self, input_kinds):
        for input_kind in input_kinds:
            if 'construle' not in input_kind:
                continue
            
            input_kind_type = input_kind["type"]
            input_const_rule_name = input_kind["K1"] if input_kind_type == 'parameterized' else input_kind["name"]
            input_const_rule_checker_class = input_kind["construle"]["type_checker_class"]

            self.const_rules = f"""{self.const_rules}
    case Kind::{input_const_rule_name}:
        return {input_const_rule_checker_class}::computeIsConst(nodeManager, n);
            """

    def fill_type_checker_includes_template_data(self):
        self.fill_template(self.typechecker_header_replacement_pattern, self.type_checker_includes)

    def fill_typerules_template_data(self):
        self.fill_template(self.typerules_replacement_pattern, self.typerules)
        self.fill_template(self.pre_typerules_replacement_pattern, self.pre_typerules)

    def fill_const_rules_template_data(self):
        self.fill_template(self.const_rules_replacement_pattern, self.const_rules)
    
    def fill_template(self, target_pattern, replacement_string):
        self.template_data = self.template_data.replace(target_pattern, str.encode(replacement_string))
    
    def write_output_data(self):
        with open(self.type_checker_template_output, 'wb') as f:
            f.write(self.file_header)
            f.write(self.template_data)

class TheoryValidator:
    def __init__(self):
        self.seen_theory_builtin = False
        self.VALID_PROPERTIES = [
            "finite", 
            "stable-infinite", 
            "polite", 
            "parametric", 
            "check", 
            "propagate", 
            "ppStaticLearn", 
            "notifyRestart", 
            "presolve", 
            "postsolve"
        ]

        self.src_directory = os.path.dirname(os.getcwd())
    
    def validate_header(self, filename, header):
        path_header = os.path.join(self.src_directory, header)
        if not os.path.exists(path_header):
            print(f"{filename}: error: Cannot find file {path_header}")
            exit(1)

    def check_required_fields(self, filename, struct, input_fields, required_fields):
        for required_field in required_fields:
            if required_field not in input_fields:
                print(f"{filename}: error: {struct} does not contain required field '{required_field}'")
                exit(1)
    
    def check_not_allowed_fields(self, filename, struct, input_fields, allowed_fields):
        support_structs = ["type", "cardinality", "well-founded", "typerule", "construle"]
        for input_field in input_fields:
            if input_field not in support_structs and input_field not in allowed_fields:
                print(f"{filename}: error: {struct} contains a not allowed field '{input_field}'")
                exit(1)

    def validate_rewriter(self, filename, kinds):
        rewriter = kinds.get("rewriter")
        required_fields = ["class", "header"]
        if not rewriter:
            print(f"{filename}: error: theory not defined")
            exit(1)
        
        self.check_required_fields(filename, "rewriter", rewriter, required_fields)
        self.check_not_allowed_fields(filename, "rewriter", rewriter, required_fields)
        self.validate_header(filename, rewriter["header"])
        
        # if "header" not in rewriter:
        #     print(f"{filename}: error: rewriter does not contain required field 'header'")
        #     exit(1)

    def validate_typerule(self, filename, typerule):
        required_fields = ["type_checker_class"]
        optional_fields = []

        self.check_required_fields(filename, "typerule", typerule, required_fields)
        self.check_not_allowed_fields(filename, "typerule", typerule, required_fields)
    
    def validate_construle(self, filename, construle):
        required_fields = ["type_checker_class"]
        optional_fields = []

        self.check_required_fields(filename, "construle", construle, required_fields)
        self.check_not_allowed_fields(filename, "construle", construle, required_fields)
    
    def validate_sort(self, filename, sort):
        required_fields = ["name", "cardinality", "well_founded"]
        optional_fields = ["comment"]

        self.check_required_fields(filename, "sort", sort, required_fields)

        name = sort["name"]
        well_founded = sort["well_founded"]
        # [well-founded ground-term header | not-well-founded]
        if well_founded:
            if "ground-term" not in sort:
                print(f"{filename}: error: missing 'ground-term' property at 'well-founded' sort {name}")
                exit(1)
            if "header" not in sort:
                print(f"{filename}: error: missing 'header' property at 'well-founded' sort {name}")
                exit(1)
            required_fields += ["ground-term", "header"]

        self.check_extra_fields(filename, sort, "sort")
        self.check_not_allowed_fields(filename, "sort", sort, required_fields + optional_fields)

    def validate_cardinality(self, filename, cardinality):
        required_fields = ["computer"]
        optional_fields = ["header"]

        self.check_required_fields(filename, "cardinality", cardinality, required_fields)
        self.check_not_allowed_fields(filename, "cardinality", cardinality, required_fields + optional_fields)

        if "header" in cardinality:
            self.validate_header(filename, cardinality["header"])

    def check_extra_fields(self, filename, kind, kind_type = "kind"):
        if "typerule" in kind:
            self.validate_typerule(filename, kind["typerule"])
        
        if "construle" in kind:
            self.validate_construle(filename, kind["construle"])
        
        if "cardinality" in kind and kind_type != "sort":
            self.validate_cardinality(filename, kind["cardinality"])
        
        if "well-founded" in kind:
            self.validate_well_founded(filename, kind["well-founded"])

    def validate_operator(self, filename, operator):
        required_fields = ["name", "children"]
        optional_fields = ["comment"]

        self.check_required_fields(filename, "operator", operator, required_fields)
        self.check_extra_fields(filename, operator)
        self.check_not_allowed_fields(filename, "operator", operator, required_fields + optional_fields)
    
    def validate_nullary_operator(self, filename, nullary_operator):
        required_fields = ["name"]
        optional_fields = ["comment"]

        self.check_required_fields(filename, "nullaryoperator", nullary_operator, required_fields)
        self.check_extra_fields(filename, nullary_operator)
        self.check_not_allowed_fields(filename, "nullaryoperator", nullary_operator, required_fields + optional_fields)

    def validate_variable(self, filename, variable):
        required_fields = ["name"]
        optional_fields = ["comment"]
        
        self.check_required_fields(filename, "variable", variable, required_fields)
        self.check_extra_fields(filename, variable)
        self.check_not_allowed_fields(filename, "variable", variable, required_fields + optional_fields)
    
    def validate_parameterized(self, filename, parameterized):
        required_fields = ["K1", "K2", "children"]
        optional_fields = ["comment"]
        
        self.check_required_fields(filename, "parameterized", parameterized, required_fields)
        self.check_extra_fields(filename, parameterized)
        self.check_not_allowed_fields(filename, "parameterized", parameterized, required_fields + optional_fields)
    
    def validate_constant(self, filename, constant):
        required_fields = ["name", "class_key", "cpp_type", "hasher", "header"]
        optional_fields = ["comment"]
        
        self.check_required_fields(filename, "constant", constant, required_fields)
        self.check_extra_fields(filename, constant)
        self.check_not_allowed_fields(filename, "constant", constant, required_fields + optional_fields)

    def validate_well_founded(self, filename, well_founded):
        required_fields = ["wellfoundedness-computer", "ground-term-computer"]
        optional_fields = ["header"]
        
        self.check_required_fields(filename, "well-founded", well_founded, required_fields)
        if "header" in well_founded:
            self.validate_header(filename, well_founded["header"])
        self.check_not_allowed_fields(filename, "well-founded", well_founded, required_fields + optional_fields)

    def validate_enumerator(self, filename, enumerator):
        required_fields = ["name", "class", "header"]
        optional_fields = ["comment"]
        
        self.check_required_fields(filename, "enumerator", enumerator, required_fields)
        self.check_not_allowed_fields(filename, "enumerator", enumerator, required_fields + optional_fields)
    
    def validate_kind(self, filename, kind):
        if "type" not in kind:
            print(f"{filename}: error: kind defined without a type")
            print(kind)
            exit(1)

        kind_type = kind["type"]

        if kind_type == "constant":
            self.validate_constant(filename, kind)
        elif kind_type == "enumerator":
            self.validate_enumerator(filename, kind)
        elif kind_type == "nullaryoperator":
            self.validate_nullary_operator(filename, kind)
        elif kind_type == "operator":
            self.validate_operator(filename, kind)
        elif kind_type == "parameterized":
            self.validate_parameterized(filename, kind)
        elif kind_type == "sort":
            self.validate_sort(filename, kind)
        elif kind_type == "variable":
            self.validate_variable(filename, kind)
        else:
            print(f"{filename}: error: found kind with invalid type: {kind_type}")
            exit(1)

    def validate_theory_properties(self, filename, input_properties):
        for input_property in input_properties:
            if input_property not in self.VALID_PROPERTIES:
                print(f"{filename}: error: theory has an invalid property: {input_property}")
                exit(1)

    def validate_theory(self, filename, input_theory):
        theory = input_theory.get("theory")

        if not theory:
            print(f"{filename}: error: theory not defined")
            exit(1)

        theory_id = theory.get("id")
        theory_class = theory.get("base_class")
        theory_header = theory.get("base_class_header")
        typechecker_header = theory.get("typechecker_header")
        properties = theory.get("properties", [])

        self.validate_theory_properties(filename, properties)

        if not theory_id:
            print(f"{filename}: error: theory id not defined")
            exit(1)
        
        if theory_id == 'THEORY_BUILTIN':
            if self.seen_theory_builtin:
                print(f"{filename}: error: \"builtin\" theory redefined")
                exit(1)
            self.seen_theory_builtin = True
        
        if not theory_class or not theory_header or not typechecker_header:
            print(f"{filename}: error: \"theory\" directive missing class or header argument")
            exit(1)

        self.validate_header(filename, theory_header)
        self.validate_header(filename, typechecker_header)

        if not theory_class.startswith("::"):
            print(f"{filename}: warning: theory class `{theory_class}` isn't fully-qualified (e.g., ::cvc5::internal::theory::foo)")
        
        if not theory_class.startswith("::cvc5::internal::theory::"):
            print(f"{filename}: warning: theory class not under ::cvc5::internal::theory namespace")
        
        self.validate_rewriter(filename, input_theory)

        kinds = input_theory["kinds"]
        for input_kind in kinds:
            self.validate_kind(filename, input_kind)


def mkexpr_main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--kinds', nargs='+', help='List of input TOML files', required=True, type=str)
    parser.add_argument('--template', help='Path to the template', required=True, type=str)
    parser.add_argument('--output', help='Output path', required=True)

    args = parser.parse_args()
    type_checker_template_path = args.template
    output_path = args.output
    kinds_files = args.kinds

    input_command = ' '.join(sys.argv)

    cg = CodeGenerator(type_checker_template_path, output_path, input_command)
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
                tv.validate_theory(filename, kinds_data)

                input_kinds = kinds_data.get("kinds", [])
                cg.generate_code_for_typerules(input_kinds)
                
                type_checker_include = kinds_data["theory"]["typechecker_header"]
                cg.generate_code_for_type_checker_includes(type_checker_include)
                
                cg.generate_code_for_const_rules(input_kinds)
        except Exception as e:
            print(f"Could not parse file {filename}")
            print(e)
            exit(1)

    cg.fill_typerules_template_data()
    cg.fill_type_checker_includes_template_data()
    cg.fill_const_rules_template_data()
    cg.write_output_data()

if __name__ == "__main__":
    mkexpr_main()
    exit(0)