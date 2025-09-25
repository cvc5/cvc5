###############################################################################
# Top contributors (to current version):
#   José Neto
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Utility class for mk*.py scripts.
#
##
import os

class TheoryValidator:
    def __init__(self):
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

        self.validated_theories = []
        self.src_directory = os.path.dirname(os.path.dirname(__file__))
    
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
        support_structs = ["type", "cardinality", "well-founded", "typerule", "construle", "enumerator"]
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
        if "cardinality" in kind and kind_type != "sort":
            self.validate_cardinality(filename, kind["cardinality"])
        
        if "well-founded" in kind:
            self.validate_well_founded(filename, kind["well-founded"])
        
        if "enumerator" in kind:
            self.validate_enumerator(filename, kind["enumerator"])

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
        required_fields = ["class", "header"]
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
        
        if theory_id in self.validated_theories:
            print(f"{filename}: error: \"{theory_id}\" theory redefined")
            exit(1)
        
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
        
        self.validated_theories.append(theory_id)
