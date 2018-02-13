#!/usr/bin/env python3

import json
import toml
import sys

# TODO: more checks for options, e.g., long options start with -- ...
# TODO: documentation generation
# TODO: long-options have --no- alternate if type is bool
# TODO: add error checking as done in mkoptions

MODULE_ATTR_REQ = ['id', 'name', 'header']
MODULE_ATTR_OPT = ['option', 'alias']
MODULE_ATTR_ALL = MODULE_ATTR_REQ + MODULE_ATTR_OPT

OPTION_ATTR_REQ = ['name', 'category', 'type']
OPTION_ATTR_OPT = [
   'help', 'smt_name', 'short', 'long', 'include', 'default', 'handler' ,
   'predicate', 'notify', 'read_only', 'link'
]
OPTION_ATTR_ALL = OPTION_ATTR_REQ + OPTION_ATTR_OPT

ALIAS_ATTR_REQ = ['name', 'category', 'link']
ALIAS_ATTR_OPT = ['help', 'short', 'long']
ALIAS_ATTR_ALL = ALIAS_ATTR_REQ + ALIAS_ATTR_OPT

TYPE_VALUES = ['common', 'expert', 'regular', 'undocumented']


class Module(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in MODULE_ATTR_ALL)
        for (k, v) in d.items():
            assert(k in self.__dict__)
            self.__dict__[k] = v

class Option(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in OPTION_ATTR_ALL)
        for (k, v) in d.items():
            assert(k in self.__dict__)
            self.__dict__[k] = v
        # TODO: initialize read_only if not in 'd'

class Alias(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in ALIAS_ATTR_ALL)
        for (k, v) in d.items():
            assert(k in self.__dict__)
            self.__dict__[k] = v


def die(msg):
    sys.exit(msg)


def check_attribs(req_attribs, valid_attribs, d, type):
    msg_for = ""
    if 'name' in d:
        msg_for = " for '{}'".format(d['name'])
    for k in req_attribs:
        if k not in d:
            die("required {} attribute '{}' not specified{}".format(
                type, k, msg_for))
    for k in d:
        if k not in valid_attribs:
            die("invalid {} attribute '{}' specified{}".format(
                type, k, msg_for))

def read_tpl(name):
    try:
        f = open(name, 'r')
    except IOError:
        return None
    else:
        # Escape { and } since we later use .format to add the generated code.
        # Further, strip ${ and }$ from placeholder variables in the template
        # file.
        with f:
            return f.read().replace('{', '{{').replace('}', '}}').\
                            replace('${', '').replace('}$', '')


def codegen_module(module):
    # <module.name>_options.h
    #
    # - #define __CVC4__OPTIONS__{module.id}_H
    # - <module.include> set of all options includes
    # - option holder spec #define macro for option holder
    #   #define CVC4_OPTIONS__{module.id}__FOR_OPTION_HOLDER
    #   {option.name}__option_t::type {option.name};
    #   bool {option.name}__setByUser__;
    # - module declarations in CVC4::options (for each option)
    #   extern struct CVC4_PUBLIC {option.name}__option_t { typedef {option.type} type; type operator()() const; bool wasSetByUser() const; void set(const type& v); } {option.name} CVC4_PUBLIC;
    # - module specializations in CVC4::
    #   template <> void Options::set(options::{option.name}__option_t, const options::{option.name}__option_t::type& x);
    #   template <> bool Options::wasSetByUser(options::{option.name}__option_t) const;
    #   template <> void Options::assign(options::{option.name}__option_t, std::string option, std::string value);
    # - module inlines in CVC4::options
    #   inline {option.name}__option_t::type {option.name}__option_t::operator()() const { return (*Options::current())[*this]; }
    #   inline bool {option.name}__option_t::wasSetByUser() const { return Options::current()->wasSetByUser(*this); }
    #   inline void {option.name}__option_t::set(const {option.name}__option_t::type& v) { Options::current()->set(*this, v); }
    #
    # <module.name>_options.cpp
    #
    # - module accesors in namespace CVC4
    #   template <> void Options::set(options::{option.name}__option_t, const options::{option.name}__option_t::type& x) { d_holder->{option.name} = x; }
    #   template <> bool Options::wasSetByUser(options::{option.name}__option_t) const { return d_holder->{option.name}__setByUser__; }
    # - module global def in namespace CVC4::options
    #   struct {option.name}__option_t {option.name};

    tpl_module_h = read_tpl('module_template.h')
    tpl_module_cpp = read_tpl('module_template.cpp')

    if tpl_module_h is None:
        die("Cannot find 'module_template.h'. Aborting.")
    if tpl_module_cpp is None:
        die("Cannot find 'module_template.cpp'. Aborting.")

    # {name} ... option.name
    tpl_h_holder_spec_def = "#define CVC4_OPTIONS__{id}__FOR_OPTION_HOLDER"
    tpl_h_holder_spec = "{name}__option_t::type {name}; bool {name}__setByUser__;"

    # {name} ... option.name, {type} ... option.type
    tpl_h_decl =  "extern struct CVC4_PUBLIC {name}__option_t {{ "
    tpl_h_decl += "typedef {type} type; type operator()() const; "
    tpl_h_decl += "bool wasSetByUser() const; "
    tpl_h_decl += "void set(const type& v); }} {name} CVC4_PUBLIC;"

    # {name} ... option.name
    tpl_h_spec_s = "template <> void Options::set(options::{name}__option_t, const options::{name}__option_t::type& x);"
    tpl_h_spec_wsbu = "template <> bool Options::wasSetByUser(options::{name}__option_t) const;"
    tpl_h_spec_a = "template <> void Options::assign(options::{name}__option_t, std::string option, std::string value);"
    tpl_h_spec_ab = "template <> void Options::assignBool(options::{name}__option_t, std::string option, bool value);"

    # {name} ... option.name
    tpl_h_inl_s = "inline void {name}__option_t::set(const {name}__option_t::type& v) {{ Options::current()->set(*this, v); }}"
    tpl_h_inl_wsbu = "inline bool {name}__option_t::wasSetByUser() const {{ return Options::current()->wasSetByUser(*this); }}"
    tpl_h_inl_op = "inline {name}__option_t::type {name}__option_t::operator()() const {{ return (*Options::current())[*this]; }}"

    # {name} ... option.name
    tpl_cpp_acc_s = "template <> void Options::set(options::{name}__option_t, const options::{name}__option_t::type& x) {{ d_holder->{name} = x; }}"
    tpl_cpp_acc_wsbu = "template <> bool Options::wasSetByUser(options::{name}__option_t) const {{ return d_holder->{name}__setByUser__; }}"

    tpl_cpp_def = "struct {name}__option_t {name};"


    # .h file
    includes = set()
    holder_specs = []
    decls = []
    specs = []
    inls = []

    # .cpp file
    accs = []
    defs = []

    holder_specs.append(tpl_h_holder_spec_def.format(id=module.id))
    for option in module.options:
        if option.name == '-':
            continue

        ### generate code for {module.name}_options.h
        includes.update(["#include {}".format(x) for x in option.include])

        # generate option holder
        holder_specs.append(tpl_h_holder_spec.format(name=option.name))

        # generate module declaration
        decls.append(tpl_h_decl.format(name=option.name, type=option.type))

        # generate module specialization
        if not option.read_only:
            specs.append(tpl_h_spec_s.format(name=option.name))
        specs.append(tpl_h_spec_wsbu.format(name=option.name))

        if option.type == "bool":
            specs.append(tpl_h_spec_a.format(name=option.name))
        else:
            specs.append(tpl_h_spec_ab.format(name=option.name))

        # generate module inlines
        if not option.read_only:
            inls.append(tpl_h_inl_s.format(name=option.name))

        inls.append(tpl_h_inl_wsbu.format(name=option.name))
        inls.append(tpl_h_inl_op.format(name=option.name))


        ### generate code for {module.name}_options.cpp

        # accessors
        if not option.read_only:
            accs.append(tpl_cpp_acc_s.format(name=option.name))
        accs.append(tpl_cpp_acc_wsbu.format(name=option.name))

        # global defintions
        defs.append(tpl_cpp_def.format(name=option.name))



    filename=module.header[:-2]
    print(tpl_module_h.format(filename=filename,
                              header=module.header,
                              id=module.id,
                              includes="\n".join(sorted(list(includes))),
                              holder_spec=" \\\n".join(holder_specs),
                              decls="\n".join(decls),
                              specs="\n".join(specs),
                              inls="\n".join(inls)))

    print(tpl_module_cpp.format(filename=filename,
                                accs="\n".join(accs),
                                defs="\n".join(defs)))



def check(data):
    check_attribs(MODULE_ATTR_REQ, MODULE_ATTR_ALL, data, 'module')

    options = []
    if 'option' in data:
        for attribs in data['option']:
            check_attribs(OPTION_ATTR_REQ, OPTION_ATTR_ALL, attribs, 'option')
            options.append(Option(attribs))

    aliases = []
    if 'alias' in data:
        for attribs in data['alias']:
            check_attribs(ALIAS_ATTR_REQ, ALIAS_ATTR_ALL, attribs, 'alias')
            aliases.append(Alias(attribs))

    module = Module(data)
    module.options = options
    module.aliases = aliases
    return module


if __name__ == "__main__":

    if len(sys.argv) < 2:
        sys.exit("no TOML option file(s) given")

    filenames = sys.argv[1:]

    # parse files, check attributes and create module/option objects
    modules = []
    for filename in filenames:
        with open(filename, 'r') as f:
            modules.append(check(toml.load(f)))

    for module in modules:
        codegen_module(module)

    sys.exit(0)
