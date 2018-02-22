#!/usr/bin/env python3

import ast
import copy
import os
import re
import sys
import textwrap

# TODO: more checks for options, e.g., long options start with -- ...
# TODO: documentation generation
# TODO: long-options have --no- alternate if type is bool
# TODO: add error checking as done in mkoptions
# TODO: bool options don't have handlers
# TODO: check short options only one character
# TODO: links and --no- options
# TODO: if short option given, then also long option should be specified
# TODO: check option name clashes. alias vs. option etc.

MODULE_ATTR_REQ = ['id', 'name', 'header']
MODULE_ATTR_ALL = MODULE_ATTR_REQ + ['options', 'aliases']

OPTION_ATTR_REQ = ['category', 'type']
OPTION_ATTR_ALL = OPTION_ATTR_REQ + [
    'name', 'help', 'smt_name', 'short', 'long', 'default', 'includes',
    'handler', 'predicates', 'notifies', 'links', 'read_only'
]

ALIAS_ATTR_REQ = ['category', 'long', 'links']
ALIAS_ATTR_ALL = ALIAS_ATTR_REQ + ['help']

CATEGORY_VALUES = ['common', 'expert', 'regular', 'undocumented']

g_long_to_opt = dict()  # TODO: this maps long options to options and
                        # is needed to map links to links_smt for now
                        # (workaround to produce the same code)


tpl_holder_macro = 'CVC4_OPTIONS__{id}__FOR_OPTION_HOLDER'



class Module(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in MODULE_ATTR_ALL)
        self.options = []
        self.aliases = []
        for (k, v) in d.items():
            assert(k in d)
            if len(v) > 0:
                self.__dict__[k] = v

class Option(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in OPTION_ATTR_ALL)
        self.includes = []
        self.predicates = []
        self.notifies = []
        self.links = []
        self.read_only = False
        for (k, v) in d.items():
            assert(k in self.__dict__)
            if k == 'read_only' or v:
                self.__dict__[k] = v

class Alias(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in ALIAS_ATTR_ALL)
        self.links = []
        for (k, v) in d.items():
            assert(k in self.__dict__)
            if len(v) > 0:
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

def write_file(directory, name, s):
    fname = '{}/{}'.format(directory, name)
    try:
        if os.path.isfile(fname):
            f = open(fname, 'r')
            if s == f.read():
                print('{} is up-to-date'.format(name))
                return
        f = open(fname, 'w')
    except IOError:
        die("Could not write '{}'".format(fname))
    else:
        print('generating {}'.format(name))
        with f:
            f.write(s)


def read_tpl(directory, name):
    fname = '{}/{}'.format(directory, name)
    try:
        f = open(fname, 'r')
    except IOError:
        die("Could not find '{}'. Aborting.".format(fname))
    else:
        # Escape { and } since we later use .format to add the generated code.
        # Further, strip ${ and }$ from placeholder variables in the template
        # file.
        with f:
            contents = \
                f.read().replace('{', '{{').replace('}', '}}').\
                         replace('${', '').replace('}$', '')

            # insert correct line numbers and template name
            lines = contents.split('\n')
            for i in range(len(lines)):
                if lines[i].startswith('#line'):
                    lines[i] = lines[i].format(line=i + 2, template=name)

            return '\n'.join(lines)



def codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp):
    global g_long_to_opt

    # {name} ... option.name
    tpl_h_holder_macro = '#define ' + tpl_holder_macro
    tpl_h_holder = \
        "  {name}__option_t::type {name}; \\\n  bool {name}__setByUser__;"

    # {name} ... option.name, {type} ... option.type
    tpl_h_decl_rw  = "extern struct CVC4_PUBLIC {name}__option_t {{ "
    tpl_h_decl_rw += "typedef {type} type; type operator()() const; "
    tpl_h_decl_rw += "bool wasSetByUser() const; "
    tpl_h_decl_rw += "void set(const type& v); }} {name} CVC4_PUBLIC;"

    tpl_h_decl_ro  = "extern struct CVC4_PUBLIC {name}__option_t {{ "
    tpl_h_decl_ro += "typedef {type} type; type operator()() const; "
    tpl_h_decl_ro += "bool wasSetByUser() const; }} {name} CVC4_PUBLIC;"

    # {name} ... option.name
    tpl_h_spec_s    = "template <> void Options::set(options::{name}__option_t, const options::{name}__option_t::type& x);"
    tpl_h_spec_o    = "template <> const options::{name}__option_t::type& Options::operator[](options::{name}__option_t) const;"
    tpl_h_spec_wsbu = "template <> bool Options::wasSetByUser(options::{name}__option_t) const;"
    tpl_h_spec_a    = "template <> void Options::assign(options::{name}__option_t, std::string option, std::string value);"
    tpl_h_spec_ab   = "template <> void Options::assignBool(options::{name}__option_t, std::string option, bool value);"

    # {name} ... option.name
    tpl_h_inl_s    = "inline void {name}__option_t::set(const {name}__option_t::type& v) {{ Options::current()->set(*this, v); }}"
    tpl_h_inl_wsbu = "inline bool {name}__option_t::wasSetByUser() const {{ return Options::current()->wasSetByUser(*this); }}"
    tpl_h_inl_op   = "inline {name}__option_t::type {name}__option_t::operator()() const {{ return (*Options::current())[*this]; }}"

    # {name} ... option.name
    tpl_cpp_acc_s    = "template <> void Options::set(options::{name}__option_t, const options::{name}__option_t::type& x) {{ d_holder->{name} = x; }}"
    tpl_cpp_acc_o    = "template <> const options::{name}__option_t::type& Options::operator[](options::{name}__option_t) const {{ return d_holder->{name}; }}"
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

    holder_specs.append(tpl_h_holder_macro.format(id=module.id))

    for option in module.options:
        if option.long:
            g_long_to_opt[long_get_option(option.long)] = option

        if option.name is None:
            continue

        ### generate code for {module.name}_options.h
        for include in option.includes:
            includes.add(format_include(include))

        # generate option holder
        holder_specs.append(tpl_h_holder.format(name=option.name))

        # generate module declaration
        tpl_decl = tpl_h_decl_ro if option.read_only else tpl_h_decl_rw
        decls.append(tpl_decl.format(name=option.name, type=option.type))

        # generate module specialization
        if not option.read_only:
            specs.append(tpl_h_spec_s.format(name=option.name))
        specs.append(tpl_h_spec_o.format(name=option.name))
        specs.append(tpl_h_spec_wsbu.format(name=option.name))

        if option.type == 'bool':
            specs.append(tpl_h_spec_ab.format(name=option.name))
        else:
            specs.append(tpl_h_spec_a.format(name=option.name))

        # generate module inlines
        inls.append(tpl_h_inl_op.format(name=option.name))
        inls.append(tpl_h_inl_wsbu.format(name=option.name))
        if not option.read_only:
            inls.append(tpl_h_inl_s.format(name=option.name))


        ### generate code for {module.name}_options.cpp

        # accessors
        if not option.read_only:
            accs.append(tpl_cpp_acc_s.format(name=option.name))
        accs.append(tpl_cpp_acc_o.format(name=option.name))
        accs.append(tpl_cpp_acc_wsbu.format(name=option.name))

        # global defintions
        defs.append(tpl_cpp_def.format(name=option.name))


    filename=module.header.split('/')[1][:-2]
    write_file(dst_dir, '{}.h'.format(filename),
        tpl_module_h.format(
            filename=filename,
            header=module.header,
            id=module.id,
            includes='\n'.join(sorted(list(includes))),
            holder_spec=' \\\n'.join(holder_specs),
            decls='\n'.join(decls),
            specs='\n'.join(specs),
            inls='\n'.join(inls)))

    write_file(dst_dir, '{}.cpp'.format(filename),
        tpl_module_cpp.format(
            filename=filename,
            accs='\n'.join(accs),
            defs='\n'.join(defs)))

def match_option(long):
    global g_long_to_opt
    assert(long.startswith('--'))
    val = True
    opt = None
    long = long_get_option(long)
    if long.startswith('--no-'):
        val = False
        opt = g_long_to_opt[long[5:]]
    else:
        opt = g_long_to_opt[long[2:]]
    return (opt, val)


def long_get_arg(name):
    l = name.split('=')
    assert(len(l) <= 2)
    return l[1] if len(l) == 2 else None

def long_get_option(name):
    return name.split('=')[0]

def is_numeric_cpp_type(t):
    if t in ['int', 'unsigned', 'unsigned long', 'long', 'float', 'double']:
        return True
    elif re.match('u?int[0-9]+_t', t):
        return True
    return False

def format_include(include):
    if '<' in include:
        return '#include {}'.format(include)
    return '#include "{}"'.format(include)

def help_format_options(short, long):
    opts = []
    arg = None
    if long:
        opts.append('--{}'.format(long))
        l = long.split('=')
        if len(l) > 1:
            arg = l[1]

    if short:
        if arg:
            opts.append('-{} {}'.format(short, arg))
        else:
            opts.append('-{}'.format(short))

    return ' | '.join(opts)

def help_format(help, short, long):
    width = 80
    width_opt = 25
    text = \
        textwrap.wrap(help.replace('"', '\\"'), width=width - width_opt)
    text_opt = help_format_options(short, long)
    if len(text_opt) > width_opt - 3:
        lines = ['  {}'.format(text_opt)]
        lines.append(' ' * width_opt + text[0])
    else:
        lines = ['  {}{}'.format(text_opt.ljust(width_opt - 2), text[0])]
    lines.extend([' ' * width_opt + l for l in text[1:]])
    return ['"{}\\n"'.format(x) for x in lines]

def codegen_all_modules(modules, dst_dir, tpl_options, tpl_options_holder):

    option_value_start = 256

    tpl_run_handler_bool = \
"""template <> void runBoolPredicates(options::{name}__option_t, std::string option, bool b, options::OptionsHandler* handler) {{
  {predicates}
}}"""
# TODO: remove newline before {handler}
    tpl_run_handler = \
"""template <> options::{name}__option_t::type runHandlerAndPredicates(options::{name}__option_t, std::string option, std::string optionarg, options::OptionsHandler* handler) {{
  options::{name}__option_t::type retval = 
  {handler};
  {predicates}
  return retval;
}}"""
    tpl_assign = \
"""template <> void Options::assign(options::{name}__option_t, std::string option, std::string value) {{
  d_holder->{name} = runHandlerAndPredicates(options::{name}, option, value, d_handler);
  d_holder->{name}__setByUser__ = true;
  Trace(\"options\") << \"user assigned option {name}\" << std::endl;
  {notifications}
}}"""
    tpl_assign_bool = \
"""template <> void Options::assignBool(options::{name}__option_t, std::string option, bool value) {{
  runBoolPredicates(options::{name}, option, value, d_handler);
  d_holder->{name} = value;
  d_holder->{name}__setByUser__ = true;
  Trace(\"options\") << \"user assigned option {name}\" << std::endl;
  {notifications}
}}"""

    headers_module = []
    headers_handler = set()
    macros_module = []
    notifiers = []
    options_short = []
    cmdline_options = []
    options_smt = []
    options_getoptions = []
    options_handler = []
    defaults = []
    custom_handlers = []
    help_common = []
    help_others = []

    setoption_handlers = [] # TODO
    getoption_handlers = [] # TODO

    option_value_cur = option_value_start
    for module in modules:
        headers_module.append(format_include(module.header))
        macros_module.append(tpl_holder_macro.format(id=module.id))

        # TODO: sort by name
#        for option in sorted(module.options, key=lambda x: x.long if x.long else x.name):
        for option in module.options:
            assert(option.type != 'void' or option.name is None)
            assert(option.name or option.smt_name or option.short or option.long)
            argument_req = option.type not in ['bool', 'void']

            # TODO: we can probably remove these includes since they are
            #       already included in 'headers_module' header files
            for include in option.includes:
                headers_handler.add(format_include(include))

            # generate help text
            if (option.short or option.long) \
               and option.category != 'undocumented':
                l = help_common if option.category == 'common' else help_others
                if not option.help:
                    print("no help for {} option {}".format(
                           option.category, option.name))
                l.extend(help_format(option.help, option.short, option.long))

            ### generate handler call
            handler = None
            if option.handler:
                if option.type == 'void':
                    handler = 'handler->{}(option)'.format(option.handler)
                else:
                    handler = \
                        'handler->{}(option, optionarg)'.format(option.handler)
            elif option.type != 'bool':
                handler = \
                    'handleOption<{}>(option, optionarg)'.format(option.type)

            ### generate predicate calls
            predicates = []
            if option.predicates:
                if option.type == 'bool':
                    predicates = \
                        ['handler->{}(option, b);'.format(x) \
                            for x in option.predicates]
                elif option.type != 'void':
                    predicates = \
                        ['handler->{}(option, retval);'.format(x) \
                            for x in option.predicates]
                else:
                    assert(False)

            ### generate notification calls
            notifications = \
                ['d_handler->{}(option);'.format(x) for x in option.notifies]

            ### options_handler and cmdline_options
            cases = []
            if option.short:
                cases.append("case '{}':".format(option.short))

                options_short.append(option.short)
                if argument_req:
                    options_short.append(':')

            if option.long:
                cases.append(
                    'case {}:// --{}'.format(option_value_cur, option.long))
                cmdline_options.append(
                    '{{ "{}", {}_argument, nullptr, {} }},'.format(
                        long_get_option(option.long),
                        'required' if argument_req else 'no',
                        option_value_cur))
                option_value_cur += 1

            if len(cases) > 0:
                if option.type == 'bool' and option.name:
                    cases.append(
                        '  options->assignBool(options::{}, option, true);'.format(option.name))
                elif option.type != 'void' and option.name:
                    cases.append(
                        '  options->assign(options::{}, option, optionarg);'.format(option.name))
                elif handler:
                    cases.append('{};'.format(handler))

                cases.extend(
                    ['  extender->pushBackPreemption("{}");'.format(x) \
                        for x in option.links])
                cases.append('  break;\n')

                options_handler.extend(cases)


            ### generate handlers for setOption/getOption
            if option.smt_name or option.long:
                smtlinks = []
                for link in option.links:
                    m = match_option(link)
                    assert(m)
                    smtname = m[0].smt_name if m[0].smt_name else long_get_option(m[0].long)
                    assert(smtname)
                    smtlinks.append('setOption(std::string("{smtname}"), ("{value}"));'.format(
                        smtname=smtname,
                        value="true" if m[1] else "false"
                        ))

                smtname = option.smt_name if option.smt_name else long_get_option(option.long)

                setoption_handlers.append('if(key == "{}") {{'.format(smtname))
                if option.type == 'bool':
                    setoption_handlers.append(
                        'Options::current()->assignBool(options::{name}, "{smtname}", optionarg == "true");'.format(name=option.name, smtname=smtname))
                elif argument_req and option.name:
                    setoption_handlers.append(
                        'Options::current()->assign(options::{name}, "{smtname}", optionarg);'.format(name=option.name, smtname=smtname))
                elif option.handler:
                    handler = 'handler->{handler}("{smtname}"'
                    if argument_req:
                        handler += ', optionarg'
                    handler += ');'
                    setoption_handlers.append(
                        handler.format(handler=option.handler,
                                           smtname=smtname))

                if len(smtlinks) > 0:
                    setoption_handlers.append('\n'.join(smtlinks))
                setoption_handlers.append('return;')
                setoption_handlers.append('}')

                if option.name:
                    getoption_handlers.append(
                        'if (key == "{}") {{'.format(smtname))
                    if option.type == 'bool':
                        getoption_handlers.append(
                            'return options::{}() ? "true" : "false";'.format(
                                option.name))
                    else:
                        getoption_handlers.append('std::stringstream ss;')
                        if is_numeric_cpp_type(option.type):
                            getoption_handlers.append('ss << std::fixed << std::setprecision(8);')
                        getoption_handlers.append('ss << options::{}();'.format(option.name))
                        getoption_handlers.append('return ss.str();')
                    getoption_handlers.append('}')


            # handle --no- case for boolean options
            if option.long and option.type == 'bool':
                cases = []
                cases.append(
                    'case {}:// --no-{}'.format(
                        option_value_cur, option.long))
                cases.append(
                    '  options->assignBool(options::{}, option, false);'.format(option.name))
                cases.append('  break;\n')

                options_handler.extend(cases)

                cmdline_options.append(
                    '{{ "no-{}", {}_argument, nullptr, {} }},'.format(
                        long_get_option(option.long),
                        'required' if argument_req else 'no',
                        option_value_cur))
                option_value_cur += 1


            ### build opts for options::getOptions()
            if option.name:
                optname = None
                if option.smt_name:
                    optname = option.smt_name
                else:
                    optname = option.long

                if optname:
                    # collect SMT option names
                    options_smt.append('"{}",'.format(option.smt_name))

                    if option.type == 'bool':
                        s  = '{ std::vector<std::string> v; '
                        s += 'v.push_back("{}"); '.format(optname)
                        s += 'v.push_back(std::string(d_holder->{} ? "true" : "false")); '.format(option.name)
                        s += 'opts.push_back(v); }'
                    else:
                        s  = '{ std::stringstream ss; '
                        if is_numeric_cpp_type(option.type):
                            s += 'ss << std::fixed << std::setprecision(8); '
                        s += 'ss << d_holder->{}; '.format(option.name)
                        s += 'std::vector<std::string> v; '
                        s += 'v.push_back("{}"); '.format(optname)
                        s += 'v.push_back(ss.str()); '
                        s += 'opts.push_back(v); }'
                    options_getoptions.append(s)


            ### define runBoolPredicates/runHandlerAndPredicates
            if option.name:
                if option.type == 'bool':
                    if len(predicates) > 0:
                        assert(handler is None)
                        custom_handlers.append(
                            tpl_run_handler_bool.format(
                                name=option.name,
                                predicates='\n'.join(predicates)
                            ))
                elif option.short or option.long:
                    assert(option.type != 'void')
                    assert(handler)
                    custom_handlers.append(
                        tpl_run_handler.format(
                            name=option.name,
                            handler=handler,
                            predicates='\n'.join(predicates)
                        ))

            ### define handler assign/assignBool
            if option.name:
                tpl = tpl_assign_bool if option.type == 'bool' else tpl_assign
                if option.type == 'bool' \
                   or option.short or option.long or option.smt_name:
                    custom_handlers.append(
                            tpl.format(
                                name=option.name,
                                notifications='\n'.join(notifications)
                            ))

            # default option values
            if option.name:
                default = option.default if option.default else ''
                defaults.append('{}({})'.format(option.name, default))
                defaults.append('{}__setByUser__(false)'.format(option.name))


#        for alias in sorted(module.aliases, key=lambda x: x.long):
        for alias in module.aliases:
            argument_req = '=' in alias.long

            options_handler.append(
                'case {}:// --{}'.format(option_value_cur, alias.long))

            assert(len(alias.links) > 0)
            arg = long_get_arg(alias.long)
            for link in alias.links:
                arg_link = long_get_arg(link)
                if arg == arg_link:
                    options_handler.append(
                        'extender->pushBackPreemption("{}");'.format(long_get_option(link)))
                    if argument_req:
                        options_handler.append(
                            'extender->pushBackPreemption(optionarg.c_str());')
                else:
                    options_handler.append(
                        'extender->pushBackPreemption("{}");'.format(link))

            options_handler.append('  break;\n')

            cmdline_options.append(
                '{{ "{}", {}_argument, nullptr, {} }},'.format(
                    long_get_option(alias.long),
                    'required' if argument_req else 'no',
                    option_value_cur))
            option_value_cur += 1

            # generate help text
            if alias.category != 'undocumented':
                l = help_common if alias.category == 'common' else help_others
                if not alias.help:
                    print("no help for {} alias {}".format(
                            alias.category, alias.long))
                l.extend(help_format(alias.help, None, alias.long))

    write_file(dst_dir, 'options_holder.h',
        tpl_options_holder.format(
            headers_module='\n'.join(headers_module),
            macros_module='\n'.join(macros_module)
            ))

    write_file(dst_dir, 'options.cpp',
        tpl_options.format(
            headers_module='\n'.join(headers_module),
            headers_handler='\n'.join(sorted(list(headers_handler))),
            custom_handlers='\n'.join(custom_handlers),
            module_defaults=',\n  '.join(defaults),
            help_common='\n'.join(help_common),
            help_others='\n'.join(help_others),
            cmdline_options='\n  '.join(cmdline_options),
            options_short=''.join(options_short),
            options_handler='\n    '.join(options_handler),
            option_value_begin=option_value_start,
            option_value_end=option_value_cur,
            options_smt='\n  '.join(options_smt),
            options_getoptions='\n  '.join(options_getoptions),
            setoption_handlers='\n'.join(setoption_handlers),
            getoption_handlers='\n'.join(getoption_handlers)
        ))




def check(data):

    data_options = []
    data_aliases = []
    if 'options' in data:
        data_options = data['options']
        del(data['options'])
    if 'aliases' in data:
        data_aliases = data['aliases']
        del(data['aliases'])

    check_attribs(MODULE_ATTR_REQ, MODULE_ATTR_ALL, data, 'module')

    module = Module(data)
    for attribs in data_options:
        check_attribs(OPTION_ATTR_REQ, OPTION_ATTR_ALL, attribs, 'option')
        module.options.append(Option(attribs))
    for attribs in data_aliases:
        check_attribs(ALIAS_ATTR_REQ, ALIAS_ATTR_ALL, attribs, 'alias')
        module.aliases.append(Alias(attribs))

    return module

def perr(line, msg):
    die('option parse error at line {}: {}'.format(line + 1, msg))

def parse_value(lineno, s):

    if s[0] == '"':
        if s[-1] != '"':
            perr(lineno, 'missing closing " for string')
        s = s.lstrip('"').rstrip('"').replace('\\"', '"')
        return s if len(s) > 0 else None
    elif s[0] == '[':
        try:
            l = ast.literal_eval(s)
        except SyntaxError as e:
            perr(lineno, 'parsing list: {}'.format(e.msg))
        return l
    elif s == 'true':
        return True
    elif s == 'false':
        return False
    else:
        perr(lineno, "invalid value '{}'".format(s))

# simple parser for the module options files
def parse_module(file):
    module = dict()
    options = []
    aliases = []
    lines = [[x.strip() for x in line.split('=', maxsplit=1)] for line in file]
    option = None
    alias = None
    for i in range(len(lines)):
        assert(option is None or alias is None)
        line = lines[i]
        if len(line) == 1:
            # parse new option/alias, save previously parsed
            if line[0] in ['[[option]]', '[[alias]]']:
                if option:
                    options.append(option)
                    option = None
                if alias:
                    aliases.append(alias)
                    alias = None
                if line[0] == '[[option]]':
                    assert(alias is None)
                    option = dict()
                else:
                    assert(line[0] == '[[alias]]')
                    assert(option is None)
                    alias = dict()
            elif line[0] != '':
                perr(i, "invalid attribute '{}'".format(line[0]))
        elif len(line) == 2:
            attrib = line[0]
            value = parse_value(i, line[1])
            if option is not None:
                if attrib not in OPTION_ATTR_ALL:
                    perr(i, "invalid option attribute '{}'".format(attrib))
                if attrib in option:
                    perr(i, "duplicate option attribute '{}'".format(attrib))
                assert(option is not None)
                option[attrib] = value
            elif alias is not None:
                if attrib not in ALIAS_ATTR_ALL:
                    perr(i, "invalid alias attribute '{}'".format(attrib))
                if attrib in alias:
                    perr(i, "duplicate alias attribute '{}'".format(attrib))
                assert(alias is not None)
                alias[attrib] = value
            else:
                if attrib not in MODULE_ATTR_ALL:
                    perr(i, "invalid module attribute '{}'".format(attrib))
                if attrib in module:
                    perr(i, "duplicate module attribute '{}'".format(attrib))
                module[attrib] = value
        else:
            perr(i, "invalid attribute '{}'".format(line[0]))

    # save previously parsed option/alias
    if option:
        options.append(option)
    if alias:
        aliases.append(alias)

    module['options'] = options
    module['aliases'] = aliases
    return module

if __name__ == "__main__":

    if len(sys.argv) < 4:
        sys.exit("no TOML option file(s) given")

    src_dir = sys.argv[1]
    dst_dir = sys.argv[2]
    filenames = sys.argv[3:]

    # read template files
    tpl_module_h = read_tpl(src_dir, 'module_template.h')
    tpl_module_cpp = read_tpl(src_dir, 'module_template.cpp')
    tpl_options = read_tpl(src_dir, 'options_template_new.cpp')
    tpl_options_holder = read_tpl(src_dir, 'options_holder_template_new.h')

    # parse files, check attributes and create module/option objects
    modules = []
    for filename in filenames:
        with open(filename, 'r') as f:
            modules.append(check(parse_module(f)))

    for module in modules:
        codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp)

    codegen_all_modules(modules, dst_dir, tpl_options, tpl_options_holder)

    sys.exit(0)
