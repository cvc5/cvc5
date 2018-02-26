#!/usr/bin/env python3

import ast
import os
import re
import sys
import textwrap

# TODO: missing documentation
#       - manpage
#       - doxygen
#       - ??

### Allowed attributes for module/option/alias

g_module_attr_req = ['id', 'name', 'header']
g_module_attr_all = g_module_attr_req + ['options', 'aliases']

g_option_attr_req = ['category', 'type']
g_option_attr_all = g_option_attr_req + [
    'name', 'help', 'smt_name', 'short', 'long', 'default', 'includes',
    'handler', 'predicates', 'notifies', 'links', 'read_only'
]

g_alias_attr_req = ['category', 'long', 'links']
g_alias_attr_all = g_alias_attr_req + ['help']

g_category_values = ['common', 'expert', 'regular', 'undocumented']


### Other globals

g_long_to_opt = dict()     # maps long options to option objects
g_module_id_cache = dict() # maps ids to filename/lineno
g_long_cache = dict()      # maps long options to filename/fileno
g_short_cache = dict()     # maps short options to filename/fileno
g_smt_cache = dict()       # maps smt options to filename/fileno
g_name_cache = dict()      # maps option names to filename/fileno


### Source code templates

## Templates for options_holder.h

# {id} ... module.id
tpl_holder_macro = 'CVC4_OPTIONS__{id}__FOR_OPTION_HOLDER'

## Templates for options.cpp

tpl_run_handler = \
"""template <> options::{name}__option_t::type runHandlerAndPredicates(
    options::{name}__option_t,
    std::string option,
    std::string optionarg,
    options::OptionsHandler* handler)
{{
  options::{name}__option_t::type retval = {handler};
  {predicates}
  return retval;
}}"""

tpl_assign = \
"""template <> void Options::assign(
    options::{name}__option_t,
    std::string option,
    std::string value)
{{
  d_holder->{name} =
    runHandlerAndPredicates(options::{name}, option, value, d_handler);
  d_holder->{name}__setByUser__ = true;
  Trace("options") << "user assigned option {name}" << std::endl;
  {notifications}
}}"""

tpl_run_handler_bool = \
"""template <> void runBoolPredicates(
    options::{name}__option_t,
    std::string option,
    bool b,
    options::OptionsHandler* handler)
{{
  {predicates}
}}"""

tpl_assign_bool = \
"""template <> void Options::assignBool(
    options::{name}__option_t,
    std::string option,
    bool value)
{{
  runBoolPredicates(options::{name}, option, value, d_handler);
  d_holder->{name} = value;
  d_holder->{name}__setByUser__ = true;
  Trace("options") << "user assigned option {name}" << std::endl;
  {notifications}
}}"""

## Templates for *_options.h

# {name} ... option.name
tpl_h_holder_macro = '#define ' + tpl_holder_macro
tpl_h_holder_macro_attr  = "  {name}__option_t::type {name};\\\n"
tpl_h_holder_macro_attr += "  bool {name}__setByUser__;"

# {name} ... option.name, {type} ... option.type
tpl_h_struct_rw  = \
"""extern struct CVC4_PUBLIC {name}__option_t
{{
  typedef {type} type;
  type operator()() const;
  bool wasSetByUser() const;
  void set(const type& v);
}} {name} CVC4_PUBLIC;"""

tpl_h_struct_ro  = \
"""extern struct CVC4_PUBLIC {name}__option_t
{{
  typedef {type} type;
  type operator()() const;
  bool wasSetByUser() const;
}} {name} CVC4_PUBLIC;"""

# {name} ... option.name
tpl_h_spec_s    = \
"""template <> void Options::set(
    options::{name}__option_t,
    const options::{name}__option_t::type& x);"""

tpl_h_spec_o    = \
"""template <> const options::{name}__option_t::type& Options::operator[](
    options::{name}__option_t) const;"""

tpl_h_spec_wsbu = \
"""template <> bool Options::wasSetByUser(options::{name}__option_t) const;"""

tpl_h_spec_a = \
"""template <> void Options::assign(
    options::{name}__option_t,
    std::string option,
    std::string value);"""

tpl_h_spec_ab = \
"""template <> void Options::assignBool(
    options::{name}__option_t,
    std::string option,
    bool value);"""

# {name} ... option.name
tpl_h_impl_s = \
"""inline void {name}__option_t::set(
    const {name}__option_t::type& v)
{{
  Options::current()->set(*this, v);
}}"""

tpl_h_impl_wsbu = \
"""inline bool {name}__option_t::wasSetByUser() const
{{
  return Options::current()->wasSetByUser(*this);
}}"""

tpl_h_impl_op = \
"""inline {name}__option_t::type {name}__option_t::operator()() const
{{
  return (*Options::current())[*this];
}}"""


## Templates for *_options.cpp

# {name} ... option.name
tpl_c_acc_s = \
"""template <> void Options::set(
    options::{name}__option_t,
    const options::{name}__option_t::type& x)
{{
  d_holder->{name} = x;
}}"""

tpl_c_acc_o = \
"""template <> const options::{name}__option_t::type& Options::operator[](
    options::{name}__option_t) const
{{
  return d_holder->{name};
}}"""

tpl_c_acc_wsbu = \
"""template <> bool Options::wasSetByUser(
    options::{name}__option_t) const
{{
  return d_holder->{name}__setByUser__;
}}"""

tpl_c_struct = "struct {name}__option_t {name};"




class Module(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in g_module_attr_all)
        self.options = []
        self.aliases = []
        for (k, v) in d.items():
            assert(k in d)
            if len(v) > 0:
                self.__dict__[k] = v

class Option(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in g_option_attr_all)
        self.includes = []
        self.predicates = []
        self.notifies = []
        self.links = []
        self.read_only = False
        self.lineno = None
        self.filename = None
        self.add_alternative = True  # add --no- alternative for bool
        for (k, v) in d.items():
            assert(k in self.__dict__)
            if k == 'read_only' or v:
                self.__dict__[k] = v

class Alias(object):
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in g_alias_attr_all)
        self.links = []
        self.lineno = None
        self.filename = None
        for (k, v) in d.items():
            assert(k in self.__dict__)
            if len(v) > 0:
                self.__dict__[k] = v


def die(msg):
    sys.exit(msg)


# TODO: pass filename, lineno
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

            # Insert correct line numbers and template name
            lines = contents.split('\n')
            for i in range(len(lines)):
                if lines[i].startswith('#line'):
                    lines[i] = lines[i].format(line=i + 2, template=name)

            return '\n'.join(lines)


def match_option(long):
    global g_long_to_opt
    val = True
    opt = None
    long = lstrip('--', long_get_option(long))
    if long.startswith('no-'):
        val = False
        opt = g_long_to_opt.get(lstrip('no-', long))
    else:
        opt = g_long_to_opt.get(long)
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


# Generate code for each option module (*_options.{h,cpp})
def codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp):
    global g_long_to_opt

    # *_options.h
    includes = set()
    holder_specs = []
    decls = []
    specs = []
    inls = []

    # *_options_.cpp
    accs = []
    defs = []

    holder_specs.append(tpl_h_holder_macro.format(id=module.id))

    for option in module.options:
        if option.name is None:
            continue

        ### Generate code for {module.name}_options.h
        for include in option.includes:
            includes.add(format_include(include))

        # Generate option holder macro
        holder_specs.append(tpl_h_holder_macro_attr.format(name=option.name))

        # Generate module declaration
        tpl_decl = tpl_h_struct_ro if option.read_only else tpl_h_struct_rw
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
        inls.append(tpl_h_impl_op.format(name=option.name))
        inls.append(tpl_h_impl_wsbu.format(name=option.name))
        if not option.read_only:
            inls.append(tpl_h_impl_s.format(name=option.name))


        ### generate code for {module.name}_options.cpp

        # accessors
        if not option.read_only:
            accs.append(tpl_c_acc_s.format(name=option.name))
        accs.append(tpl_c_acc_o.format(name=option.name))
        accs.append(tpl_c_acc_wsbu.format(name=option.name))

        # global defintions
        defs.append(tpl_c_struct.format(name=option.name))


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


# Generate code for all option modules (options.cpp, options_holder.h)
def codegen_all_modules(modules, dst_dir, tpl_options, tpl_options_holder):

    option_value_start = 256

    headers_module = []      # generated *_options.h header includes
    headers_handler = set()  # option includes (for handlers, predicates, ...)
    macros_module = []       # option holder macro for options_holder.h
    options_short = []       # short options for getopt_long
    cmdline_options = []     # long options for getopt_long
    options_smt = []         # all options names accessible via {set,get}-option
    options_getoptions = []  # options for Options::getOptions()
    options_handler = []     # option handler calls
    defaults = []            # default values
    custom_handlers = []     # custom handler implementations assign/assignBool
    help_common = []         # help text for all common options
    help_others = []         # help text for all non-common options
    setoption_handlers = []  # handlers for set-option command
    getoption_handlers = []  # handlers for get-option command

    option_value_cur = option_value_start
    for module in modules:
        headers_module.append(format_include(module.header))
        macros_module.append(tpl_holder_macro.format(id=module.id))

        if module.options or module.aliases:
            help_others.append(
                '"\\nFrom the {} module:\\n"'.format(module.name))

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

            # Generate and format help text
            if (option.short or option.long) \
               and option.category != 'undocumented':
                l = help_common if option.category == 'common' else help_others
                if not option.help:
                    print("no help for {} option {}".format(
                           option.category, option.name))
                help = option.help
                if option.category == 'expert':
                    help += ' (EXPERTS only)'
                if option.type == 'bool':
                    help += ' [*]'
                l.extend(help_format(help, option.short, option.long))

            ### Generate handler call
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

            ### Generate predicate calls
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

            ### Generate notification calls
            notifications = \
                ['d_handler->{}(option);'.format(x) for x in option.notifies]

            ### Generate options_handler and cmdline_options
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


            ### Generate handlers for setOption/getOption
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
                            getoption_handlers.append(
                                'ss << std::fixed << std::setprecision(8);')
                        getoption_handlers.append('ss << options::{}();'.format(
                            option.name))
                        getoption_handlers.append('return ss.str();')
                    getoption_handlers.append('}')


            # Add --no- alternative options for boolean options
            if option.long and option.type == 'bool' and option.add_alternative:
                cases = []
                cases.append(
                    'case {}:// --no-{}'.format(
                        option_value_cur, option.long))
                cases.append(
                    '  options->assignBool(options::{}, option, false);'.format(
                        option.name))
                cases.append('  break;\n')

                options_handler.extend(cases)

                cmdline_options.append(
                    '{{ "no-{}", {}_argument, nullptr, {} }},'.format(
                        long_get_option(option.long),
                        'required' if argument_req else 'no',
                        option_value_cur))
                option_value_cur += 1


            if option.name:
                optname = option.smt_name if option.smt_name else option.long

                ### Build options for options::getOptions()
                if optname:
                    # collect SMT option names
                    options_smt.append('"{}",'.format(long_get_option(optname)))

                    if option.type == 'bool':
                        s  = '{ std::vector<std::string> v; '
                        s += 'v.push_back("{}"); '.format(optname)
                        s += 'v.push_back(std::string('
                        s += 'd_holder->{} ? "true" : "false")); '.format(
                                option.name)
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


                ### Define runBoolPredicates/runHandlerAndPredicates
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

                ### Define handler assign/assignBool
                tpl = tpl_assign_bool if option.type == 'bool' else tpl_assign
                if option.type == 'bool' \
                   or option.short or option.long or option.smt_name:
                    custom_handlers.append(
                            tpl.format(
                                name=option.name,
                                notifications='\n'.join(notifications)
                            ))

                # default option values
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
                        'extender->pushBackPreemption("{}");'.format(
                            long_get_option(link)))
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


def perr(filename, lineno, msg):
    die('parse error in {}:{}: {}'.format(filename, lineno + 1, msg))


def lstrip(prefix, s):
    return s[len(prefix):] if s.startswith(prefix) else s


def rstrip(suffix, s):
    return s[:-len(suffix)] if s.endswith(suffix) else s


def parse_value(filename, lineno, attrib, s):

    if s[0] == '"':
        if s[-1] != '"':
            perr(filename, lineno, 'missing closing " for string')
        s = s.lstrip('"').rstrip('"').replace('\\"', '"')

        # for read_only we allow both true/false and "true"/"false"
        if attrib == 'read_only':
            if s == 'true':
                return True
            elif s == 'false':
                return False
        return s if len(s) > 0 else None
    elif s[0] == '[':
        try:
            l = ast.literal_eval(s)
        except SyntaxError as e:
            perr(filename, lineno, 'parsing list: {}'.format(e.msg))
        return l
    elif s == 'true':
        return True
    elif s == 'false':
        return False
    else:
        perr(filename, lineno, "invalid value '{}'".format(s))


def check_unique(filename, lineno, value, cache, attrib):
    if value in cache:
        perr(filename, lineno,
             "'{}' already defined in '{}' at line {}".format(
                 value, cache[value][0], cache[value][1]))
    cache[value] = (filename, lineno + 1)


def check_long(filename, lineno, long, type = None):
    global g_long_cache
    if long is None:
        return
    if long.startswith('--'):
        perr(filename, lineno, 'remove -- prefix from long option')
    r = '[0-9a-zA-Z\-=]+'
    if not re.fullmatch(r, long):
        perr(fielname, lineno,
             "long option '{}' does not match regex criteria '{}'".format(
                long, r))
    name = long_get_option(long)
    check_unique(filename, lineno, name, g_long_cache, 'long')

    if type == 'bool':
        check_unique(filename, lineno,
                     'no-{}'.format(name), g_long_cache, 'long')


def check_links(filename, lineno, links):
    global g_long_cache
    for link in links:
        long = lstrip('no-', lstrip('--', long_get_option(link)))
        if long not in g_long_cache:
            perr(filename, lineno,
                 "invalid long option '{}' in links list".format(link))


def check_alias_attrib(filename, lineno, attrib, value):
    if attrib not in g_alias_attr_all:
        perr(filename, lineno, "invalid alias attribute '{}'".format(attrib))
    if attrib == 'category':
        if value not in g_category_values:
            perr(filename, lineno, "invalid category value '{}'".format(value))
    elif attrib == 'long':
        pass # Will be checked after parsing is done
    elif attrib == 'links':
        assert(isinstance(value, list))
        if len(value) == 0:
            perr(filename, lineno, 'links list must not be empty')


def check_option_attrib(filename, lineno, attrib, value):
    global g_smt_cache, g_name_cache, g_short_cache

    if attrib not in g_option_attr_all:
        perr(filename, lineno, "invalid option attribute '{}'".format(attrib))

    if attrib == 'category':
        if value not in g_category_values:
            perr(filename, lineno, "invalid category value '{}'".format(value))
    elif attrib == 'type':
        if len(value) == 0:
            perr(filename, lineno, 'type must not be empty'.format(value))
    elif attrib == 'long':
        pass # Will be checked after parsing is done
    elif attrib == 'name' and value:
        r = '[a-zA-Z]+[0-9a-zA-Z_]*'
        if not re.fullmatch(r, value):
            perr(filename, lineno,
                 "name '{}' does not match regex criteria '{}'".format(
                    value, r))
        check_unique(filename, lineno, value, g_name_cache, attrib)
    elif attrib == 'smt_name' and value:
        r = '[a-zA-Z]+[0-9a-zA-Z\-_]*'
        if not re.fullmatch(r, value):
            perr(filename, lineno,
                 "smt_name '{}' does not match regex criteria '{}'".format(
                    value, r))
        check_unique(filename, lineno, value, g_smt_cache, attrib)
    elif attrib == 'short' and value:
        if value[0].startswith('-'):
            perr(filename, lineno, 'remove - prefix from short option')
        if len(value) != 1:
            perr(filename, lineno, 'short option must be of length 1')
        if not value.isalpha() and not value.isdigit():
            perr(filename, lineno, 'short option must be a character or a digit')
        check_unique(filename, lineno, value, g_short_cache, attrib)
    elif attrib == 'default':
        pass
    elif attrib == 'includes' and value:
        if not isinstance(value, list):
            perr(filename, lineno, 'expected list for includes attribute')
    elif attrib == 'handler':
        pass
    elif attrib == 'predicates' and value:
        if not isinstance(value, list):
            perr(filename, lineno, 'expected list for predicates attribute')
    elif attrib == 'notifies' and value:
        if not isinstance(value, list):
            perr(filename, lineno, 'expected list for notifies attribute')
    elif attrib == 'links' and value:
        if not isinstance(value, list):
            perr(filename, lineno, 'expected list for links attribute')
    elif attrib == 'read_only' and value:
        if not isinstance(value, bool):
            perr(filename, lineno,
                 "expected true/false instead of '{}' for read_only".format(
                     value))


def check_module_attrib(filename, lineno, attrib, value):
    global g_module_id_cache
    if attrib not in g_module_attr_all:
        perr(filename, lineno, "invalid module attribute '{}'".format(attrib))
    if attrib == 'id':
        if len(value) == 0:
            perr(lineno, 'module id must not be empty')
        if value in g_module_id_cache:
            perr(filename, lineno,
                 "module id '{}' already defined in '{}' at line {}".format(
                     value,
                     g_module_id_cache[value][0],
                     g_module_id_cache[value][1]))
        g_module_id_cache[value] = (filename, lineno)
        if not value.isalpha():
            perr(filename, lineno,
                 "module id '{}' should only contain characters".format(value))
    elif attrib == 'name':
        if len(value) == 0:
            perr(filename, lineno, 'module name must not be empty')
    elif attrib == 'header':
        if len(value) == 0:
            perr(filename, lineno, 'module header must not be empty')
        header_name = 'options/{}.h'.format(
                            rstrip('.toml', os.path.basename(filename)))
        if header_name != value:
            perr(filename, lineno,
                 "expected module header '{}' instead of '{}'".format(
                     header_name, value))


# Parse options module file.
#
# Note: We could use an existing toml parser to parse the configuration files.
# However, since we only use a very restricted feature set of the toml format,
# we chose to implement our own parser to get better error messages.
def parse_module(filename, file):
    module = dict()
    options = []
    aliases = []
    lines = [[x.strip() for x in line.split('=', maxsplit=1)] for line in file]
    option = None
    alias = None
    option_lines = []
    alias_lines = []
    for i in range(len(lines)):
        assert(option is None or alias is None)
        line = lines[i]
        # skip comments
        if line[0].startswith('#'):
            continue
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
                    option_lines.append(i)
                else:
                    assert(line[0] == '[[alias]]')
                    assert(option is None)
                    alias = dict()
                    alias_lines.append(i)
            elif line[0] != '':
                perr(filename, i, "invalid attribute '{}'".format(line[0]))
        elif len(line) == 2:
            attrib = line[0]
            value = parse_value(filename, i, attrib, line[1])
            if option is not None:
                check_option_attrib(filename, i, attrib, value)
                if attrib in option:
                    perr(filename, i,
                         "duplicate option attribute '{}'".format(attrib))
                assert(option is not None)
                option[attrib] = value
            elif alias is not None:
                check_alias_attrib(filename, i, attrib, value)
                if attrib in alias:
                    perr(filename, i,
                         "duplicate alias attribute '{}'".format(attrib))
                assert(alias is not None)
                alias[attrib] = value
            else:
                if attrib in module:
                    perr(filename, i,
                         "duplicate module attribute '{}'".format(attrib))
                check_module_attrib(filename, i, attrib, value)
                module[attrib] = value
        else:
            perr(filename, i, "invalid attribute '{}'".format(line[0]))

    # Save previously parsed option/alias
    if option:
        options.append(option)
    if alias:
        aliases.append(alias)

    # Check if required attributes are defined and create
    # module/option/alias objects
    check_attribs(g_module_attr_req, g_module_attr_all, module, 'module')
    res = Module(module)

    assert(len(option_lines) == len(options))
    assert(len(alias_lines) == len(aliases))

    for i in range(len(options)):
        attribs = options[i]
        lineno = option_lines[i]
        check_attribs(g_option_attr_req, g_option_attr_all, attribs, 'option')
        option = Option(attribs)
        if option.short and not option.long:
            perr(filename, lineno,
                 "short option '{}' specified but no long option".format(
                    option.short))
        if option.type == 'bool' and option.handler:
            perr(filename, lineno,
                 'specifying handlers for options of type bool is not allowed')
        if option.category != 'undocumented' and not option.help:
            perr(filename, lineno,
                 'help text is required for {} options'.format(option.category))
        option.lineno = option_lines[i]
        option.filename = filename
        res.options.append(option)

    for i in range(len(aliases)):
        attribs = aliases[i]
        check_attribs(g_alias_attr_req, g_alias_attr_all, attribs, 'alias')
        alias = Alias(attribs)
        alias.lineno = alias_lines[i]
        alias.filename = filename
        res.aliases.append(alias)
    return res


def usage():
    print('mkoptions.py <src> <dst> <toml>+')
    print('')
    print('  <src>     directory that contains all *_template.{cpp,h} files')
    print('  <dst>     destination directory for the generated source files')
    print('  <toml>+   one or more *_optios.toml files')


if __name__ == "__main__":

    if len(sys.argv) < 4:
        usage()
        die('not enough arguments given')

    src_dir = sys.argv[1]
    dst_dir = sys.argv[2]
    filenames = sys.argv[3:]

    if not os.path.isdir(src_dir):
        usage()
        die("'{}' is not a directory".format(src_dir))
    if not os.path.isdir(dst_dir):
        usage()
        die("'{}' is not a directory".format(dst_dir))

    # Read template files from source directory
    tpl_module_h = read_tpl(src_dir, 'module_template.h')
    tpl_module_cpp = read_tpl(src_dir, 'module_template.cpp')
    tpl_options = read_tpl(src_dir, 'options_template.cpp')
    tpl_options_holder = read_tpl(src_dir, 'options_holder_template.h')

    # Parse files, check attributes and create module/option objects
    modules = []
    for filename in filenames:
        with open(filename, 'r') as f:
            module = parse_module(filename, f)
            # Check if long options are valid and unique.  First populate
            # g_long_cache with option.long and --no- alternatives if
            # applicable.
            for option in module.options:
                check_long(option.filename, option.lineno, option.long,
                           option.type)
                if option.long:
                    g_long_to_opt[long_get_option(option.long)] = option

            modules.append(module)

    # Then check if alias.long is unique
    for module in modules:
        for alias in module.aliases:
            # If an alias defines a --no- alternative for an existing boolean
            # option, we do not create the alternative for the option, but use
            # the alias instead.
            # This can be useful, since we can define links for the alternative
            # options, which would not be possible otherwise.
            # TODO: if we define an alternative for an existing long option we
            #       still need to set the option to false
            if alias.long.startswith('no-'):
                m = match_option(alias.long)
                if m[0] and m[0].type == 'bool':
                    m[0].add_alternative = False
                    del(g_long_cache[alias.long])
            check_long(alias.filename, alias.lineno, alias.long)

    # Check if long options in links lists are valid
    # (that needs to be done after checking all long options)
    for module in modules:
        for option in module.options:
            check_links(option.filename, option.lineno, option.links)
        for alias in module.aliases:
            check_links(alias.filename, alias.lineno, alias.links)

    # Create *_options.{h,cpp} in destination directory
    for module in modules:
        codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp)

    # Create options.cpp and options_holder.h in destination directory
    codegen_all_modules(modules, dst_dir, tpl_options, tpl_options_holder)

    sys.exit(0)
