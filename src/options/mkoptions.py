#!/usr/bin/env python3
"""
    Generate option handling code and documentation in one pass. The generated
    files are only written to the destination file if the contents of the file
    has changed (in order to avoid global re-compilation if only single option
    files changed).

    mkoptions.py <tpl-src> <tpl-doc> <dst> <toml>+

      <tpl-src> location of all *_template.{cpp,h} files
      <tpl-doc> location of all *_template documentation files
      <dst>     destination directory for the generated source code files
      <toml>+   one or more *_optios.toml files


    Directory <tpl-src> must contain:
        - options_template.cpp
        - module_template.cpp
        - options_holder_template.h
        - module_template.h

    Directory <tpl-doc> must contain:
        - cvc4.1_template
        - options.3cvc_template
        - SmtEngine.3cvc_template
    These files get generated during autogen.sh from the corresponding *.in
    files in doc/. Note that for the generated documentation files tpl-doc is
    also the destination directory.

    <toml>+ must be the list of all *.toml option configuration files from
    the src/options directory.


    The script generates the following files:
        - <dst>/MODULE_options.h
        - <dst>/MODULE_options.cpp
        - <dst>/options_holder.h
        - <dst>/options.cpp
        - <tpl-doc>/cvc4.1
        - <tpl-doc>/options.3
        - <tpl-doc>/SmtEngine.3
"""

import ast
import os
import re
import sys
import textwrap

### Allowed attributes for module/option/alias

MODULE_ATTR_REQ = ['id', 'name', 'header']
MODULE_ATTR_ALL = MODULE_ATTR_REQ + ['options', 'aliases']

OPTION_ATTR_REQ = ['category', 'type']
OPTION_ATTR_ALL = OPTION_ATTR_REQ + [
    'name', 'help', 'smt_name', 'short', 'long', 'default', 'includes',
    'handler', 'predicates', 'notifies', 'links', 'read_only', 'alternate'
]

ALIAS_ATTR_REQ = ['category', 'long', 'links']
ALIAS_ATTR_ALL = ALIAS_ATTR_REQ + ['help']

CATEGORY_VALUES = ['common', 'expert', 'regular', 'undocumented']

SUPPORTED_CTYPES = ['int', 'unsigned', 'unsigned long', 'long', 'float',
                    'double']

### Other globals

g_long_to_opt = dict()     # maps long options to option objects
g_module_id_cache = dict() # maps ids to filename/lineno
g_long_cache = dict()      # maps long options to filename/fileno
g_short_cache = dict()     # maps short options to filename/fileno
g_smt_cache = dict()       # maps smt options to filename/fileno
g_name_cache = dict()      # maps option names to filename/fileno
g_long_arguments = set()   # set of long options that require an argument

g_getopt_long_start = 256

### Source code templates

TPL_HOLDER_MACRO_NAME = 'CVC4_OPTIONS__{id}__FOR_OPTION_HOLDER'

TPL_RUN_HANDLER = \
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

TPL_DECL_ASSIGN = \
"""template <> void Options::assign(
    options::{name}__option_t,
    std::string option,
    std::string value);"""

TPL_IMPL_ASSIGN = TPL_DECL_ASSIGN[:-1] + \
"""
{{
  d_holder->{name} =
    runHandlerAndPredicates(options::{name}, option, value, d_handler);
  d_holder->{name}__setByUser__ = true;
  Trace("options") << "user assigned option {name}" << std::endl;
  {notifications}
}}"""


TPL_RUN_HANDLER_BOOL = \
"""template <> void runBoolPredicates(
    options::{name}__option_t,
    std::string option,
    bool b,
    options::OptionsHandler* handler)
{{
  {predicates}
}}"""

TPL_DECL_ASSIGN_BOOL = \
"""template <> void Options::assignBool(
    options::{name}__option_t,
    std::string option,
    bool value);"""

TPL_IMPL_ASSIGN_BOOL = TPL_DECL_ASSIGN_BOOL[:-1] + \
"""
{{
  runBoolPredicates(options::{name}, option, value, d_handler);
  d_holder->{name} = value;
  d_holder->{name}__setByUser__ = true;
  Trace("options") << "user assigned option {name}" << std::endl;
  {notifications}
}}"""

TPL_CALL_ASSIGN_BOOL = \
    '  options->assignBool(options::{name}, {option}, {value});'

TPL_CALL_ASSIGN = '  options->assign(options::{name}, {option}, optionarg);'

TPL_CALL_SET_OPTION = 'setOption(std::string("{smtname}"), ("{value}"));'

TPL_GETOPT_LONG = '{{ "{}", {}_argument, nullptr, {} }},'

TPL_PUSHBACK_PREEMPT = 'extender->pushBackPreemption({});'


TPL_HOLDER_MACRO = '#define ' + TPL_HOLDER_MACRO_NAME

TPL_HOLDER_MACRO_ATTR = "  {name}__option_t::type {name};\\\n"
TPL_HOLDER_MACRO_ATTR += "  bool {name}__setByUser__;"


TPL_OPTION_STRUCT_RW = \
"""extern struct CVC4_PUBLIC {name}__option_t
{{
  typedef {type} type;
  type operator()() const;
  bool wasSetByUser() const;
  void set(const type& v);
}} {name} CVC4_PUBLIC;"""

TPL_OPTION_STRUCT_RO = \
"""extern struct CVC4_PUBLIC {name}__option_t
{{
  typedef {type} type;
  type operator()() const;
  bool wasSetByUser() const;
}} {name} CVC4_PUBLIC;"""


TPL_DECL_SET = \
"""template <> void Options::set(
    options::{name}__option_t,
    const options::{name}__option_t::type& x);"""

TPL_IMPL_SET = TPL_DECL_SET[:-1] + \
"""
{{
  d_holder->{name} = x;
}}"""


TPL_DECL_OP_BRACKET = \
"""template <> const options::{name}__option_t::type& Options::operator[](
    options::{name}__option_t) const;"""

TPL_IMPL_OP_BRACKET = TPL_DECL_OP_BRACKET[:-1] + \
"""
{{
  return d_holder->{name};
}}"""


TPL_DECL_WAS_SET_BY_USER = \
"""template <> bool Options::wasSetByUser(options::{name}__option_t) const;"""

TPL_IMPL_WAS_SET_BY_USER = TPL_DECL_WAS_SET_BY_USER[:-1] + \
"""
{{
  return d_holder->{name}__setByUser__;
}}"""


# Option specific methods

TPL_IMPL_OPTION_SET = \
"""inline void {name}__option_t::set(const {name}__option_t::type& v)
{{
  Options::current()->set(*this, v);
}}"""

TPL_IMPL_OP_PAR = \
"""inline {name}__option_t::type {name}__option_t::operator()() const
{{
  return (*Options::current())[*this];
}}"""

TPL_IMPL_OPTION_WAS_SET_BY_USER = \
"""inline bool {name}__option_t::wasSetByUser() const
{{
  return Options::current()->wasSetByUser(*this);
}}"""



class Module(object):
    """Options module.

    An options module represents a MODULE_options.toml option configuration
    file and contains lists of options and aliases.
    """
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in MODULE_ATTR_ALL)
        self.options = []
        self.aliases = []
        for (attr, val) in d.items():
            assert attr in self.__dict__
            if val:
                self.__dict__[attr] = val


class Option(object):
    """Module option.

    An instance of this class corresponds to an option defined in a
    MODULE_options.toml configuration file specified via [[option]].
    """
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in OPTION_ATTR_ALL)
        self.includes = []
        self.predicates = []
        self.notifies = []
        self.links = []
        self.read_only = False
        self.alternate = True    # add --no- alternative long option for bool
        self.lineno = None
        self.filename = None
        for (attr, val) in d.items():
            assert attr in self.__dict__
            if attr in ['read_only', 'alternate'] or val:
                self.__dict__[attr] = val


class Alias(object):
    """Module alias.

    An instance of this class corresponds to an alias defined in a
    MODULE_options.toml configuration file specified via [[alias]].
    """
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in ALIAS_ATTR_ALL)
        self.links = []
        self.lineno = None
        self.filename = None
        self.alternate_for = None  # replaces a --no- alternative for an option
        for (attr, val) in d.items():
            assert attr in self.__dict__
            if val:
                self.__dict__[attr] = val


def die(msg):
    sys.exit('[error] {}'.format(msg))


def perr(filename, lineno, msg):
    die('parse error in {}:{}: {}'.format(filename, lineno + 1, msg))


def write_file(directory, name, content):
    """
    Write string 'content' to file directory/name. If the file already exists,
    we first check if the contents of the file is different from 'content'
    before overwriting the file.
    """
    fname = os.path.join(directory, name)
    try:
        if os.path.isfile(fname):
            with open(fname, 'r') as file:
                if content == file.read():
                    print('{} is up-to-date'.format(name))
                    return
        with open(fname, 'w') as file:
            print('generated {}'.format(name))
            file.write(content)
    except IOError:
        die("Could not write '{}'".format(fname))


def read_tpl(directory, name):
    """
    Read a template file directory/name. The contents of the template file will
    be read into a string, which will later be used to fill in the generated
    code/documentation via format. Hence, we have to escape curly braces. All
    placeholder variables in the template files are enclosed in ${placeholer}$
    and will be {placeholder} in the returned string.
    """
    fname = os.path.join(directory, name)
    try:
        # Escape { and } since we later use .format to add the generated code.
        # Further, strip ${ and }$ from placeholder variables in the template
        # file.
        with open(fname, 'r') as file:
            contents = \
                file.read().replace('{', '{{').replace('}', '}}').\
                            replace('${', '').replace('}$', '')
            return contents
    except IOError:
        die("Could not find '{}'. Aborting.".format(fname))


def match_option(long_name):
    """
    Lookup option by long_name option name. The function returns a tuple of (option,
    bool), where the bool indicates the option value (true if not alternate,
    false if alternate option).
    """
    global g_long_to_opt
    val = True
    opt = None
    long_name = lstrip('--', long_get_option(long_name))
    if long_name.startswith('no-'):
        opt = g_long_to_opt.get(lstrip('no-', long_name))
        # Check if we generated an alternative option
        if opt and opt.type == 'bool' and opt.alternate:
            val = False
    else:
        opt = g_long_to_opt.get(long_name)
    return (opt, val)


def long_get_arg(name):
    """
    Extract the argument part ARG of a long_name option long_name=ARG.
    """
    long_name = name.split('=')
    assert len(long_name) <= 2
    return long_name[1] if len(long_name) == 2 else None


def long_get_option(name):
    """
    Extract the name of a given long option long=ARG
    """
    return name.split('=')[0]


def get_smt_name(option):
    """
    Determine the name of the option used as SMT option name. If no smt_name is
    given it defaults to the long option name.
    """
    assert option.smt_name or option.long
    return option.smt_name if option.smt_name else long_get_option(option.long)


def is_numeric_cpp_type(ctype):
    """
    Check if given type is a numeric C++ type (this should cover the most
    common cases).
    """
    if ctype in SUPPORTED_CTYPES:
        return True
    elif re.match('u?int[0-9]+_t', ctype):
        return True
    return False


def format_include(include):
    """
    Generate the #include directive for a given header name.
    """
    if '<' in include:
        return '#include {}'.format(include)
    return '#include "{}"'.format(include)


def help_format_options(short_name, long_name):
    """
    Format short and long options for the cmdline documentation
    (--long | -short).
    """
    opts = []
    arg = None
    if long_name:
        opts.append('--{}'.format(long_name))
        long_name = long_name.split('=')
        if len(long_name) > 1:
            arg = long_name[1]

    if short_name:
        if arg:
            opts.append('-{} {}'.format(short_name, arg))
        else:
            opts.append('-{}'.format(short_name))

    return ' | '.join(opts)


def help_format(help_msg, opts):
    """
    Format cmdline documentation (--help) to be 80 chars wide.
    """
    width = 80
    width_opt = 25
    wrapper = \
        textwrap.TextWrapper(width=width - width_opt, break_on_hyphens=False)
    text = wrapper.wrap(help_msg.replace('"', '\\"'))
    if len(opts) > width_opt - 3:
        lines = ['  {}'.format(opts)]
        lines.append(' ' * width_opt + text[0])
    else:
        lines = ['  {}{}'.format(opts.ljust(width_opt - 2), text[0])]
    lines.extend([' ' * width_opt + l for l in text[1:]])
    return ['"{}\\n"'.format(x) for x in lines]


def codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp):
    """
    Generate code for each option module (*_options.{h,cpp})
    """
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

    holder_specs.append(TPL_HOLDER_MACRO.format(id=module.id))

    for option in \
        sorted(module.options, key=lambda x: x.long if x.long else x.name):
        if option.name is None:
            continue

        ### Generate code for {module.name}_options.h
        includes.update([format_include(x) for x in option.includes])

        # Generate option holder macro
        holder_specs.append(TPL_HOLDER_MACRO_ATTR.format(name=option.name))

        # Generate module declaration
        tpl_decl = TPL_OPTION_STRUCT_RO if option.read_only else TPL_OPTION_STRUCT_RW
        decls.append(tpl_decl.format(name=option.name, type=option.type))

        # Generate module specialization
        if not option.read_only:
            specs.append(TPL_DECL_SET.format(name=option.name))
        specs.append(TPL_DECL_OP_BRACKET.format(name=option.name))
        specs.append(TPL_DECL_WAS_SET_BY_USER.format(name=option.name))

        if option.type == 'bool':
            specs.append(TPL_DECL_ASSIGN_BOOL.format(name=option.name))
        else:
            specs.append(TPL_DECL_ASSIGN.format(name=option.name))

        # Generate module inlines
        inls.append(TPL_IMPL_OP_PAR.format(name=option.name))
        inls.append(TPL_IMPL_OPTION_WAS_SET_BY_USER.format(name=option.name))
        if not option.read_only:
            inls.append(TPL_IMPL_OPTION_SET.format(name=option.name))


        ### Generate code for {module.name}_options.cpp

        # Accessors
        if not option.read_only:
            accs.append(TPL_IMPL_SET.format(name=option.name))
        accs.append(TPL_IMPL_OP_BRACKET.format(name=option.name))
        accs.append(TPL_IMPL_WAS_SET_BY_USER.format(name=option.name))

        # Global definitions
        defs.append('struct {name}__option_t {name};'.format(name=option.name))


    filename = os.path.splitext(os.path.split(module.header)[1])[0]
    write_file(dst_dir, '{}.h'.format(filename), tpl_module_h.format(
        filename=filename,
        header=module.header,
        id=module.id,
        includes='\n'.join(sorted(list(includes))),
        holder_spec=' \\\n'.join(holder_specs),
        decls='\n'.join(decls),
        specs='\n'.join(specs),
        inls='\n'.join(inls)
    ))

    write_file(dst_dir, '{}.cpp'.format(filename), tpl_module_cpp.format(
        filename=filename,
        accs='\n'.join(accs),
        defs='\n'.join(defs)
    ))


def docgen(category, name, smt_name, short_name, long_name, ctype, default,
           help_msg, alternate,
           help_common, man_common, man_common_smt, man_common_int,
           help_others, man_others, man_others_smt, man_others_int):
    """
    Generate the documentation for --help and all man pages.
    """

    ### Generate documentation
    if category == 'common':
        doc_cmd = help_common
        doc_man = man_common
        doc_smt = man_common_smt
        doc_int = man_common_int
    else:
        doc_cmd = help_others
        doc_man = man_others
        doc_smt = man_others_smt
        doc_int = man_others_int

    help_msg = help_msg if help_msg else '[undocumented]'
    if category == 'expert':
        help_msg += ' (EXPERTS only)'

    opts = help_format_options(short_name, long_name)

    # Generate documentation for cmdline options
    if opts and category != 'undocumented':
        help_cmd = help_msg
        if ctype == 'bool' and alternate:
            help_cmd += ' [*]'
        doc_cmd.extend(help_format(help_cmd, opts))

        # Generate man page documentation for cmdline options
        doc_man.append('.IP "{}"'.format(opts.replace('-', '\\-')))
        doc_man.append(help_cmd.replace('-', '\\-'))

    # Escape - with \- for man page documentation
    help_msg = help_msg.replace('-', '\\-')

    # Generate man page documentation for smt options
    if smt_name or long_name:
        smtname = smt_name if smt_name else long_get_option(long_name)
        doc_smt.append('.TP\n.B "{}"'.format(smtname))
        if ctype:
            doc_smt.append('({}) {}'.format(ctype, help_msg))
        else:
            doc_smt.append(help_msg)

    # Generate man page documentation for internal options
    if name:
        doc_int.append('.TP\n.B "{}"'.format(name))
        if default:
            assert ctype
            doc_int.append('({}, default = {})'.format(
                ctype,
                default.replace('-', '\\-')))
        elif ctype:
            doc_int.append('({})'.format(ctype))
        doc_int.append('.br\n{}'.format(help_msg))



def docgen_option(option,
                  help_common, man_common, man_common_smt, man_common_int,
                  help_others, man_others, man_others_smt, man_others_int):
    """
    Generate documentation for options.
    """
    docgen(option.category, option.name, option.smt_name,
           option.short, option.long, option.type, option.default,
           option.help, option.alternate,
           help_common, man_common, man_common_smt, man_common_int,
           help_others, man_others, man_others_smt, man_others_int)


def docgen_alias(alias,
                 help_common, man_common, man_common_smt, man_common_int,
                 help_others, man_others, man_others_smt, man_others_int):
    """
    Generate documentation for aliases.
    """
    docgen(alias.category, None, None,
           None, alias.long, None, None,
           alias.help, None,
           help_common, man_common, man_common_smt, man_common_int,
           help_others, man_others, man_others_smt, man_others_int)


def add_getopt_long(long_name, argument_req, getopt_long):
    """
    For each long option we need to add an instance of the option struct in
    order to parse long options (command-line) with getopt_long. Each long
    option is associated with a number that gets incremented by one each time
    we add a new long option.
    """
    value = g_getopt_long_start + len(getopt_long)
    getopt_long.append(
        TPL_GETOPT_LONG.format(
            long_get_option(long_name),
            'required' if argument_req else 'no', value))


def codegen_all_modules(modules, dst_dir, tpl_options, tpl_options_holder,
                        doc_dir, tpl_man_cvc, tpl_man_smt, tpl_man_int):
    """
    Generate code for all option modules (options.cpp, options_holder.h).
    """

    headers_module = []      # generated *_options.h header includes
    headers_handler = set()  # option includes (for handlers, predicates, ...)
    macros_module = []       # option holder macro for options_holder.h
    getopt_short = []        # short options for getopt_long
    getopt_long = []         # long options for getopt_long
    options_smt = []         # all options names accessible via {set,get}-option
    options_getoptions = []  # options for Options::getOptions()
    options_handler = []     # option handler calls
    defaults = []            # default values
    custom_handlers = []     # custom handler implementations assign/assignBool
    help_common = []         # help text for all common options
    help_others = []         # help text for all non-common options
    setoption_handlers = []  # handlers for set-option command
    getoption_handlers = []  # handlers for get-option command

    # other documentation
    man_common = []
    man_others = []
    man_common_smt = []
    man_others_smt = []
    man_common_int = []
    man_others_int = []

    for module in modules:
        headers_module.append(format_include(module.header))
        macros_module.append(TPL_HOLDER_MACRO_NAME.format(id=module.id))

        if module.options or module.aliases:
            help_others.append(
                '"\\nFrom the {} module:\\n"'.format(module.name))
            man_others.append('.SH {} OPTIONS'.format(module.name.upper()))
            man_others_smt.append(
                '.TP\n.I "{} OPTIONS"'.format(module.name.upper()))
            man_others_int.append(man_others_smt[-1])


        for option in \
            sorted(module.options, key=lambda x: x.long if x.long else x.name):
            assert option.type != 'void' or option.name is None
            assert option.name or option.smt_name or option.short or option.long
            argument_req = option.type not in ['bool', 'void']

            docgen_option(option,
                          help_common, man_common, man_common_smt,
                          man_common_int, help_others, man_others,
                          man_others_smt, man_others_int)

            # Generate handler call
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

            # Generate predicate calls
            predicates = []
            if option.predicates:
                if option.type == 'bool':
                    predicates = \
                        ['handler->{}(option, b);'.format(x) \
                            for x in option.predicates]
                else:
                    assert option.type != 'void'
                    predicates = \
                        ['handler->{}(option, retval);'.format(x) \
                            for x in option.predicates]

            # Generate notification calls
            notifications = \
                ['d_handler->{}(option);'.format(x) for x in option.notifies]


            # Generate options_handler and getopt_long
            cases = []
            if option.short:
                cases.append("case '{}':".format(option.short))

                getopt_short.append(option.short)
                if argument_req:
                    getopt_short.append(':')

            if option.long:
                cases.append(
                    'case {}:// --{}'.format(
                        g_getopt_long_start + len(getopt_long),
                        option.long))
                add_getopt_long(option.long, argument_req, getopt_long)

            if cases:
                if option.type == 'bool' and option.name:
                    cases.append(
                        TPL_CALL_ASSIGN_BOOL.format(
                            name=option.name,
                            option='option',
                            value='true'))
                elif option.type != 'void' and option.name:
                    cases.append(
                        TPL_CALL_ASSIGN.format(
                            name=option.name,
                            option='option',
                            value='optionarg'))
                elif handler:
                    cases.append('{};'.format(handler))

                cases.extend(
                    [TPL_PUSHBACK_PREEMPT.format('"{}"'.format(x)) \
                        for x in option.links])
                cases.append('  break;\n')

                options_handler.extend(cases)


            # Generate handlers for setOption/getOption
            if option.smt_name or option.long:
                smtlinks = []
                for link in option.links:
                    m = match_option(link)
                    assert m
                    smtname = get_smt_name(m[0])
                    assert smtname
                    smtlinks.append(
                        TPL_CALL_SET_OPTION.format(
                            smtname=smtname,
                            value='true' if m[1] else 'false'
                        ))

                # Make smt_name and long name available via set/get-option
                keys = set()
                if option.smt_name:
                    keys.add(option.smt_name)
                if option.long:
                    keys.add(long_get_option(option.long))
                assert keys

                cond = ' || '.join(
                    ['key == "{}"'.format(x) for x in sorted(keys)])

                smtname = get_smt_name(option)

                setoption_handlers.append('if({}) {{'.format(cond))
                if option.type == 'bool':
                    setoption_handlers.append(
                        TPL_CALL_ASSIGN_BOOL.format(
                            name=option.name,
                            option='"{}"'.format(smtname),
                            value='optionarg == "true"'))
                elif argument_req and option.name:
                    setoption_handlers.append(
                        TPL_CALL_ASSIGN.format(
                            name=option.name,
                            option='"{}"'.format(smtname)))
                elif option.handler:
                    h = 'handler->{handler}("{smtname}"'
                    if argument_req:
                        h += ', optionarg'
                    h += ');'
                    setoption_handlers.append(
                        h.format(handler=option.handler, smtname=smtname))

                if smtlinks:
                    setoption_handlers.append('\n'.join(smtlinks))
                setoption_handlers.append('return;')
                setoption_handlers.append('}')

                if option.name:
                    getoption_handlers.append(
                        'if ({}) {{'.format(cond))
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
            if option.long and option.type == 'bool' and option.alternate:
                cases = []
                cases.append(
                    'case {}:// --no-{}'.format(
                        g_getopt_long_start + len(getopt_long),
                        option.long))
                cases.append(
                    TPL_CALL_ASSIGN_BOOL.format(
                        name=option.name, option='option', value='false'))
                cases.append('  break;\n')

                options_handler.extend(cases)

                add_getopt_long('no-{}'.format(option.long), argument_req,
                                getopt_long)

            optname = option.smt_name if option.smt_name else option.long
            # collect options available to the SMT-frontend
            if optname:
                options_smt.append('"{}",'.format(optname))

            if option.name:
                # Build options for options::getOptions()
                if optname:
                    # collect SMT option names
                    options_smt.append('"{}",'.format(optname))

                    if option.type == 'bool':
                        s = '{ std::vector<std::string> v; '
                        s += 'v.push_back("{}"); '.format(optname)
                        s += 'v.push_back(std::string('
                        s += 'd_holder->{}'.format(option.name)
                        s += ' ? "true" : "false")); '
                        s += 'opts.push_back(v); }'
                    else:
                        s = '{ std::stringstream ss; '
                        if is_numeric_cpp_type(option.type):
                            s += 'ss << std::fixed << std::setprecision(8); '
                        s += 'ss << d_holder->{}; '.format(option.name)
                        s += 'std::vector<std::string> v; '
                        s += 'v.push_back("{}"); '.format(optname)
                        s += 'v.push_back(ss.str()); '
                        s += 'opts.push_back(v); }'
                    options_getoptions.append(s)


                # Define runBoolPredicates/runHandlerAndPredicates
                tpl = None
                if option.type == 'bool':
                    if predicates:
                        assert handler is None
                        tpl = TPL_RUN_HANDLER_BOOL
                elif option.short or option.long:
                    assert option.type != 'void'
                    assert handler
                    tpl = TPL_RUN_HANDLER
                if tpl:
                    custom_handlers.append(
                        tpl.format(
                            name=option.name,
                            handler=handler,
                            predicates='\n'.join(predicates)
                        ))

                # Define handler assign/assignBool
                tpl = None
                if option.type == 'bool':
                    tpl = TPL_IMPL_ASSIGN_BOOL
                elif option.short or option.long or option.smt_name:
                    tpl = TPL_IMPL_ASSIGN
                if tpl:
                    custom_handlers.append(tpl.format(
                        name=option.name,
                        notifications='\n'.join(notifications)
                    ))

                # Default option values
                default = option.default if option.default else ''
                defaults.append('{}({})'.format(option.name, default))
                defaults.append('{}__setByUser__(false)'.format(option.name))


        for alias in sorted(module.aliases, key=lambda x: x.long):
            argument_req = '=' in alias.long

            options_handler.append(
                'case {}:// --{}'.format(
                    g_getopt_long_start + len(getopt_long), alias.long))

            # If an alias replaces and alternate --no- option, we have to set
            # the corresponding option to false
            if alias.alternate_for:
                assert alias.alternate_for.name
                options_handler.append(
                    TPL_CALL_ASSIGN_BOOL.format(
                        name=alias.alternate_for.name,
                        option='option', value='false'))

            assert alias.links
            arg = long_get_arg(alias.long)
            for link in alias.links:
                arg_link = long_get_arg(link)
                if arg == arg_link:
                    options_handler.append(
                        TPL_PUSHBACK_PREEMPT.format(
                            '"{}"'.format(long_get_option(link))))
                    if argument_req:
                        options_handler.append(
                            TPL_PUSHBACK_PREEMPT.format('optionarg.c_str()'))
                else:
                    options_handler.append(
                        TPL_PUSHBACK_PREEMPT.format('"{}"'.format(link)))

            options_handler.append('  break;\n')

            add_getopt_long(alias.long, argument_req, getopt_long)

            docgen_alias(alias,
                         help_common, man_common, man_common_smt,
                         man_common_int, help_others, man_others,
                         man_others_smt, man_others_int)


    write_file(dst_dir, 'options_holder.h', tpl_options_holder.format(
        headers_module='\n'.join(headers_module),
        macros_module='\n  '.join(macros_module)
    ))

    write_file(dst_dir, 'options.cpp', tpl_options.format(
        headers_module='\n'.join(headers_module),
        headers_handler='\n'.join(sorted(list(headers_handler))),
        custom_handlers='\n'.join(custom_handlers),
        module_defaults=',\n  '.join(defaults),
        help_common='\n'.join(help_common),
        help_others='\n'.join(help_others),
        cmdline_options='\n  '.join(getopt_long),
        options_short=''.join(getopt_short),
        options_handler='\n    '.join(options_handler),
        option_value_begin=g_getopt_long_start,
        option_value_end=g_getopt_long_start + len(getopt_long),
        options_smt='\n  '.join(options_smt),
        options_getoptions='\n  '.join(options_getoptions),
        setoption_handlers='\n'.join(setoption_handlers),
        getoption_handlers='\n'.join(getoption_handlers)
    ))

    write_file(doc_dir, 'cvc4.1', tpl_man_cvc.format(
        man_common='\n'.join(man_common),
        man_others='\n'.join(man_others)
    ))

    write_file(doc_dir, 'SmtEngine.3cvc', tpl_man_smt.format(
        man_common_smt='\n'.join(man_common_smt),
        man_others_smt='\n'.join(man_others_smt)
    ))

    write_file(doc_dir, 'options.3cvc', tpl_man_int.format(
        man_common_internals='\n'.join(man_common_int),
        man_others_internals='\n'.join(man_others_int)
    ))


def lstrip(prefix, s):
    """
    Remove prefix from the beginning of string s.
    """
    return s[len(prefix):] if s.startswith(prefix) else s


def rstrip(suffix, s):
    """
    Remove suffix from the end of string s.
    """
    return s[:-len(suffix)] if s.endswith(suffix) else s


def check_attribs(filename, lineno, req_attribs, valid_attribs, attribs, ctype):
    """
    Check if for a given module/option/alias the defined attributes are valid and
    if all required attributes are defined.
    """
    msg_for = ""
    if 'name' in attribs:
        msg_for = " for '{}'".format(attribs['name'])
    for k in req_attribs:
        if k not in attribs:
            perr(filename, lineno,
                 "required {} attribute '{}' not specified{}".format(
                     ctype, k, msg_for))
    for k in attribs:
        if k not in valid_attribs:
            perr(filename, lineno,
                 "invalid {} attribute '{}' specified{}".format(
                     ctype, k, msg_for))


def check_unique(filename, lineno, value, cache):
    """
    Check if given name is unique in cache.
    """
    if value in cache:
        perr(filename, lineno,
             "'{}' already defined in '{}' at line {}".format(
                 value, cache[value][0], cache[value][1]))
    cache[value] = (filename, lineno + 1)


def check_long(filename, lineno, long_name, ctype=None):
    """
    Check if given long option name is valid.
    """
    global g_long_cache
    if long_name is None:
        return
    if long_name.startswith('--'):
        perr(filename, lineno, 'remove -- prefix from long option')
    r = r'^[0-9a-zA-Z\-=]+$'
    if not re.match(r, long_name):
        perr(filename, lineno,
             "long option '{}' does not match regex criteria '{}'".format(
                 long_name, r))
    name = long_get_option(long_name)
    check_unique(filename, lineno, name, g_long_cache)

    if ctype == 'bool':
        check_unique(filename, lineno, 'no-{}'.format(name), g_long_cache)


def check_links(filename, lineno, links):
    """
    Check if long options defined in links are valid and correctly used.
    """
    global g_long_cache, g_long_arguments
    for link in links:
        long_name = lstrip('no-', lstrip('--', long_get_option(link)))
        if long_name not in g_long_cache:
            perr(filename, lineno,
                 "invalid long option '{}' in links list".format(link))
        # check if long option requires an argument
        if long_name in g_long_arguments and '=' not in link:
            perr(filename, lineno,
                 "linked option '{}' requires an argument".format(link))


def check_alias_attrib(filename, lineno, attrib, value):
    """
    Check alias attribute values. All attribute checks that can be done while
    parsing should be done here.
    """
    if attrib not in ALIAS_ATTR_ALL:
        perr(filename, lineno, "invalid alias attribute '{}'".format(attrib))
    if attrib == 'category':
        if value not in CATEGORY_VALUES:
            perr(filename, lineno, "invalid category value '{}'".format(value))
    elif attrib == 'long':
        pass # Will be checked after parsing is done
    elif attrib == 'links':
        assert isinstance(value, list)
        if not value:
            perr(filename, lineno, 'links list must not be empty')


def check_option_attrib(filename, lineno, attrib, value):
    """
    Check option attribute values. All attribute checks that can be done while
    parsing should be done here.
    """
    global g_smt_cache, g_name_cache, g_short_cache

    if attrib not in OPTION_ATTR_ALL:
        perr(filename, lineno, "invalid option attribute '{}'".format(attrib))

    if attrib == 'category':
        if value not in CATEGORY_VALUES:
            perr(filename, lineno, "invalid category value '{}'".format(value))
    elif attrib == 'type':
        if not value:
            perr(filename, lineno, 'type must not be empty')
    elif attrib == 'long':
        pass # Will be checked after parsing is done
    elif attrib == 'name' and value:
        r = r'^[a-zA-Z]+[0-9a-zA-Z_]*$'
        if not re.match(r, value):
            perr(filename, lineno,
                 "name '{}' does not match regex criteria '{}'".format(
                     value, r))
        check_unique(filename, lineno, value, g_name_cache)
    elif attrib == 'smt_name' and value:
        r = r'^[a-zA-Z]+[0-9a-zA-Z\-_]*$'
        if not re.match(r, value):
            perr(filename, lineno,
                 "smt_name '{}' does not match regex criteria '{}'".format(
                     value, r))
        check_unique(filename, lineno, value, g_smt_cache)
    elif attrib == 'short' and value:
        if value[0].startswith('-'):
            perr(filename, lineno, 'remove - prefix from short option')
        if len(value) != 1:
            perr(filename, lineno, 'short option must be of length 1')
        if not value.isalpha() and not value.isdigit():
            perr(filename, lineno, 'short option must be a character or a digit')
        check_unique(filename, lineno, value, g_short_cache)
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
    elif attrib in ['read_only', 'alternate'] and value is not None:
        if not isinstance(value, bool):
            perr(filename, lineno,
                 "expected true/false instead of '{}' for {}".format(
                     value, attrib))


def check_module_attrib(filename, lineno, attrib, value):
    """
    Check module attribute values. All attribute checks that can be done while
    parsing should be done here.
    """
    global g_module_id_cache
    if attrib not in MODULE_ATTR_ALL:
        perr(filename, lineno, "invalid module attribute '{}'".format(attrib))
    if attrib == 'id':
        if not value:
            perr(filename, lineno, 'module id must not be empty')
        if value in g_module_id_cache:
            perr(filename, lineno,
                 "module id '{}' already defined in '{}' at line {}".format(
                     value,
                     g_module_id_cache[value][0],
                     g_module_id_cache[value][1]))
        g_module_id_cache[value] = (filename, lineno)
        r = r'^[A-Z]+[A-Z_]*$'
        if not re.match(r, value):
            perr(filename, lineno,
                 "module id '{}' does not match regex criteria '{}'".format(
                     value, r))
    elif attrib == 'name':
        if not value:
            perr(filename, lineno, 'module name must not be empty')
    elif attrib == 'header':
        if not value:
            perr(filename, lineno, 'module header must not be empty')
        header_name = \
            'options/{}.h'.format(rstrip('.toml', os.path.basename(filename)))
        if header_name != value:
            perr(filename, lineno,
                 "expected module header '{}' instead of '{}'".format(
                     header_name, value))


def parse_value(filename, lineno, attrib, val):
    """
    Parse attribute values.
    We only allow three types of values:
     - bool   (val either true/false or "true"/"false")
     - string (val starting with ")
     - lists  (val starting with [)
    """
    if val[0] == '"':
        if val[-1] != '"':
            perr(filename, lineno, 'missing closing " for string')
        val = val.lstrip('"').rstrip('"').replace('\\"', '"')

        # for read_only/alternate we allow both true/false and "true"/"false"
        if attrib in ['read_only', 'alternate']:
            if val == 'true':
                return True
            elif val == 'false':
                return False
        return val if val else None
    elif val[0] == '[':
        try:
            val_list = ast.literal_eval(val)
        except SyntaxError as e:
            perr(filename, lineno, 'parsing list: {}'.format(e.msg))
        return val_list
    elif val == 'true':
        return True
    elif val == 'false':
        return False
    else:
        perr(filename, lineno, "invalid value '{}'".format(val))
        return None


def parse_module(filename, file):
    """
    Parse options module file.

    Note: We could use an existing toml parser to parse the configuration
    files.  However, since we only use a very restricted feature set of the
    toml format, we chose to implement our own parser to get better error
    messages.
    """
    module = dict()
    options = []
    aliases = []
    lines = [[x.strip() for x in line.split('=', 1)] for line in file]
    option = None
    alias = None
    option_lines = []
    alias_lines = []
    for i in range(len(lines)):
        assert option is None or alias is None
        line = lines[i]
        # Skip comments
        if line[0].startswith('#'):
            continue
        # Check if a new option/alias starts.
        if len(line) == 1:
            # Create a new option/alias object, save previously created
            if line[0] in ['[[option]]', '[[alias]]']:
                if option:
                    options.append(option)
                    option = None
                if alias:
                    aliases.append(alias)
                    alias = None
                # Create new option dict and save line number where option
                # was defined.
                if line[0] == '[[option]]':
                    assert alias is None
                    option = dict()
                    option_lines.append(i)
                else:
                    # Create new alias dict and save line number where alias
                    # was defined.
                    assert line[0] == '[[alias]]'
                    assert option is None
                    alias = dict()
                    # Save line number where alias was defined
                    alias_lines.append(i)
            elif line[0] != '':
                perr(filename, i, "invalid attribute '{}'".format(line[0]))
        # Parse module/option/alias attributes.
        elif len(line) == 2:
            attrib = line[0]
            value = parse_value(filename, i, attrib, line[1])
            # All attributes we parse are part of the current option.
            if option is not None:
                check_option_attrib(filename, i, attrib, value)
                if attrib in option:
                    perr(filename, i,
                         "duplicate option attribute '{}'".format(attrib))
                assert option is not None
                option[attrib] = value
            # All attributes we parse are part of the current alias.
            elif alias is not None:
                check_alias_attrib(filename, i, attrib, value)
                if attrib in alias:
                    perr(filename, i,
                         "duplicate alias attribute '{}'".format(attrib))
                assert alias is not None
                alias[attrib] = value
            # All other attributes are part of the module.
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

    # Check if parsed module attributes are valid and if all required
    # attributes are defined.
    check_attribs(filename, 1,
                  MODULE_ATTR_REQ, MODULE_ATTR_ALL, module, 'module')
    res = Module(module)

    # Check parsed option/alias attributes and create option/alias objects and
    # associate file name and line number with options/aliases (required for
    # better error reporting).
    assert len(option_lines) == len(options)
    assert len(alias_lines) == len(aliases)
    for i in range(len(options)):
        attribs = options[i]
        lineno = option_lines[i]
        check_attribs(filename, lineno,
                      OPTION_ATTR_REQ, OPTION_ATTR_ALL, attribs, 'option')
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
        option.lineno = lineno
        option.filename = filename
        res.options.append(option)

    for i in range(len(aliases)):
        attribs = aliases[i]
        lineno = alias_lines[i]
        check_attribs(filename, lineno,
                      ALIAS_ATTR_REQ, ALIAS_ATTR_ALL, attribs, 'alias')
        alias = Alias(attribs)
        alias.lineno = lineno
        alias.filename = filename
        res.aliases.append(alias)

    return res


def usage():
    print('mkoptions.py <tpl-src> <tpl-doc> <dst> <toml>+')
    print('')
    print('  <tpl-src> location of all *_template.{cpp,h} files')
    print('  <tpl-doc> location of all *_template documentation files')
    print('  <dst>     destination directory for the generated files')
    print('  <toml>+   one or more *_optios.toml files')
    print('')


def mkoptions_main():
    if len(sys.argv) < 5:
        usage()
        die('missing arguments')

    src_dir = sys.argv[1]
    doc_dir = sys.argv[2]
    dst_dir = sys.argv[3]
    filenames = sys.argv[4:]

    # Check if given directories exist.
    for d in [src_dir, doc_dir, dst_dir]:
        if not os.path.isdir(d):
            usage()
            die("'{}' is not a directory".format(d))

    # Check if given configuration files exist.
    for file in filenames:
        if not os.path.exists(file):
            die("configuration file '{}' does not exist".format(file))

    # Read source code template files from source directory.
    tpl_module_h = read_tpl(src_dir, 'module_template.h')
    tpl_module_cpp = read_tpl(src_dir, 'module_template.cpp')
    tpl_options = read_tpl(src_dir, 'options_template.cpp')
    tpl_options_holder = read_tpl(src_dir, 'options_holder_template.h')

    # Read documentation template files from documentation directory.
    tpl_man_cvc = read_tpl(doc_dir, 'cvc4.1_template')
    tpl_man_smt = read_tpl(doc_dir, 'SmtEngine.3cvc_template')
    tpl_man_int = read_tpl(doc_dir, 'options.3cvc_template')

    # Parse files, check attributes and create module/option objects
    modules = []
    for filename in filenames:
        with open(filename, 'r') as file:
            module = parse_module(filename, file)
            # Check if long options are valid and unique.  First populate
            # g_long_cache with option.long and --no- alternatives if
            # applicable.
            for option in module.options:
                check_long(option.filename, option.lineno, option.long,
                           option.type)
                if option.long:
                    g_long_to_opt[long_get_option(option.long)] = option
                    # Add long option that requires an argument
                    if option.type not in ['bool', 'void']:
                        g_long_arguments.add(long_get_option(option.long))
            modules.append(module)

    # Check if alias.long is unique and check if alias.long defines an alias
    # for an alternate (--no-<long>) option for existing option <long>.
    for module in modules:
        for alias in module.aliases:
            # If an alias defines a --no- alternative for an existing boolean
            # option, we do not create the alternative for the option, but use
            # the alias instead.
            if alias.long.startswith('no-'):
                m = match_option(alias.long)
                if m[0] and m[0].type == 'bool':
                    m[0].alternate = False
                    alias.alternate_for = m[0]
                    del g_long_cache[alias.long]
            check_long(alias.filename, alias.lineno, alias.long)
            # Add long option that requires an argument
            if '=' in alias.long:
                g_long_arguments.add(long_get_option(alias.long))

    # Check if long options in links are valid (that needs to be done after all
    # long options are available).
    for module in modules:
        for option in module.options:
            check_links(option.filename, option.lineno, option.links)
        for alias in module.aliases:
            check_links(alias.filename, alias.lineno, alias.links)

    # Create *_options.{h,cpp} in destination directory
    for module in modules:
        codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp)

    # Create options.cpp and options_holder.h in destination directory
    codegen_all_modules(modules,
                        dst_dir, tpl_options, tpl_options_holder,
                        doc_dir, tpl_man_cvc, tpl_man_smt, tpl_man_int)



if __name__ == "__main__":
    mkoptions_main()
    sys.exit(0)
