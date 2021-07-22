#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Mathias Preiner, Everett Maus
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

"""
    Generate option handling code and documentation in one pass. The generated
    files are only written to the destination file if the contents of the file
    has changed (in order to avoid global re-compilation if only single option
    files changed).

    mkoptions.py <tpl-src> <dst> <toml>+

      <tpl-src> location of all *_template.{cpp,h} files
      <dst>     destination directory for the generated source code files
      <toml>+   one or more *_options.toml files


    Directory <tpl-src> must contain:
        - options_template.cpp
        - module_template.cpp
        - module_template.h

    <toml>+ must be the list of all *.toml option configuration files from
    the src/options directory.


    The script generates the following files:
        - <dst>/MODULE_options.h
        - <dst>/MODULE_options.cpp
        - <dst>/options.cpp
"""

import os
import re
import sys
import textwrap
import toml

### Allowed attributes for module/option

MODULE_ATTR_REQ = ['id', 'name']
MODULE_ATTR_ALL = MODULE_ATTR_REQ + ['option', 'public']

OPTION_ATTR_REQ = ['category', 'type']
OPTION_ATTR_ALL = OPTION_ATTR_REQ + [
    'name', 'short', 'long', 'alias',
    'default', 'alternate', 'mode',
    'handler', 'predicates', 'includes',
    'help', 'help_mode'
]

CATEGORY_VALUES = ['common', 'expert', 'regular', 'undocumented']
SUPPORTED_CTYPES = ['int', 'unsigned', 'unsigned long', 'double']

### Other globals

g_long_cache = dict()      # maps long options to filename/fileno

g_getopt_long_start = 256

### Source code templates

TPL_ASSIGN = '''
void assign_{module}_{name}(Options& opts, const std::string& option, const std::string& optionarg) {{
  auto value = {handler};
  {predicates}
  opts.{module}.{name} = value;
  opts.{module}.{name}WasSetByUser = true;
  Trace("options") << "user assigned option {name} = " << value << std::endl;
}}'''

TPL_ASSIGN_BOOL = '''
void assign_{module}_{name}(Options& opts, const std::string& option, bool value) {{
  {predicates}
  opts.{module}.{name} = value;
  opts.{module}.{name}WasSetByUser = true;
  Trace("options") << "user assigned option {name} = " << value << std::endl;
}}'''

TPL_CALL_ASSIGN_BOOL = '    assign_{module}_{name}(opts, {option}, {value});'
TPL_CALL_ASSIGN = '    assign_{module}_{name}(opts, {option}, optionarg);'

TPL_CALL_SET_OPTION = 'setOption(std::string("{smtname}"), ("{value}"));'

TPL_GETOPT_LONG = '{{ "{}", {}_argument, nullptr, {} }},'

TPL_HOLDER_MACRO_ATTR = '''  {type} {name};
  bool {name}WasSetByUser = false;'''

TPL_HOLDER_MACRO_ATTR_DEF = '''  {type} {name} = {default};
  bool {name}WasSetByUser = false;'''

TPL_DECL_SET_DEFAULT = 'void setDefault{funcname}(Options& opts, {type} value);'
TPL_IMPL_SET_DEFAULT = TPL_DECL_SET_DEFAULT[:-1] + '''
{{
    if (!opts.{module}.{name}WasSetByUser) {{
        opts.{module}.{name} = value;
    }}
}}'''

TPL_NAME_DECL = 'static constexpr const char* {name}__name = "{long_name}";'

TPL_OPTION_STRUCT_RW = \
"""extern struct {name}__option_t
{{
  typedef {type} type;
  type operator()() const;
}} thread_local {name};"""

# Option specific methods

TPL_IMPL_OP_PAR = \
"""inline {type} {name}__option_t::operator()() const
{{ return Options::current().{module}.{name}; }}"""

# Mode templates
TPL_DECL_MODE_ENUM = \
"""
enum class {type}
{{
  {values}
}};

static constexpr size_t {type}__numValues = {nvalues};
"""

TPL_DECL_MODE_FUNC = \
"""
std::ostream& operator<<(std::ostream& os, {type} mode);"""

TPL_IMPL_MODE_FUNC = TPL_DECL_MODE_FUNC[:-len(";")] + \
"""
{{
  switch(mode) {{{cases}
    default:
      Unreachable();
  }}
  return os;
}}
"""

TPL_IMPL_MODE_CASE = \
"""
    case {type}::{enum}:
      return os << "{type}::{enum}";"""

TPL_DECL_MODE_HANDLER = \
"""
{type} stringTo{type}(const std::string& optarg);"""

TPL_IMPL_MODE_HANDLER = TPL_DECL_MODE_HANDLER[:-1] + \
"""
{{
  {cases}
  else if (optarg == "help")
  {{
    std::cerr << {help};
    std::exit(1);
  }}
  throw OptionException(std::string("unknown option for --{long}: `") +
                        optarg + "'.  Try --{long}=help.");
}}
"""

TPL_MODE_HANDLER_CASE = \
"""if (optarg == "{name}")
  {{
    return {type}::{enum};
  }}"""

def concat_format(s, objs):
    """Helper method to render a string for a list of object"""
    return '\n'.join([s.format(**o.__dict__) for o in objs])


def get_holder_fwd_decls(modules):
    """Render forward declaration of holder structs"""
    return concat_format('  struct Holder{id_cap};', modules)


def get_holder_mem_decls(modules):
    """Render declarations of holder members of the Option class"""
    return concat_format('    std::unique_ptr<options::Holder{id_cap}> d_{id};', modules)


def get_holder_mem_inits(modules):
    """Render initializations of holder members of the Option class"""
    return concat_format('        d_{id}(std::make_unique<options::Holder{id_cap}>()),', modules)


def get_holder_ref_inits(modules):
    """Render initializations of holder references of the Option class"""
    return concat_format('        {id}(*d_{id}),', modules)


def get_holder_mem_copy(modules):
    """Render copy operation of holder members of the Option class"""
    return concat_format('      *d_{id} = *options.d_{id};', modules)


def get_holder_ref_decls(modules):
    """Render reference declarations for holder members of the Option class"""
    return concat_format('  options::Holder{id_cap}& {id};', modules)


def get_handler(option):
    """Render handler call for assignment functions"""
    optname = option.long_name if option.long else ""
    if option.handler:
        if option.type == 'void':
            return 'opts.handler().{}("{}", option)'.format(option.handler, optname)
        else:
            return 'opts.handler().{}("{}", option, optionarg)'.format(option.handler, optname)
    elif option.mode:
        return 'stringTo{}(optionarg)'.format(option.type)
    elif option.type != 'bool':
        return 'handleOption<{}>("{}", option, optionarg)'.format(option.type, optname)
    return None


def get_predicates(option):
    """Render predicate calls for assignment functions"""
    if not option.predicates:
        return []
    optname = option.long_name if option.long else ""
    assert option.type != 'void'
    return ['opts.handler().{}("{}", option, value);'.format(x, optname)
            for x in option.predicates]

class Module(object):
    """Options module.

    An options module represents a MODULE_options.toml option configuration
    file and contains lists of options.
    """
    def __init__(self, d, filename):
        self.__dict__ = {k: d.get(k, None) for k in MODULE_ATTR_ALL}
        self.options = []
        self.id = self.id.lower()
        self.id_cap = self.id.upper()
        self.filename = os.path.splitext(os.path.split(filename)[-1])[0]
        self.header = os.path.join('options', '{}.h'.format(self.filename))


class Option(object):
    """Module option.

    An instance of this class corresponds to an option defined in a
    MODULE_options.toml configuration file specified via [[option]].
    """
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in OPTION_ATTR_ALL)
        self.includes = []
        self.predicates = []
        self.alternate = True    # add --no- alternative long option for bool
        self.filename = None
        for (attr, val) in d.items():
            assert attr in self.__dict__
            if attr == 'alternate' or val:
                self.__dict__[attr] = val
        self.long_name = None
        self.long_opt = None
        if self.long:
            r = self.long.split('=', 1)
            self.long_name = r[0]
            if len(r) > 1:
                self.long_opt = r[1]


class SphinxGenerator:
    def __init__(self):
        self.common = []
        self.others = {}

    def add(self, module, option):
        if option.category == 'undocumented':
            return
        if not option.long and not option.short:
            return
        names = []
        if option.long:
            if option.long_opt:
                names.append('--{}={}'.format(option.long_name, option.long_opt))
            else:
                names.append('--{}'.format(option.long_name))
        
        if option.alias:
            if option.long_opt:
                names.extend(['--{}={}'.format(a, option.long_opt) for a in option.alias])
            else:
                names.extend(['--{}'.format(a) for a in option.alias])

        if option.short:
            if option.long_opt:
                names.append('-{} {}'.format(option.short, option.long_opt))
            else:
                names.append('-{}'.format(option.short))
        
        modes = None
        if option.mode:
            modes = {}
            for _, data in option.mode.items():
                assert len(data) == 1
                data = data[0]
                modes[data['name']] = data.get('help', '')

        data = {
            'name': names,
            'help': option.help,
            'expert': option.category == 'expert',
            'alternate': option.type == 'bool' and option.alternate,
            'help_mode': option.help_mode,
            'modes': modes,
        }

        if option.category == 'common':
            self.common.append(data)
        else:
            if module.name not in self.others:
                self.others[module.name] = []
            self.others[module.name].append(data)
    
    def __render_option(self, res, opt):
        desc = '``{}``'
        val = '    {}'
        if opt['expert']:
            res.append('.. admonition:: This option is intended for Experts only!')
            res.append('    ')
            desc = '    ' + desc
            val = '    ' + val

        if opt['alternate']:
            desc += ' (also ``--no-*``)'
        res.append(desc.format(' | '.join(opt['name'])))
        res.append(val.format(opt['help']))

        if opt['modes']:
            res.append(val.format(''))
            res.append(val.format(opt['help_mode']))
            res.append(val.format(''))
            for k, v in opt['modes'].items():
                res.append(val.format(':{}: {}'.format(k, v)))
        res.append('    ')


    def render(self, dstdir, filename):
        res = []

        res.append('Most Commonly-Used cvc5 Options')
        res.append('===============================')
        for opt in self.common:
            self.__render_option(res, opt)

        res.append('')
        res.append('Additional cvc5 Options')
        res.append('=======================')
        for module in self.others:
            res.append('')
            res.append('{} Module'.format(module))
            res.append('-' * (len(module) + 8))
            for opt in self.others[module]:
                self.__render_option(res, opt)

        write_file(dstdir, filename, '\n'.join(res))


def die(msg):
    sys.exit('[error] {}'.format(msg))


def perr(filename, msg, option=None):
    msg_suffix = ''
    if option:
        if option.name:
            msg_suffix = "option '{}' ".format(option.name)
        else:
            msg_suffix = "option '{}' ".format(option.long)
    die('parse error in {}: {}{}'.format(filename, msg, msg_suffix))


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
                    return
        with open(fname, 'w') as file:
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


def long_get_option(name):
    """
    Extract the name of a given long option long=ARG
    """
    return name.split('=')[0]


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


def help_format_options(option):
    """
    Format short and long options for the cmdline documentation
    (--long | --alias | -short).
    """
    opts = []
    if option.long:
        if option.long_opt:
            opts.append('--{}={}'.format(option.long_name, option.long_opt))
        else:
            opts.append('--{}'.format(option.long_name))
    
    if option.alias:
        if option.long_opt:
            opts.extend(['--{}={}'.format(a, option.long_opt) for a in option.alias])
        else:
            opts.extend(['--{}'.format(a) for a in option.alias])

    if option.short:
        if option.long_opt:
            opts.append('-{} {}'.format(option.short, option.long_opt))
        else:
            opts.append('-{}'.format(option.short))

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

def help_mode_format(option):
    """
    Format help message for mode options.
    """
    assert option.help_mode
    assert option.mode

    wrapper = textwrap.TextWrapper(width=78, break_on_hyphens=False)
    text = ['{}'.format(x) for x in wrapper.wrap(option.help_mode)]

    optname, optvalue = option.long.split('=')
    text.append('Available {}s for --{} are:'.format(
                optvalue.lower(), optname))

    for value, attrib in option.mode.items():
        assert len(attrib) == 1
        attrib = attrib[0]
        if value == option.default and attrib['name'] != "default":
            text.append('+ {} (default)'.format(attrib['name']))
        else:
            text.append('+ {}'.format(attrib['name']))
        if 'help' in attrib:
            text.extend('  {}'.format(x) for x in wrapper.wrap(attrib['help']))

    return '\n         '.join('"{}\\n"'.format(x) for x in text)


def codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp):
    """
    Generate code for each option module (*_options.{h,cpp})
    """
    # *_options.h / *.options.cpp
    includes = set()
    holder_specs = []
    option_names = []
    decls = []
    specs = []
    inls = []
    default_decl = []
    default_impl = []
    mode_decl = []
    mode_impl = []

    # *_options_.cpp
    accs = []
    defs = []

    for option in \
        sorted(module.options, key=lambda x: x.long if x.long else x.name):
        if option.name is None:
            continue

        ### Generate code for {module.name}_options.h
        includes.update([format_include(x) for x in option.includes])

        # Generate option holder macro
        if option.default:
            default = option.default
            if option.mode and option.type not in default:
                default = '{}::{}'.format(option.type, default)
            holder_specs.append(TPL_HOLDER_MACRO_ATTR_DEF.format(type=option.type, name=option.name, default=default))
        else:
            holder_specs.append(TPL_HOLDER_MACRO_ATTR.format(type=option.type, name=option.name))

        # Generate module declaration
        tpl_decl = TPL_OPTION_STRUCT_RW
        if option.long:
            long_name = option.long.split('=')[0]
        else:
            long_name = ""
        decls.append(tpl_decl.format(name=option.name, type=option.type, long_name = long_name))
        option_names.append(TPL_NAME_DECL.format(name=option.name, type=option.type, long_name = long_name))

        capoptionname = option.name[0].capitalize() + option.name[1:]

        # Generate module specialization
        default_decl.append(TPL_DECL_SET_DEFAULT.format(module=module.id, name=option.name, funcname=capoptionname, type=option.type))

        if option.long and option.type not in ['bool', 'void'] and \
           '=' not in option.long:
            die("module '{}': option '{}' with type '{}' needs an argument " \
                "description ('{}=...')".format(
                    module.id, option.long, option.type, option.long))
        elif option.long and option.type in ['bool', 'void'] and \
             '=' in option.long:
            die("module '{}': option '{}' with type '{}' must not have an " \
                "argument description".format(
                    module.id, option.long, option.type))

        # Generate module inlines
        inls.append(TPL_IMPL_OP_PAR.format(module=module.id, name=option.name, type=option.type))


        ### Generate code for {module.name}_options.cpp

        # Accessors
        default_impl.append(TPL_IMPL_SET_DEFAULT.format(module=module.id, name=option.name, funcname=capoptionname, type=option.type))

        # Global definitions
        defs.append('thread_local struct {name}__option_t {name};'.format(name=option.name))

        if option.mode:
            values = option.mode.keys()
            mode_decl.append(
                TPL_DECL_MODE_ENUM.format(
                    type=option.type,
                    values=',\n  '.join(values),
                    nvalues=len(values)))
            mode_decl.append(TPL_DECL_MODE_FUNC.format(type=option.type))
            cases = [TPL_IMPL_MODE_CASE.format(
                        type=option.type, enum=x) for x in values]
            mode_impl.append(
                TPL_IMPL_MODE_FUNC.format(
                    type=option.type,
                    cases=''.join(cases)))

            # Generate str-to-enum handler
            cases = []
            for value, attrib in option.mode.items():
                assert len(attrib) == 1
                cases.append(
                    TPL_MODE_HANDLER_CASE.format(
                        name=attrib[0]['name'],
                        type=option.type,
                        enum=value))
            assert option.long
            assert cases
            mode_decl.append(TPL_DECL_MODE_HANDLER.format(type=option.type))
            mode_impl.append(
                TPL_IMPL_MODE_HANDLER.format(
                    type=option.type,
                    cases='\n  else '.join(cases),
                    help=help_mode_format(option),
                    long=option.long.split('=')[0]))

    if module.public:
        visibility_include = '#include "cvc5_public.h"'
    else:
        visibility_include = '#include "cvc5_private.h"'

    filename = os.path.splitext(os.path.split(module.header)[1])[0]
    write_file(dst_dir, '{}.h'.format(filename), tpl_module_h.format(
        visibility_include=visibility_include,
        id_cap=module.id_cap,
        id=module.id,
        includes='\n'.join(sorted(list(includes))),
        holder_spec='\n'.join(holder_specs),
        decls='\n'.join(decls),
        specs='\n'.join(specs),
        option_names='\n'.join(option_names),
        inls='\n'.join(inls),
        defaults='\n'.join(default_decl),
        modes=''.join(mode_decl)))

    write_file(dst_dir, '{}.cpp'.format(filename), tpl_module_cpp.format(
        header=module.header,
        id=module.id,
        accs='\n'.join(accs),
        defaults='\n'.join(default_impl),
        defs='\n'.join(defs),
        modes=''.join(mode_impl)))


def docgen_option(option, help_common, help_others):
    """
    Generate documentation for options.
    """

    if option.category == 'undocumented':
        return

    help_msg = option.help
    if option.category == 'expert':
        help_msg += ' (EXPERTS only)'

    opts = help_format_options(option)

    # Generate documentation for cmdline options
    if opts and option.category != 'undocumented':
        help_cmd = help_msg
        if option.type == 'bool' and option.alternate:
            help_cmd += ' [*]'
        
        res = help_format(help_cmd, opts)

        if option.category == 'common':
            help_common.extend(res)
        else:
            help_others.extend(res)


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


def codegen_all_modules(modules, build_dir, dst_dir, tpl_options_h, tpl_options_cpp):
    """
    Generate code for all option modules (options.cpp, options_holder.h).
    """

    headers_module = []      # generated *_options.h header includes
    headers_handler = set()  # option includes (for handlers, predicates, ...)
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

    sphinxgen = SphinxGenerator()

    for module in modules:
        headers_module.append(format_include(module.header))

        if module.options:
            help_others.append(
                '"\\nFrom the {} module:\\n"'.format(module.name))

        for option in \
            sorted(module.options, key=lambda x: x.long if x.long else x.name):
            assert option.type != 'void' or option.name is None
            assert option.name or option.short or option.long
            mode_handler = option.handler and option.mode
            argument_req = option.type not in ['bool', 'void']

            docgen_option(option, help_common, help_others)

            sphinxgen.add(module, option)

            # Generate handler call
            handler = get_handler(option)

            # Generate predicate calls
            predicates = get_predicates(option)

            # Generate options_handler and getopt_long
            cases = []
            if option.short:
                cases.append("case '{}':".format(option.short))

                getopt_short.append(option.short)
                if argument_req:
                    getopt_short.append(':')

            if option.long:
                cases.append(
                    'case {}: // --{}'.format(
                        g_getopt_long_start + len(getopt_long),
                        option.long))
                add_getopt_long(option.long, argument_req, getopt_long)
                if option.alias:
                    for alias in option.alias:
                        cases.append(
                            'case {}: // --{}'.format(
                                g_getopt_long_start + len(getopt_long),
                                alias))
                        add_getopt_long(alias, argument_req, getopt_long)

            if cases:
                if option.type == 'bool' and option.name:
                    cases.append(
                        TPL_CALL_ASSIGN_BOOL.format(
                            module=module.id,
                            name=option.name,
                            option='option',
                            value='true'))
                elif option.type != 'void' and option.name and not mode_handler:
                    cases.append(
                        TPL_CALL_ASSIGN.format(
                            module=module.id,
                            name=option.name,
                            option='option',
                            value='optionarg'))
                elif handler:
                    cases.append('{};'.format(handler))

                cases.append('  break;')

                options_handler.extend(cases)


            # Generate handlers for setOption/getOption
            if option.long:
                # Make long and alias names available via set/get-option
                keys = set()
                if option.long:
                    keys.add(long_get_option(option.long))
                if option.alias:
                    keys.update(option.alias)
                assert keys

                cond = ' || '.join(
                    ['key == "{}"'.format(x) for x in sorted(keys)])

                setoption_handlers.append('if({}) {{'.format(cond))
                if option.type == 'bool':
                    setoption_handlers.append(
                        TPL_CALL_ASSIGN_BOOL.format(
                            module=module.id,
                            name=option.name,
                            option='key',
                            value='optionarg == "true"'))
                elif argument_req and option.name and not mode_handler:
                    setoption_handlers.append(
                        TPL_CALL_ASSIGN.format(
                            module=module.id,
                            name=option.name,
                            option='key'))
                elif option.handler:
                    h = 'handler->{handler}("{smtname}", key'
                    if argument_req:
                        h += ', optionarg'
                    h += ');'
                    setoption_handlers.append(
                        h.format(handler=option.handler, smtname=option.long_name))

                setoption_handlers.append('return;')
                setoption_handlers.append('}')

                if option.name:
                    getoption_handlers.append(
                        'if ({}) {{'.format(cond))
                    if option.type == 'bool':
                        getoption_handlers.append(
                            'return options.{}.{} ? "true" : "false";'.format(module.id, option.name))
                    elif option.type == 'std::string':
                        getoption_handlers.append(
                            'return options.{}.{};'.format(module.id, option.name))
                    elif is_numeric_cpp_type(option.type):
                        getoption_handlers.append(
                            'return std::to_string(options.{}.{});'.format(module.id, option.name))
                    else:
                        getoption_handlers.append('std::stringstream ss;')
                        getoption_handlers.append(
                            'ss << options.{}.{};'.format(module.id, option.name))
                        getoption_handlers.append('return ss.str();')
                    getoption_handlers.append('}')


            # Add --no- alternative options for boolean options
            if option.long and option.type == 'bool' and option.alternate:
                cases = []
                cases.append(
                    'case {}:// --no-{}'.format(
                        g_getopt_long_start + len(getopt_long),
                        option.long))

                add_getopt_long('no-{}'.format(option.long), argument_req,
                                getopt_long)
                if option.alias:
                    for alias in option.alias:
                        cases.append(
                            'case {}:// --no-{}'.format(
                                g_getopt_long_start + len(getopt_long),
                                alias))
                        add_getopt_long('no-{}'.format(alias), argument_req,
                                getopt_long)

                cases.append(
                    TPL_CALL_ASSIGN_BOOL.format(
                        module=module.id,
                        name=option.name, option='option', value='false'))
                cases.append('  break;')
                options_handler.extend(cases)

            optname = option.long
            # collect options available to the SMT-frontend
            if optname:
                options_smt.append('"{}",'.format(optname))

            if option.name:
                # Build options for options::getOptions()
                if optname:
                    # collect SMT option names
                    options_smt.append('"{}",'.format(optname))

                    if option.type == 'bool':
                        s = 'opts.push_back({{"{}", {}.{} ? "true" : "false"}});'.format(
                            optname, module.id, option.name)
                    elif is_numeric_cpp_type(option.type):
                        s = 'opts.push_back({{"{}", std::to_string({}.{})}});'.format(
                            optname, module.id, option.name)
                    else:
                        s = '{{ std::stringstream ss; ss << {}.{}; opts.push_back({{"{}", ss.str()}}); }}'.format(
                            module.id, option.name, optname)
                    options_getoptions.append(s)


                # Define handler assign/assignBool
                if not mode_handler:
                    if option.type == 'bool':
                        custom_handlers.append(TPL_ASSIGN_BOOL.format(
                            module=module.id,
                            name=option.name,
                            handler=handler,
                            predicates='\n'.join(predicates)
                        ))
                    elif option.short or option.long:
                        custom_handlers.append(TPL_ASSIGN.format(
                            module=module.id,
                            name=option.name,
                            handler=handler,
                            predicates='\n'.join(predicates)
                        ))

                # Default option values
                default = option.default if option.default else ''
                # Prepend enum name
                if option.mode and option.type not in default:
                    default = '{}::{}'.format(option.type, default)
                defaults.append('{}({})'.format(option.name, default))
                defaults.append('{}WasSetByUser(false)'.format(option.name))

    write_file(dst_dir, 'options.h', tpl_options_h.format(
        holder_fwd_decls=get_holder_fwd_decls(modules),
        holder_mem_decls=get_holder_mem_decls(modules),
        holder_ref_decls=get_holder_ref_decls(modules),
    ))

    write_file(dst_dir, 'options.cpp', tpl_options_cpp.format(
        headers_module='\n'.join(headers_module),
        headers_handler='\n'.join(sorted(list(headers_handler))),
        holder_mem_copy=get_holder_mem_copy(modules),
        holder_mem_inits=get_holder_mem_inits(modules),
        holder_ref_inits=get_holder_ref_inits(modules),
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

    if os.path.isdir('{}/docs/'.format(build_dir)):
        sphinxgen.render('{}/docs/'.format(build_dir), 'options_generated.rst')


def check_attribs(filename, req_attribs, valid_attribs, attribs, ctype):
    """
    Check if for a given module/option the defined attributes are valid and
    if all required attributes are defined.
    """
    msg_for = ""
    if 'name' in attribs:
        msg_for = " for '{}'".format(attribs['name'])
    elif 'long' in attribs:
        msg_for = " for '{}'".format(attribs['long'])
    for k in req_attribs:
        if k not in attribs:
            perr(filename,
                 "required {} attribute '{}' not specified{}".format(
                     ctype, k, msg_for))
    for k in attribs:
        if k not in valid_attribs:
            perr(filename,
                 "invalid {} attribute '{}' specified{}".format(
                     ctype, k, msg_for))


def check_unique(filename, value, cache):
    """
    Check if given name is unique in cache.
    """
    if value in cache:
        perr(filename,
             "'{}' already defined in '{}'".format(value, cache[value]))
    else:
        cache[value] = filename


def check_long(filename, option, long_name, ctype=None):
    """
    Check if given long option name is valid.
    """
    global g_long_cache
    if long_name is None:
        return
    if long_name.startswith('--'):
        perr(filename, 'remove -- prefix from long', option)
    r = r'^[0-9a-zA-Z\-=]+$'
    if not re.match(r, long_name):
        perr(filename,
             "long '{}' does not match regex criteria '{}'".format(
                 long_name, r), option)
    name = long_get_option(long_name)
    check_unique(filename, name, g_long_cache)

    if ctype == 'bool':
        check_unique(filename, 'no-{}'.format(name), g_long_cache)


def parse_module(filename, module):
    """
    Parse options module file.

    Note: We could use an existing toml parser to parse the configuration
    files.  However, since we only use a very restricted feature set of the
    toml format, we chose to implement our own parser to get better error
    messages.
    """
    # Check if parsed module attributes are valid and if all required
    # attributes are defined.
    check_attribs(filename,
                  MODULE_ATTR_REQ, MODULE_ATTR_ALL, module, 'module')
    res = Module(module, filename)

    if 'option' in module:
        for attribs in module['option']:
            check_attribs(filename,
                          OPTION_ATTR_REQ, OPTION_ATTR_ALL, attribs, 'option')
            option = Option(attribs)
            if option.mode and not option.help_mode:
                perr(filename, 'defines modes but no help_mode', option)
            if option.mode and option.default and \
                    option.default not in option.mode.keys():
                perr(filename,
                     "invalid default value '{}'".format(option.default),
                     option)
            if option.short and not option.long:
                perr(filename,
                     "short option '{}' specified but no long option".format(
                         option.short),
                     option)
            if option.type == 'bool' and option.handler:
                perr(filename,
                     'defining handlers for bool options is not allowed',
                     option)
            if option.category != 'undocumented' and not option.help:
                perr(filename,
                     'help text required for {} options'.format(option.category),
                     option)
            option.filename = filename
            res.options.append(option)

    return res


def usage():
    print('mkoptions.py <tpl-src> <dst> <toml>+')
    print('')
    print('  <tpl-src> location of all *_template.{cpp,h} files')
    print('  <build>   build directory')
    print('  <dst>     destination directory for the generated files')
    print('  <toml>+   one or more *_optios.toml files')
    print('')


def mkoptions_main():
    if len(sys.argv) < 5:
        usage()
        die('missing arguments')

    src_dir = sys.argv[1]
    build_dir = sys.argv[2]
    dst_dir = sys.argv[3]
    filenames = sys.argv[4:]

    # Check if given directories exist.
    for d in [src_dir, dst_dir]:
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
    tpl_options_h = read_tpl(src_dir, 'options_template.h')
    tpl_options_cpp = read_tpl(src_dir, 'options_template.cpp')

    # Parse files, check attributes and create module/option objects
    modules = []
    for filename in filenames:
        module = parse_module(filename, toml.load(filename))

        # Check if long options are valid and unique.  First populate
        # g_long_cache with option.long and --no- alternatives if
        # applicable.
        for option in module.options:
            check_long(filename, option, option.long, option.type)
        modules.append(module)

    # Create *_options.{h,cpp} in destination directory
    for module in modules:
        codegen_module(module, dst_dir, tpl_module_h, tpl_module_cpp)

    # Create options.cpp in destination directory
    codegen_all_modules(modules, build_dir, dst_dir, tpl_options_h, tpl_options_cpp)



if __name__ == "__main__":
    mkoptions_main()
    sys.exit(0)
