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
        - options_public_template.cpp
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
MODULE_ATTR_ALL = MODULE_ATTR_REQ + ['option']

OPTION_ATTR_REQ = ['category', 'type']
OPTION_ATTR_ALL = OPTION_ATTR_REQ + [
    'name', 'short', 'long', 'alias',
    'default', 'alternate', 'mode',
    'handler', 'predicates', 'includes', 'minimum', 'maximum',
    'help', 'help_mode'
]

CATEGORY_VALUES = ['common', 'expert', 'regular', 'undocumented']

################################################################################
################################################################################
# utility functions


def wrap_line(s, indent, **kwargs):
    """Wrap and indent text and forward all other kwargs to textwrap.wrap()."""
    return ('\n' + ' ' * indent).join(
        textwrap.wrap(s, width=80 - indent, **kwargs))


def concat_format(s, objs):
    """Helper method to render a string for a list of object"""
    return '\n'.join([s.format(**o.__dict__) for o in objs])


def all_options(modules, sorted=False):
    """Helper to iterate all options from all modules."""
    if sorted:
        options = []
        for m in modules:
            options = options + [(m, o) for o in m.options]
        options.sort(key=lambda t: t[1])
        yield from options
    else:
        for module in modules:
            if not module.options:
                continue
            for option in module.options:
                yield module, option


### Other globals

g_getopt_long_start = 256

### Source code templates

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

# Option specific methods

TPL_IMPL_OP_PAR = 'inline {type} {name}() {{ return Options::current().{module}.{name}; }}'

# Mode templates
TPL_DECL_MODE_ENUM = '''
enum class {type}
{{
  {values}
}};

static constexpr size_t {type}__numValues = {nvalues};
'''

TPL_DECL_MODE_FUNC = 'std::ostream& operator<<(std::ostream& os, {type} mode);'
TPL_IMPL_MODE_FUNC = TPL_DECL_MODE_FUNC[:-1] + '''
{{
  switch(mode) {{{cases}
    default:
      Unreachable();
  }}
  return os;
}}'''

TPL_IMPL_MODE_CASE = \
"""
    case {type}::{enum}:
      return os << "{type}::{enum}";"""

TPL_DECL_MODE_HANDLER = '{type} stringTo{type}(const std::string& optarg);'
TPL_IMPL_MODE_HANDLER = TPL_DECL_MODE_HANDLER[:-1] + '''
{{
  {cases}
  else if (optarg == "help")
  {{
    std::cerr << {help};
    std::exit(1);
  }}
  throw OptionException(std::string("unknown option for --{long}: `") +
                        optarg + "'.  Try --{long}=help.");
}}'''

TPL_MODE_HANDLER_CASE = \
"""if (optarg == "{name}")
  {{
    return {type}::{enum};
  }}"""


def get_module_headers(modules):
    """Render includes for module headers"""
    return concat_format('#include "{header}"', modules)


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
    """Represents on option."""
    def __init__(self, d):
        self.__dict__ = dict((k, None) for k in OPTION_ATTR_ALL)
        self.includes = []
        self.predicates = []
        for (attr, val) in d.items():
            assert attr in self.__dict__
            if attr == 'alternate' or val:
                self.__dict__[attr] = val
        if self.type == 'bool' and self.alternate is None:
            self.alternate = True
        self.long_name = None
        self.long_opt = None
        if self.long:
            r = self.long.split('=', 1)
            self.long_name = r[0]
            if len(r) > 1:
                self.long_opt = r[1]
        self.names = set()
        if self.long_name:
            self.names.add(self.long_name)
        if self.alias:
            self.names.update(self.alias)

    def __lt__(self, other):
        if self.long_name and other.long_name:
            return self.long_name < other.long_name
        if self.long_name: return True
        return False

################################################################################
# stuff for options/options_public.cpp


def generate_public_includes(modules):
    """Generates the list of includes for options_public.cpp."""
    headers = set()
    for _, option in all_options(modules):
        headers.update([format_include(x) for x in option.includes])
    return '\n'.join(headers)


def generate_getnames_impl(modules):
    """Generates the implementation for options::getNames()."""
    names = set()
    for _, option in all_options(modules):
        names.update(option.names)
    res = ', '.join(map(lambda s: '"' + s + '"', sorted(names)))
    return wrap_line(res, 4, break_on_hyphens=False)


def generate_get_impl(modules):
    """Generates the implementation for options::get()."""
    res = []
    for module, option in all_options(modules, True):
        if not option.name or not option.long:
            continue
        cond = ' || '.join(['name == "{}"'.format(x) for x in option.names])
        ret = None
        if option.type == 'bool':
            ret = 'return options.{}.{} ? "true" : "false";'.format(
                module.id, option.name)
        elif option.type == 'std::string':
            ret = 'return options.{}.{};'.format(module.id, option.name)
        elif is_numeric_cpp_type(option.type):
            ret = 'return std::to_string(options.{}.{});'.format(
                module.id, option.name)
        else:
            ret = '{{ std::stringstream s; s << options.{}.{}; return s.str(); }}'.format(
                module.id, option.name)
        res.append('if ({}) {}'.format(cond, ret))
    return '\n  '.join(res)


def _set_handlers(option):
    """Render handler call for options::set()."""
    optname = option.long_name if option.long else ""
    if option.handler:
        if option.type == 'void':
            return 'opts.handler().{}("{}", name)'.format(
                option.handler, optname)
        else:
            return 'opts.handler().{}("{}", name, optionarg)'.format(
                option.handler, optname)
    elif option.mode:
        return 'stringTo{}(optionarg)'.format(option.type)
    return 'handlers::handleOption<{}>("{}", name, optionarg)'.format(
        option.type, optname)


def _set_predicates(option):
    """Render predicate calls for options::set()."""
    if option.type == 'void':
        return []
    optname = option.long_name if option.long else ""
    assert option.type != 'void'
    res = []
    if option.minimum:
        res.append(
            'opts.handler().checkMinimum("{}", name, value, static_cast<{}>({}));'
            .format(optname, option.type, option.minimum))
    if option.maximum:
        res.append(
            'opts.handler().checkMaximum("{}", name, value, static_cast<{}>({}));'
            .format(optname, option.type, option.maximum))
    res += [
        'opts.handler().{}("{}", name, value);'.format(x, optname)
        for x in option.predicates
    ]
    return res


TPL_SET = '''    opts.{module}.{name} = {handler};
    opts.{module}.{name}WasSetByUser = true;'''
TPL_SET_PRED = '''    auto value = {handler};
    {predicates}
    opts.{module}.{name} = value;
    opts.{module}.{name}WasSetByUser = true;'''


def generate_set_impl(modules):
    """Generates the implementation for options::set()."""
    res = []
    for module, option in all_options(modules, True):
        if not option.long:
            continue
        cond = ' || '.join(['name == "{}"'.format(x) for x in option.names])
        predicates = _set_predicates(option)
        if res:
            res.append('  }} else if ({}) {{'.format(cond))
        else:
            res.append('if ({}) {{'.format(cond))
        if option.name and not (option.handler and option.mode):
            if predicates:
                res.append(
                    TPL_SET_PRED.format(module=module.id,
                                        name=option.name,
                                        handler=_set_handlers(option),
                                        predicates='\n    '.join(predicates)))
            else:
                res.append(
                    TPL_SET.format(module=module.id,
                                   name=option.name,
                                   handler=_set_handlers(option)))
        elif option.handler:
            h = '  opts.handler().{handler}("{smtname}", name'
            if option.type not in ['bool', 'void']:
                h += ', optionarg'
            h += ');'
            res.append(
                h.format(handler=option.handler, smtname=option.long_name))
    return '\n'.join(res)


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
            'alternate': option.alternate,
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
                if v == '':
                    continue
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
    return ctype in ['int64_t', 'uint64_t', 'double']


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
        if 'help' not in attrib:
            continue
        if value == option.default and attrib['name'] != "default":
            text.append('+ {} (default)'.format(attrib['name']))
        else:
            text.append('+ {}'.format(attrib['name']))
        text.extend('  {}'.format(x) for x in wrapper.wrap(attrib['help']))

    return '\n         '.join('"{}\\n"'.format(x) for x in text)


def codegen_module(module, dst_dir, tpls):
    """
    Generate code for each option module (*_options.{h,cpp})
    """
    # *_options.h / *.options.cpp
    includes = set()
    holder_specs = []
    option_names = []
    wrap_funs = []
    default_decl = []
    default_impl = []
    mode_decl = []
    mode_impl = []

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
        if option.long:
            long_name = option.long.split('=')[0]
        else:
            long_name = ""
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
        wrap_funs.append(TPL_IMPL_OP_PAR.format(module=module.id, name=option.name, type=option.type))


        ### Generate code for {module.name}_options.cpp

        # Accessors
        default_impl.append(TPL_IMPL_SET_DEFAULT.format(module=module.id, name=option.name, funcname=capoptionname, type=option.type))

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
            names = set()
            cases = []
            for value, attrib in option.mode.items():
                assert len(attrib) == 1
                name = attrib[0]['name']
                if name in names:
                    die("multiple modes with the name '{}' for option '{}'".
                        format(name, option.long))
                else:
                    names.add(name)

                cases.append(
                    TPL_MODE_HANDLER_CASE.format(
                        name=name,
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

    data = {
        'id_cap': module.id_cap,
        'id': module.id,
        'includes': '\n'.join(sorted(list(includes))),
        'holder_spec': '\n'.join(holder_specs),
        'option_names': '\n'.join(option_names),
        'wrap_funs': '\n'.join(wrap_funs),
        'defaults_decl': ''.join(default_decl),
        'modes_decl': '\n'.join(mode_decl),
        'header': module.header,
        'defaults_impl': '\n'.join(default_impl),
        'modes_impl': '\n'.join(mode_impl),
    }

    for tpl in tpls:
        filename = tpl['output'].replace('module', module.filename)
        write_file(dst_dir, filename, tpl['content'].format(**data))


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
        if option.alternate:
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


def codegen_all_modules(modules, build_dir, dst_dir, tpls):
    """
    Generate code for all option modules (options.cpp).
    """

    headers_module = []      # generated *_options.h header includes
    headers_handler = set()  # option includes (for handlers, predicates, ...)
    getopt_short = []        # short options for getopt_long
    getopt_long = []         # long options for getopt_long
    options_get_info = []    # code for getOptionInfo()
    options_handler = []     # option handler calls
    help_common = []         # help text for all common options
    help_others = []         # help text for all non-common options
    setoption_handlers = []  # handlers for set-option command

    assign_impls = []

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

            # Generate options_handler and getopt_long
            cases = []
            if option.short:
                cases.append("case '{0}': // -{0}".format(option.short))

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
                if option.type == 'bool':
                    cases.append(
                        '  solver.setOption("{}", "true");'.format(option.long_name)
                        )
                elif option.type == 'void':
                    cases.append(
                        '  solver.setOption("{}", "");'.format(option.long_name))
                else:
                    cases.append(
                        '  solver.setOption("{}", optionarg);'.format(option.long_name))

                cases.append('  break;')

                options_handler.extend(cases)


            # Generate handlers for setOption/getOption
            if option.long:
                # Make long and alias names available via set/get-option
                names = set()
                if option.long:
                    names.add(long_get_option(option.long))
                if option.alias:
                    names.update(option.alias)
                assert names

                cond = ' || '.join(
                    ['name == "{}"'.format(x) for x in sorted(names)])

                # Generate code for getOptionInfo
                if option.alias:
                    alias = ', '.join(map(lambda s: '"{}"'.format(s), option.alias))
                else:
                    alias = ''
                if option.name:
                    constr = None
                    fmt = {
                        'type': option.type,
                        'value': 'opts.{}.{}'.format(module.id, option.name),
                        'default': option.default if option.default else '{}()'.format(option.type),
                        'minimum': option.minimum if option.minimum else '{}',
                        'maximum': option.maximum if option.maximum else '{}',
                    }
                    if option.type in ['bool', 'std::string']:
                        constr = 'OptionInfo::ValueInfo<{type}>{{{default}, {value}}}'.format(**fmt)
                    elif option.type == 'double' or is_numeric_cpp_type(option.type):
                        constr = 'OptionInfo::NumberInfo<{type}>{{{default}, {value}, {minimum}, {maximum}}}'.format(**fmt)
                    elif option.mode:
                        values = ', '.join(map(lambda s: '"{}"'.format(s), sorted(option.mode.keys())))
                        assert(option.default)
                        constr = 'OptionInfo::ModeInfo{{"{default}", {value}, {{ {modes} }}}}'.format(**fmt, modes=values)
                    else:
                        constr = 'OptionInfo::VoidInfo{}'
                    options_get_info.append('if ({}) return OptionInfo{{"{}", {{{alias}}}, opts.{}.{}WasSetByUser, {}}};'.format(cond, long_get_option(option.long), module.id, option.name, constr, alias=alias))
                else:
                    options_get_info.append('if ({}) return OptionInfo{{"{}", {{{alias}}}, false, OptionInfo::VoidInfo{{}}}};'.format(cond, long_get_option(option.long), alias=alias))

            # Add --no- alternative options for boolean options
            if option.long and option.alternate:
                cases = []
                cases.append(
                    'case {}: // --no-{}'.format(
                        g_getopt_long_start + len(getopt_long),
                        option.long))

                add_getopt_long('no-{}'.format(option.long), argument_req,
                                getopt_long)
                if option.alias:
                    for alias in option.alias:
                        cases.append(
                            'case {}: // --no-{}'.format(
                                g_getopt_long_start + len(getopt_long),
                                alias))
                        add_getopt_long('no-{}'.format(alias), argument_req,
                                getopt_long)

                cases.append(
                        '  solver.setOption("{}", "false");'.format(option.long_name)
                        )
                cases.append('  break;')
                options_handler.extend(cases)

    data = {
        'holder_fwd_decls': get_holder_fwd_decls(modules),
        'holder_mem_decls': get_holder_mem_decls(modules),
        'holder_ref_decls': get_holder_ref_decls(modules),
        'headers_module': get_module_headers(modules),
        'headers_handler': '\n'.join(sorted(list(headers_handler))),
        'holder_mem_inits': get_holder_mem_inits(modules),
        'holder_ref_inits': get_holder_ref_inits(modules),
        'holder_mem_copy': get_holder_mem_copy(modules),
        # options/options_public.cpp
        'options_includes': generate_public_includes(modules),
        'getnames_impl': generate_getnames_impl(modules),
        'get_impl': generate_get_impl(modules),
        'set_impl': generate_set_impl(modules),
        'cmdline_options': '\n  '.join(getopt_long),
        'help_common': '\n'.join(help_common),
        'help_others': '\n'.join(help_others),
        'options_handler': '\n    '.join(options_handler),
        'options_short': ''.join(getopt_short),
        'options_get_info': '\n  '.join(sorted(options_get_info)),
    }
    for tpl in tpls:
        write_file(dst_dir, tpl['output'], tpl['content'].format(**data))


    if os.path.isdir('{}/docs/'.format(build_dir)):
        sphinxgen.render('{}/docs/'.format(build_dir), 'options_generated.rst')


class Checker:
    """Performs a variety of sanity checks on options and option modules, and
    constructs `Module` and `Option` from dictionaries."""
    def __init__(self):
        self.__filename = None
        self.__long_cache = {}

    def perr(self, msg, *args, **kwargs):
        """Print an error and die."""
        if 'option' in kwargs:
            msg = "option '{}' {}".format(kwargs['option'], msg)
        msg = 'parse error in {}: {}'.format(self.__filename, msg)
        die(msg.format(*args, **kwargs))

    def __check_module_attribs(self, req, valid, module):
        """Check the attributes of an option module."""
        for k in req:
            if k not in module:
                self.perr("required module attribute '{}' not specified", k)
        for k in module:
            if k not in valid:
                self.perr("invalid module attribute '{}' specified", k)

    def __check_option_attribs(self, req, valid, option):
        """Check the attributes of an option."""
        if 'name' in option:
            name = option['name']
        else:
            name = option.get('long', '--')
        for k in req:
            if k not in option:
                self.perr(
                    "required option attribute '{}' not specified for '{}'", k,
                    name)
        for k in option:
            if k not in valid:
                self.perr("invalid option attribute '{}' specified for '{}'",
                          k, name)

    def __check_option_long(self, option, long):
        """Check a long argument of an option (name and uniqueness)."""
        if long.startswith('--'):
            self.perr("remove '--' prefix from '{}'", long, option=option)
        r = r'^[0-9a-zA-Z\-]+$'
        if not re.match(r, long):
            self.perr("long '{}' does not match '{}'", long, r, option=option)
        if long in self.__long_cache:
            file = self.__long_cache[long]
            self.perr("long '{}' was already defined in '{}'",
                      long,
                      file,
                      option=option)
        self.__long_cache[long] = self.__filename

    def check_module(self, module, filename):
        """Check the given module and return a `Module` object."""
        self.__filename = os.path.basename(filename)
        self.__check_module_attribs(MODULE_ATTR_REQ, MODULE_ATTR_ALL, module)
        return Module(module, filename)

    def check_option(self, option):
        """Check the option module and return an `Option` object."""
        self.__check_option_attribs(OPTION_ATTR_REQ, OPTION_ATTR_ALL, option)
        o = Option(option)
        if o.category not in CATEGORY_VALUES:
            self.perr("has invalid category '{}'", o.category, option=o)
        if o.mode and not o.help_mode:
            self.perr('defines modes but no help_mode', option=o)
        if o.mode and not o.default:
            self.perr('mode option has no default', option=o)
        if o.mode and o.default and o.default not in o.mode.keys():
            self.perr("invalid default value '{}'", o.default, option=o)
        if o.short and not o.long:
            self.perr("has short '{}' but no long", o.short, option=o)
        if o.category != 'undocumented' and not o.help:
            self.perr("of type '{}' has no help text", o.category, option=o)
        if o.alias and not o.long:
            self.perr('has aliases but no long', option=o)
        if o.alternate and o.type != 'bool':
            self.perr('is alternate but not bool', option=o)
        if o.long:
            self.__check_option_long(o, o.long_name)
            if o.alternate:
                self.__check_option_long(o, 'no-' + o.long_name)
            if o.type in ['bool', 'void'] and '=' in o.long:
                self.perr('must not have an argument description', option=o)
            if o.type not in ['bool', 'void'] and not '=' in o.long:
                self.perr("needs argument description ('{}=...')",
                          o.long,
                          option=o)
            if o.alias:
                for alias in o.alias:
                    self.__check_option_long(o, alias)
                    if o.alternate:
                        self.__check_option_long(o, 'no-' + alias)
        return o


def usage():
    """Print the command-line usage"""
    print('mkoptions.py <src> <build> <dst> <toml>+')
    print('')
    print('  <src>     base source directory of all toml files')
    print('  <build>   build directory to write the generated sphinx docs')
    print('  <dst>     base destination directory for all generated files')
    print('  <toml>+   one or more *_options.toml files')
    print('')


def mkoptions_main():
    if len(sys.argv) < 5:
        usage()
        die('missing arguments')

    # Load command line arguments
    _, src_dir, build_dir, dst_dir, *filenames = sys.argv

    # Check if given directories exist.
    for d in [src_dir, dst_dir]:
        if not os.path.isdir(d):
            usage()
            die("'{}' is not a directory".format(d))

    # Check if given configuration files exist.
    for file in filenames:
        if not os.path.exists(file):
            die("configuration file '{}' does not exist".format(file))
    
    module_tpls = [
        {'input': 'options/module_template.h'},
        {'input': 'options/module_template.cpp'},
    ]
    global_tpls = [
        {'input': 'options/options_template.h'},
        {'input': 'options/options_template.cpp'},
        {'input': 'options/options_public_template.cpp'},
        {'input': 'main/options_template.cpp'},
    ]

    # Load all template files
    for tpl in module_tpls + global_tpls:
        tpl['output'] = tpl['input'].replace('_template', '')
        tpl['content'] = read_tpl(src_dir, tpl['input'])

    # Parse and check toml files
    checker = Checker()
    modules = []
    for filename in filenames:
        data = toml.load(filename)
        module = checker.check_module(data, filename)
        if 'option' in data:
            module.options = sorted(
                [checker.check_option(a) for a in data['option']])
        modules.append(module)

    # Generate code
    for module in modules:
        codegen_module(module, dst_dir, module_tpls)
    codegen_all_modules(modules, build_dir, dst_dir, global_tpls)


if __name__ == "__main__":
    mkoptions_main()
    sys.exit(0)
