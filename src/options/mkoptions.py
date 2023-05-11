#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

    mkoptions.py <src> <build> <dst> <toml>+

      <src>     base source directory of all toml files
      <build>   build directory to write the generated sphinx docs
      <dst>     base destination directory for all generated files
      <toml>+   one or more *_options.toml files


    This script expects the following files (within <src>):

      - <src>/main/options_template.cpp
      - <src>/options/module_template.cpp
      - <src>/options/module_template.h
      - <src>/options/options_public_template.cpp
      - <src>/options/options_template.cpp
      - <src>/options/options_template.h

    <toml>+ must be the list of all *.toml option configuration files.


    This script generates the following files:
      - <dst>/main/options.cpp
      - <dst>/options/<module>_options.cpp (for every toml file)
      - <dst>/options/<module>_options.h (for every toml file)
      - <dst>/options/options_public.cpp
      - <dst>/options/options.cpp
      - <dst>/options/options.h
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
    'name', 'short', 'long', 'alias', 'default', 'alternate', 'mode',
    'handler', 'predicates', 'includes', 'minimum', 'maximum', 'help',
    'help_mode'
]

CATEGORY_VALUES = ['common', 'expert', 'regular', 'undocumented']

################################################################################
################################################################################
# utility functions


def wrap_line(s, indent, **kwargs):
    """Wrap and indent text and forward all other kwargs to textwrap.wrap()."""
    return ('\n' + ' ' * indent).join(
        textwrap.wrap(s, width=80 - indent, **kwargs))


def concat_format(s, objs, glue='\n'):
    """Helper method to render a string for a list of object"""
    return glue.join([s.format(**o.__dict__) for o in objs])


def format_include(include):
    """Generate the #include directive for a given header name."""
    if '<' in include:
        return '#include {}'.format(include)
    return '#include "{}"'.format(include)


def is_numeric_cpp_type(ctype):
    """Check if given type is a numeric type (double, int64_t or uint64_t)."""
    return ctype in ['int64_t', 'uint64_t', 'double']


def die(msg):
    """Exit with the given error message."""
    sys.exit('[error] {}'.format(msg))


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


def write_file(directory, name, content):
    """Write content to `directory/name`. If the file exists, only overwrite it
    when the content would actually change."""
    fname = os.path.join(directory, name)
    try:
        if os.path.isfile(fname):
            with open(fname, 'r') as file:
                if content == file.read():
                    return
        with open(fname, 'w') as file:
            file.write(content)
    except IOError:
        die("Could not write to '{}'".format(fname))


def read_tpl(directory, name):
    """Read a (custom) template file from `directory/name`. Expects placeholders
    of the form `${varname}$` and turns them into `{varname}` while all other
    curly braces are replaced by double curly braces. Thus, the result is
    suitable for `.format()` with kwargs being used."""
    fname = os.path.join(directory, name)
    try:
        with open(fname, 'r') as file:
            res = file.read()
            res = res.replace('{', '{{').replace('}', '}}')
            return res.replace('${', '').replace('}$', '')
    except IOError:
        die("Could not find '{}'. Aborting.".format(fname))


################################################################################
################################################################################
# classes to represent modules and options


class Module(object):
    """Represents one options module from one <module>_options.toml file."""
    def __init__(self, d, filename):
        self.__dict__ = {k: d.get(k, None) for k in MODULE_ATTR_ALL}
        self.options = []
        self.id = self.id.lower()
        self.id_cap = self.id.upper()
        self.id_capitalized = self.id.capitalize()
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
        if self.name:
            self.name_capitalized = self.name[0].capitalize() + self.name[1:]
        if self.long:
            r = self.long.split('=', 1)
            self.long_name = r[0]
            if len(r) > 1:
                self.long_opt = r[1]
        self.fqdefault = self.default
        if self.mode and self.type not in self.default:
            self.fqdefault = '{}::{}'.format(self.type, self.default)
        self.names = set()
        if self.long_name:
            self.names.add(self.long_name)
        if self.alias:
            self.names.update(self.alias)
        if self.mode:
            self.mode_name = { k: v[0]['name'] for k,v in self.mode.items() }
            self.mode_help = { k: v[0].get('help', None) for k,v in self.mode.items() }

    def __lt__(self, other):
        if self.long_name and other.long_name:
            return self.long_name < other.long_name
        if self.long_name: return True
        return False

    def __str__(self):
        return self.long_name if self.long_name else self.name

    def enum_name(self):
        return str(self).replace("-","_").upper()


################################################################################
################################################################################
# code generation functions

################################################################################
# for options/options.h


def generate_holder_fwd_decls(modules):
    """Render forward declaration of holder structs"""
    return concat_format('  struct Holder{id_cap}; // include "{header}" if this is an incomplete type', modules)


def generate_holder_mem_decls(modules):
    """Render declarations of holder members of the Option class"""
    return concat_format(
        '    std::unique_ptr<options::Holder{id_cap}> d_{id};', modules)


def generate_holder_ref_decls(modules):
    """Render reference declarations for holder members of the Option class"""
    return concat_format('''  const options::Holder{id_cap}& {id};
  options::Holder{id_cap}& write{id_capitalized}();''', modules)


################################################################################
# for options/options.cpp


def generate_module_headers(modules):
    """Render includes for module headers"""
    return concat_format('#include "{header}"', modules)


def generate_holder_mem_inits(modules):
    """Render initializations of holder members of the Option class"""
    return concat_format(
        '        d_{id}(std::make_unique<options::Holder{id_cap}>()),',
        modules)


def generate_holder_ref_inits(modules):
    """Render initializations of holder references of the Option class"""
    return concat_format('        {id}(*d_{id}),', modules)


def generate_write_functions(modules):
    """Render write functions for holders within the Option class"""
    return concat_format('''  options::Holder{id_cap}& Options::write{id_capitalized}()
  {{
    return *d_{id};
  }}
''', modules)


def generate_holder_mem_copy(modules):
    """Render copy operation of holder members of the Option class"""
    return concat_format('      *d_{id} = *options.d_{id};', modules)


################################################################################
# for options/options_public.cpp


def generate_public_includes(modules):
    """Generates the list of includes for options_public.cpp."""
    headers = set()
    headers.add(format_include("<unordered_map>"))
    for _, option in all_options(modules):
        headers.update([format_include(x) for x in option.includes])
    return '\n'.join(headers)


def generate_option_enum_and_table(modules):
    """
    Generate an enum class OptionEnum with one variant for each option.
    Also, generate a map NAME_TO_ENUM from string names to enum variants.

    This enum is used to branch (in C++) on an option string name.
    First, you lookup the enum in the map.
    Then, you switch-case on the enum, which generates a jump table.

    When we measured, this was about 5x faster than a huge if-else chain.
    It would probably be even faster with a better hash function.
    """
    res = []
    res.append('enum class OptionEnum {')
    for module, option in all_options(modules, True):
        if not option.long:
            continue
        res.append('  {n},'.format(n=option.enum_name()))
    res.append('};')
    res.append('const std::unordered_map<std::string, OptionEnum> NAME_TO_ENUM = {')
    for module, option in all_options(modules, True):
        if not option.long:
            continue
        for name in option.names:
            res.append('  {{ \"{}\", OptionEnum::{} }},'
                       .format(name, option.enum_name()))
    res.append('};')
    return '\n    '.join(res)


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
    res.append('auto it = NAME_TO_ENUM.find(name);')
    res.append('if (it == NAME_TO_ENUM.end()) {')
    res.append('  throw OptionException(\"Unrecognized option key or setting: \" + name);')
    res.append('}')
    res.append('switch (it->second) {')
    for module, option in all_options(modules, True):
        if not option.name or not option.long:
            continue
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
        res.append('  case OptionEnum::{}: {}'.format(option.enum_name(), ret))
    res.append('  default:'.format(option.enum_name()))
    res.append('  {')
    res.append('    throw OptionException(\"Ungettable option key or setting: \" + name);')
    res.append('  }')
    res.append('}')
    return '\n    '.join(res)


def _set_handlers(option):
    """Render handler call for options::set()."""
    if option.handler:
        return 'opts.handler().{}(name, optionarg)'.format(option.handler)
    elif option.mode:
        return 'stringTo{}(optionarg)'.format(option.type)
    return 'handlers::handleOption<{}>(name, optionarg)'.format(option.type)


def _set_predicates(module, option):
    """Render predicate calls for options::set()."""
    res = []
    if option.minimum:
        res.append(
            'opts.handler().checkMinimum(name, value, static_cast<{}>({}));'
            .format(option.type, option.minimum))
    if option.maximum:
        res.append(
            'opts.handler().checkMaximum(name, value, static_cast<{}>({}));'
            .format(option.type, option.maximum))
    res += [
        'opts.handler().{}(name, value);'.format(x) for x in option.predicates
    ]
    if module.id == 'printer':
        res.append('ioutils::setDefault{}(value);'.format(option.name_capitalized))

    return res


def generate_set_impl(modules):
    """Generates the implementation for options::set()."""
    res = []
    res.append('auto it = NAME_TO_ENUM.find(name);')
    res.append('if (it == NAME_TO_ENUM.end()) {')
    res.append('  throw OptionException(\"Unrecognized option key or setting: \" + name);')
    res.append('}')
    res.append('switch (it->second) {')
    for module, option in all_options(modules, True):
        if not option.long:
            continue
        res.append('  case OptionEnum::{}:'.format(option.enum_name()))
        res.append('  {')
        res.append('    auto value = {};'.format(_set_handlers(option)))
        for pred in _set_predicates(module, option):
            res.append('    {}'.format(pred))
        if option.name:
            res.append('    opts.write{module}().{name} = value;'.format(
                module=module.id_capitalized, name=option.name))
            res.append('    opts.write{module}().{name}WasSetByUser = true;'.format(
                module=module.id_capitalized, name=option.name))
        res.append('    break;')
        res.append('  }')
    res.append('}')
    return '\n    '.join(res)


def generate_getinfo_impl(modules):
    """Generates the implementation for options::getInfo()."""
    res = []
    res.append('auto it = NAME_TO_ENUM.find(name);')
    res.append('if (it == NAME_TO_ENUM.end()) {')
    res.append('  throw OptionException(\"Unrecognized option key or setting: \" + name);')
    res.append('}')
    res.append('switch (it->second) {')
    for module, option in all_options(modules, True):
        if not option.long:
            continue
        constr = None
        fmt = {
            'name': option.long_name,
            'alias': '',
            'type': option.type,
            'value': 'opts.{}.{}'.format(module.id, option.name),
            'setbyuser': 'opts.{}.{}WasSetByUser'.format(module.id, option.name),
            'default': option.default if option.default else '{}()'.format(option.type),
            'minimum': option.minimum if option.minimum else '{}',
            'maximum': option.maximum if option.maximum else '{}',
        }
        if option.alias:
            fmt['alias'] = ', '.join(map(lambda s: '"{}"'.format(s), option.alias))
        if not option.name:
            fmt['setbyuser'] = 'false'
            constr = 'OptionInfo::VoidInfo{{}}'
        elif option.type in ['bool', 'std::string']:
            constr = 'OptionInfo::ValueInfo<{type}>{{{default}, {value}}}'
        elif option.type == 'double' or is_numeric_cpp_type(option.type):
            constr = 'OptionInfo::NumberInfo<{type}>{{{default}, {value}, {minimum}, {maximum}}}'
        elif option.mode:
            modes = { key: value[0]['name'] for key,value in option.mode.items() }
            fmt['modes'] = ', '.join(['"{}"'.format(s) for s in sorted(modes.values())])
            fmt['default'] = modes[fmt['default']]
            constr = 'OptionInfo::ModeInfo{{"{default}", {value}, {{ {modes} }}}}'
        else:
            constr = 'OptionInfo::VoidInfo{{}}'
        res.append("  case OptionEnum::{}:".format(option.enum_name()))
        line = '    return OptionInfo{{"{name}", {{{alias}}}, {setbyuser}, ' + constr + '}};'
        res.append(line.format(**fmt))
    res.append("}")
    return '\n  '.join(res)


################################################################################
# for options/<module>.h


def generate_module_includes(module):
    includes = set()
    for option in module.options:
        if option.name is None:
            continue
        includes.update([format_include(x) for x in option.includes])
    return '\n'.join(sorted(includes))


TPL_MODE_DECL = '''enum class {type}
{{
  {values},
  __MAX_VALUE = {maxvalue}
}};
std::ostream& operator<<(std::ostream& os, {type} mode);
{type} stringTo{type}(const std::string& optarg);
'''


def generate_module_mode_decl(module):
    """Generates the declarations of mode enums and utility functions."""
    res = []
    for option in module.options:
        if not option.mode:
            continue
        values = list(option.mode.keys())
        res.append(
            TPL_MODE_DECL.format(type=option.type,
                                 values=wrap_line(', '.join(values), 2),
                                 maxvalue=values[-1]))
    return '\n'.join(res)


def generate_module_holder_decl(module):
    res = []
    for option in module.options:
        if option.name is None:
            continue
        if option.fqdefault:
            res.append('{} {} = {};'.format(option.type, option.name, option.fqdefault))
        else:
            res.append('{} {};'.format(option.type, option.name))
        res.append('bool {}WasSetByUser = false;'.format(option.name))
    return '\n  '.join(res)

################################################################################
# for options/<module>.cpp

TPL_MODE_STREAM_OPERATOR = '''std::ostream& operator<<(std::ostream& os, {type} mode)
{{
  switch(mode)
  {{
    {cases}
    default: Unreachable();
  }}
  return os;
}}'''

TPL_MODE_TO_STRING = '''{type} stringTo{type}(const std::string& optarg)
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


def _module_mode_help(option):
    """Format help message for mode options."""
    assert option.help_mode
    assert option.mode

    text = ['R"FOOBAR(']
    text.append('  ' + wrap_line(option.help_mode, 2, break_on_hyphens=False))
    text.append('Available {}s for --{} are:'.format(option.long_opt.lower(),
                                                     option.long_name))

    for value, attrib in option.mode.items():
        assert len(attrib) == 1
        attrib = attrib[0]
        if 'help' not in attrib:
            continue
        if value == option.default and attrib['name'] != "default":
            text.append('+ {} (default)'.format(attrib['name']))
        else:
            text.append('+ {}'.format(attrib['name']))
        text.append('  '
                    + wrap_line(attrib['help'], 2, break_on_hyphens=False))
    text.append(')FOOBAR"')
    return '\n'.join(text)


def generate_module_mode_impl(module):
    """Generates the declarations of mode enums and utility functions."""
    res = []
    for option in module.options:
        if not option.mode:
            continue
        cases = [
            'case {type}::{enum}: return os << "{name}";'.format(
                type=option.type, enum=enum, name=info[0]['name'])
            for enum, info in option.mode.items()
        ]
        res.append(
            TPL_MODE_STREAM_OPERATOR.format(type=option.type,
                                            cases='\n    '.join(cases)))

        # Generate str-to-enum handler
        names = set()
        cases = []
        for value, attrib in option.mode.items():
            assert len(attrib) == 1
            name = attrib[0]['name']
            if name in names:
                die("multiple modes with the name '{}' for option '{}'".format(
                    name, option.long))
            else:
                names.add(name)

            cases.append(
                'if (optarg == "{name}") return {type}::{enum};'.format(
                    name=name, type=option.type, enum=value))
        assert option.long
        assert cases
        res.append(
            TPL_MODE_TO_STRING.format(type=option.type,
                                      cases='\n  else '.join(cases),
                                      help=_module_mode_help(option),
                                      long=option.long_name))
    return '\n'.join(res)


################################################################################
# for main/options.cpp


def _add_cmdoption(option, name, opts, next_id):
    fmt = {
        'name': name,
        'arg': 'no' if option.type == 'bool' else 'required',
        'next_id': next_id
    }
    opts.append(
        '{{ "{name}", {arg}_argument, nullptr, {next_id} }},'.format(**fmt))


def generate_parsing(modules):
    """Generates the implementation for main::parseInternal() and matching
    options definitions suitable for getopt_long(). Returns a tuple with:
    - short options description (passed as third argument to getopt_long)
    - long options description (passed as fourth argument to getopt_long)
    - handler code that turns getopt_long return value to a setOption call
    """
    short = ""
    opts = []
    code = []
    next_id = 256
    for _, option in all_options(modules, False):
        needs_impl = False
        if option.short:  # short option
            needs_impl = True
            code.append("case '{0}': // -{0}".format(option.short))
            short += option.short
            if option.type != 'bool':
                short += ':'
        if option.long:  # long option
            needs_impl = True
            _add_cmdoption(option, option.long_name, opts, next_id)
            code.append('case {}: // --{}'.format(next_id, option.long_name))
            next_id += 1
        if option.alias:  # long option aliases
            needs_impl = True
            for alias in option.alias:
                _add_cmdoption(option, alias, opts, next_id)
                code.append('case {}: // --{}'.format(next_id, alias))
                next_id += 1

        if needs_impl:
            # there is some way to call it, add call to solver.setOption()
            if option.type == 'bool':
                code.append('  solver.setOption("{}", "true"); break;'.format(
                    option.long_name))
            else:
                code.append(
                    '  solver.setOption("{}", optionarg); break;'.format(
                        option.long_name))

        if option.alternate:
            assert option.type == 'bool'
            # bool option that wants a --no-*
            needs_impl = False
            if option.long:  # long option
                needs_impl = True
                _add_cmdoption(option, 'no-' + option.long_name, opts, next_id)
                code.append('case {}: // --no-{}'.format(
                    next_id, option.long_name))
                next_id += 1
            if option.alias:  # long option aliases
                needs_impl = True
                for alias in option.alias:
                    _add_cmdoption(option, 'no-' + alias, opts, next_id)
                    code.append('case {}: // --no-{}'.format(next_id, alias))
                    next_id += 1
            code.append('  solver.setOption("{}", "false"); break;'.format(
                option.long_name))

    return short, '\n  '.join(opts), '\n    '.join(code)


def _cli_help_format_options(option):
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
            opts.extend(
                ['--{}={}'.format(a, option.long_opt) for a in option.alias])
        else:
            opts.extend(['--{}'.format(a) for a in option.alias])

    if option.short:
        if option.long_opt:
            opts.append('-{} {}'.format(option.short, option.long_opt))
        else:
            opts.append('-{}'.format(option.short))

    return ' | '.join(opts)


def _cli_help_wrap(help_msg, opts):
    """Format cmdline documentation (--help) to be 80 chars wide."""
    width_opt = 25
    text = textwrap.wrap(help_msg, 80 - width_opt, break_on_hyphens=False)
    if len(opts) > width_opt - 3:
        lines = ['  {}'.format(opts), ' ' * width_opt + text[0]]
    else:
        lines = ['  {}{}'.format(opts.ljust(width_opt - 2), text[0])]
    lines.extend([' ' * width_opt + l for l in text[1:]])
    return lines


def generate_cli_help(modules):
    """Generate the output for --help."""
    common = []
    others = []
    for module in modules:
        if not module.options:
            continue
        others.append('')
        others.append('From the {} module:'.format(module.name))
        for option in module.options:
            if option.category == 'undocumented':
                continue
            msg = option.help
            if option.category == 'expert':
                msg += ' (EXPERTS only)'
            opts = _cli_help_format_options(option)
            if opts:
                if option.alternate:
                    msg += ' [*]'
                res = _cli_help_wrap(msg, opts)

                if option.category == 'common':
                    common.extend(res)
                else:
                    others.extend(res)
    return '\n'.join(common), '\n'.join(others)


################################################################################
# sphinx command line documentation @ docs/options_generated.rst


def _sphinx_help_add(module, option, common, others):
    """Analyze an option and add it to either common or others."""
    if option.category == 'common':
        common.append(option)
    else:
        if module.name not in others:
            others[module.name] = []
        others[module.name].append(option)


def _sphinx_help_render_option(res, opt):
    """Render an option to be displayed with sphinx."""
    names = []
    if opt.short:
        names.append(opt.short)
    names.append(opt.long_name)
    if opt.alias:
        names.extend(opt.alias)

    data = {
        'names': ' | '.join(names),
        'alternate': '',
        'type': '',
        'default': '',
    }

    if opt.alternate:
        data['alternate'] = ' (also ``--no-*``)'

    if opt.type == 'bool':
        data['type'] = 'type ``bool``'
    elif opt.type == 'std::string':
        data['type'] = 'type ``string``'
    elif is_numeric_cpp_type(opt.type):
        data['type'] = 'type ``{}``'.format(opt.type)
        if opt.minimum and opt.maximum:
            data['type'] += ', ``{} <= {} <= {}``'.format(
                opt.minimum, opt.long_opt, opt.maximum)
        elif opt.minimum:
            data['type'] += ', ``{} <= {}``'.format(opt.minimum, opt.long_opt)
        elif opt.maximum:
            data['type'] += ', ``{} <= {}``'.format(opt.long_opt, opt.maximum)
    elif opt.mode:
        data['type'] = '``' + ' | '.join(opt.mode_name.values()) + '``'
    else:
        data['type'] = 'custom ``{}``'.format(opt.type)

    if opt.default:
        if opt.mode:
            data['default'] = ', default ``{}``'.format(
                opt.mode_name[opt.default])
        else:
            data['default'] = ', default ``{}``'.format(opt.default)

    desc = '``{names}`` [{type}{default}]{alternate}'.format(**data)

    res.append('.. _lbl-option-{}:'.format(opt.long_name))
    res.append('')
    if opt.category == 'expert':
        res.append('.. rst-class:: expert-option simple')
        res.append('')
        desc += '''
    .. rst-class:: float-right

    **[experts only]**
'''

    res.append(desc)
    res.append('    ' + opt.help.replace("*", "\\*"))

    if opt.mode:
        res.append('    ')
        res.append('    ' + opt.help_mode)
        res.append('    ')
        for m in opt.mode.keys():
            if opt.mode_help[m]:
                res.append('    :``{}``: {}'.format(opt.mode_name[m], opt.mode_help[m]))
    res.append('    ')


def generate_sphinx_help(modules):
    """Render the command line help for sphinx."""
    common = []
    others = {}
    for module, option in all_options(modules, False):
        if option.category == 'undocumented':
            continue
        if not option.long and not option.short:
            continue
        _sphinx_help_add(module, option, common, others)

    res = []
    res.append('Most Commonly-Used cvc5 Options')
    res.append('===============================')
    for opt in common:
        _sphinx_help_render_option(res, opt)

    res.append('')
    res.append('Additional cvc5 Options')
    res.append('=======================')
    for module in others:
        res.append('')
        res.append('{} Module'.format(module))
        res.append('-' * (len(module) + 8))
        for opt in others[module]:
            _sphinx_help_render_option(res, opt)

    return '\n'.join(res)


################################################################################
# sphinx documentation for --output @ docs/output_tags_generated.rst


def generate_sphinx_output_tags(modules, src_dir, build_dir):
    """Render help for the --output option for sphinx."""
    base = next(filter(lambda m: m.id == 'base', modules))
    opt = next(filter(lambda o: o.long == 'output=TAG', base.options))

    # The programoutput extension has weird semantics about the cwd:
    # https://sphinxcontrib-programoutput.readthedocs.io/en/latest/#usage
    cwd = '/' + os.path.relpath(build_dir, src_dir)

    res = []
    for name, info in opt.mode.items():
        info = info[0]
        if 'description' not in info:
            continue
        res.append(opt.mode_name[name])
        res.append('~' * len(res[-1]))
        res.append('')
        res.append(info['description'])
        if 'example-file' in info:
            res.append('')
            res.append('.. command-output:: bin/cvc5 -o {} ../test/regress/cli/{}'.format(info['name'], info['example-file']))
            res.append('  :cwd: {}'.format(cwd))
        res.append('')
        res.append('')

    return '\n'.join(res)


################################################################################
# for io_utils.h and io_utils.cpp


def __get_printer_options(modules):
    for mod, opt in all_options(modules):
        if mod.id == 'printer':
            yield opt


def generate_iodecls(modules):
    return concat_format(
        '''
void setDefault{name_capitalized}({type} value);
void apply{name_capitalized}(std::ios_base& ios, {type} value) CVC5_EXPORT;
{type} get{name_capitalized}(std::ios_base& ios);''',
        __get_printer_options(modules))


def generate_ioimpls(modules):
    return concat_format(
        '''
const static int s_ios{name_capitalized} = std::ios_base::xalloc();
static thread_local {type} s_{name}Default = {fqdefault};
void setDefault{name_capitalized}({type} value) {{ s_{name}Default = value; }}
void apply{name_capitalized}(std::ios_base& ios, {type} value) {{ setData(ios, s_ios{name_capitalized}, value); }}
{type} get{name_capitalized}(std::ios_base& ios) {{ return getData(ios, s_ios{name_capitalized}, s_{name}Default); }}
''', __get_printer_options(modules))


def generate_ioscope_members(modules):
    return concat_format('  {type} d_{name};', __get_printer_options(modules))


def generate_ioscope_memberinit(modules):
    return concat_format('      d_{name}(get{name_capitalized}(d_ios))',
                         __get_printer_options(modules),
                         glue=',\n')


def generate_ioscope_restore(modules):
    return concat_format('  apply{name_capitalized}(d_ios, d_{name});',
                         __get_printer_options(modules))


################################################################################
# main code generation for individual modules


def codegen_module(module, dst_dir, tpls):
    """Generate code for one option module."""
    data = {
        'id_cap': module.id_cap,
        'id': module.id,
        # module header
        'includes': generate_module_includes(module),
        'modes_decl': generate_module_mode_decl(module),
        'holder_decl': generate_module_holder_decl(module),
        # module source
        'header': module.header,
        'modes_impl': generate_module_mode_impl(module),
    }
    for tpl in tpls:
        filename = tpl['output'].replace('module', module.filename)
        write_file(dst_dir, filename, tpl['content'].format(**data))


################################################################################
# main code generation


def codegen_all_modules(modules, src_dir, build_dir, dst_dir, tpls):
    """Generate code for all option modules."""
    short, cmdline_opts, parseinternal = generate_parsing(modules)
    help_common, help_others = generate_cli_help(modules)

    if os.path.isdir('{}/docs/'.format(build_dir)):
        write_file('{}/docs/'.format(build_dir), 'options_generated.rst',
                   generate_sphinx_help(modules))
        write_file('{}/docs/'.format(build_dir), 'output_tags_generated.rst',
                   generate_sphinx_output_tags(modules, src_dir, build_dir))

    data = {
        # options/io_utils.h
        'ioscope_members': generate_ioscope_members(modules),
        'iodecls': generate_iodecls(modules),
        # options/io_utils.cpp
        'ioimpls': generate_ioimpls(modules),
        'ioscope_memberinit': generate_ioscope_memberinit(modules),
        'ioscope_restore': generate_ioscope_restore(modules),
        # options/options.h
        'holder_fwd_decls': generate_holder_fwd_decls(modules),
        'holder_mem_decls': generate_holder_mem_decls(modules),
        'holder_ref_decls': generate_holder_ref_decls(modules),
        # options/options.cpp
        'headers_module': generate_module_headers(modules),
        'holder_mem_inits': generate_holder_mem_inits(modules),
        'holder_ref_inits': generate_holder_ref_inits(modules),
        'write_functions': generate_write_functions(modules),
        'holder_mem_copy': generate_holder_mem_copy(modules),
        # options/options_public.cpp
        'options_includes': generate_public_includes(modules),
        'getnames_impl': generate_getnames_impl(modules),
        'option_enum_and_table': generate_option_enum_and_table(modules),
        'get_impl': generate_get_impl(modules),
        'set_impl': generate_set_impl(modules),
        'getinfo_impl': generate_getinfo_impl(modules),
        # main/options.cpp
        'help_common': help_common,
        'help_others': help_others,
        'cmdoptions_long': cmdline_opts,
        'cmdoptions_short': short,
        'parseinternal_impl': parseinternal,
    }
    for tpl in tpls:
        write_file(dst_dir, tpl['output'], tpl['content'].format(**data))


################################################################################
# sanity checking


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
        if o.name and o.default is None:
            self.perr('has no default', option=o)
        if o.long:
            self.__check_option_long(o, o.long_name)
            if o.alternate:
                self.__check_option_long(o, 'no-' + o.long_name)
            if o.type == 'bool' and '=' in o.long:
                self.perr('bool options must not have an argument description', option=o)
            if o.type != 'bool' and not '=' in o.long:
                self.perr("needs argument description ('{}=...')",
                          o.long,
                          option=o)
            if o.alias:
                for alias in o.alias:
                    self.__check_option_long(o, alias)
                    if o.alternate:
                        self.__check_option_long(o, 'no-' + alias)
        return o


################################################################################
# main entrypoint


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
        {'input': 'options/io_utils_template.h'},
        {'input': 'options/io_utils_template.cpp'},
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
    codegen_all_modules(modules, src_dir, build_dir, dst_dir, global_tpls)

    # Generate output file to signal cmake when this script was run last
    open(os.path.join(dst_dir, 'options/options.stamp'), 'w').write('')


if __name__ == "__main__":
    mkoptions_main()
    sys.exit(0)
