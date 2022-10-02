Specifying Modules
==================

Every options module, that is a group of options that belong together in some
way, is declared in its own file in `options/{module name}_options.toml`. Each
options module starts with the following required attributes:

* `id` (string): ID of the module (e.g., `"ARITH"`)
* `name` (string): name of the module (e.g., `"Arithmetic Theory"`)

A module defines zero or more options.
In general, each attribute/value pair is required to be in one line. Comments
start with # and are not allowed in attribute/value lines.

After parsing, a module is extended to have the following attributes:

* `id`: lower-case version of the parsed `id`
* `id_cap`: upper-case version of `id` (used for the `Holder{id_cap}` class)
* `id_capitalized`: `id` with first letter upper-cased (used for the
  `write{id_capitalized}()` method)
* `filename`: base filename for generated files (`"{id}_options"`)
* `header`: generated header name (`"options/{filename}.h"`)


Specifying Options
==================

Options can be defined within a module file with the `[[option]]` tag, the
required attributes for an option are:

* `category` (string): one of `common`, `regular`, `expert`, or `undocumented`
* `type` (string): the C++ type of the option value, see below for more details.

Optional attributes are:

* `name` (string): the option name used to access the option internally
  (`d_option.{module.id}.{name}`)
* `long` (string): long option name (without `--` prefix). Long option names may
  have a suffix `=XXX` where `XXX` can be used to indicate the type of the
  option value, e.g., `=MODE`, `=LANG`, `=N`, ...
* `short` (string): short option name consisting of one character (no `-` prefix
  required), can be given if `long` is specified
* `alias` (list): alternative names that can be used instead of `long`
* `default` (string): default value, needs to be a valid C++ expression of type
  `type`
* `alternate` (bool, default `true`): if `true`, adds `--no-{long}` alternative
  option
* `mode` (list): used to define options whose type shall be an auto-generated
  enum, more details below
* `handler` (string): alternate parsing routine for option types not covered by
  the default parsers, more details below
* `predicates` (list): custom validation function to check whether an option
  value is valid, more details below
* `includes` (list): additional header files required by handler or predicate
  functions
* `minimum` (numeric): impose a minimum value on this option.
* `maximum` (numeric): impose a maximum value on this option.
* `help` (string): documentation string (required, unless the `category` is
  `undocumented`)
* `help_mode` (string): documentation for the mode enum (required if `mode` is
  given)


Option categories
-----------------

Every option has one of the following categories that influences where and how an option is visible:

* `common`: Used for the most common options. All `common` options are shown at the very top in both the online documentation and the output of `--help` on the command line.
* `regular`: This should be used for most options.
* `expert`: This is for options that should be used with care only. A warning is shown in both the online documentation and the command line help.
* `undocumented`: Such an option is skipped entirely in both the online documentation and the command line help. This should only be used when users don't have a (reasonable) use case for this option (e.g., because it stores data that is added via another option like for `output` and `outputTagHolder`).

Option types
------------

Though not enforced explicitly, option types are commonly expected to come from
a rather restricted set of C++ types:
Boolean options should use `bool`;
numeric options should use one of `int64_t`, `uint64_t` and `double`, possibly
using `minimum` and `maximum` to further restrict the options domain;
mode options should use a fresh type name for the auto-generated enum as
detailed below.

While other C++ types are allowed, they should only be used in special cases
when the above types are not sufficient.


Handler functions
-----------------

Custom handler functions are used to turn the option value from an `std::string`
into the type specified by `type`. Standard handler functions are provided for
basic types (`std::string`, `bool`, `int64_t`, `uint64_t`, and `double`) as
well as enums specified by `mode`. A custom handler function needs to be a 
member function of `options::OptionsHandler` with signature
`{type} {handler}(const std::string& flag, const std::string& optionvalue)`.
The parameter `flag` holds the actually used option name, which may be an alias
name, and should only be used in user messages.


Predicate functions
-------------------

Predicate functions are called after an option value has been parsed by a
(standard or custom) handler function. They usually either check whether the
parsed option value is valid, or to trigger some action (e.g. print some
message or set another option). Like a handler function, a predicate function
needs to be a member function of `options::OptionsHandler` with signature
`void {predicate}(const std::string& flag, {type} value)`.
A predicate function is expected to raise an `OptionException` if the option
value is not valid for some reason.


Mode options
------------

An option can be defined to hold one of a given set of values we call modes.
Doing so automatically defines an `enum class` for the set of modes and makes
the option accept one of the values from the enum. The enum class will be called
`{type}` and methods `operator<<` and `stringTo{enum}` are automatically
generated. A mode is defined by specifying `[[option.mode.{NAME}]]` after the
main `[[option]]` section with the following attributes:

* `name` (string): the string value that corresponds to the enum value
* `help` (string): documentation about this mode

Example:

    [[option]]
        name       = "bitblastMode"
        category   = "regular"
        long       = "bitblast=MODE"
        type       = "BitblastMode"
        default    = "LAZY"
        help       = "choose bitblasting mode, see --bitblast=help"
        help_mode  = "Bit-blasting modes."
    [[option.mode.LAZY]]
        name = "lazy"
        help = "Separate boolean structure and term reasoning between the core SAT solver and the bit-vector SAT solver."
    [[option.mode.EAGER]]
        name = "eager"
        help = "Bitblast eagerly to bit-vector SAT solver."

The option can now be set with `--bitblast=lazy`, `(set-option :bitblast
eager)`, or `options::set("bitblast", "eager")`.


Generated code
==============

The entire options setup heavily relies on generating a lot of code from the
information retrieved from the `*_options.toml` files. After code generation,
files related to options live either in `src/options/` (if not changed) or in
`build/src/options/` (if automatically generated). Additionally, code that is
only needed when using cvc5 on the command line lives in `src/main/` and
`build/src/main`. After all code has been generated, the entire options setup
consists of the following components:

* `options/options.h`: core `Options` class
* `options/options_public.h`: utility methods used by the API (`getNames()`, `get()`, `set()` and `getInfo()`)
* `options/{module}_options.h`: specifics for one single options module
* `main/options.h`: utility methods used by the CLI (`parse()` and `printUsage()`)


`Options` class
---------------

The `Options` class is the central entry point for regular usage of options. It
holds a `std::unique_ptr` to an "option holder" for every option module, that
can be accessed using references `const {module}&`. These holders hold the actual
option data for the specific module. For non-const accesses, there are methods
`write{module}()` which can only be used from a non-const handle to the `Options`
object.

The holder types are forward declared and can thus only be accessed if one also
includes the appropriate `{module}_options.h`, which contains the proper
declaration for the holder class.


Option modules
--------------

Every option module declares an "option holder" class, which is a simple struct
that has two members for every option (that specifies a `name`):
the actual option value as `{option.type} {option.name}` and a Boolean flag
`bool {option.name}WasSetByUser` that indicates whether the option value was
explicitly set by the user. If any of the options of a module is a mode option,
the option module also defines an enum class that corresponds to the mode,
including `operator<<()` and `stringTo{mode type}`.


Full Example
============

    [[option]]
      category   = "regular"
      name       = "decisionMode"
      long       = "decision=MODE"
      alias      = ["decision-mode"]
      type       = "DecisionMode"
      default    = "INTERNAL"
      predicates = ["setDecisionModeStopOnly"]
      help       = "choose decision mode, see --decision=help"
      help_mode  = "Decision modes."
    [[option.mode.INTERNAL]]
      name = "internal"
      help = "Use the internal decision heuristics of the SAT solver."
    [[option.mode.JUSTIFICATION]]
      name = "justification"
      help = "An ATGP-inspired justification heuristic."
    [[option.mode.STOPONLY]]
      name = "justification-stoponly"
      help = "Use the justification heuristic only to stop early, not for decisions."

This defines a new option that is accessible via
`d_options.{module.id}.decisionMode` and stores an automatically generated mode
`DecisionMode`, an enum class with the values `INTERNAL`, `JUSTIFICATION` and
`STOPONLY`. From the outside, it can be set by `--decision=internal`, but also
with `--decision-mode=justification`, and similarly from an SMT-LIB input with
`(set-option :decision internal)` and `(set-option :decision-mode
justification)`. The command-line help for this option looks as follows:

    --decision=MODE | --decision-mode=MODE
                           choose decision mode, see --decision=help
