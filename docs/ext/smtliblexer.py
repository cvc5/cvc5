from pygments.lexer import RegexLexer
from pygments import token


class SmtLibLexer(RegexLexer):
    """This class implements a lexer for SMT-LIBv2.
    It tries to be very close to the SMT-LIBv2 standard while providing proper
    highlighting for everything cvc5 supports.
    The lexer implements the SMT-LIBv2 lexicon (section 3.1 of the standard)
    directly in the root state, as well as the commands, sorts and operators.
    Note that commands, sorts and operators are used to build regular
    expressions and, thus, can contain character classes (e.g. "[0-9]+"), but
    also need to escape certain characters (e.g. "\." or "\+").
    """

    name = 'smtlib'

    COMMANDS = [
        'assert', 'block-model', 'block-model-values', 'check-sat',
        'check-sat-assuming', 'declare-const', 'declare-datatype',
        'declare-datatypes', 'declare-codatatypes', 'declare-fun',
        'declare-sort', 'define-const', 'define-fun', 'define-fun-rec',
        'define-funs-rec', 'define-sort', 'echo', 'exit', 'get-abduct',
        'get-abduct-next', 'get-assertions', 'get-assignment', 'get-info',
        'get-interpolant', 'get-model', 'get-option', 'get-proof', 'get-qe',
        'get-qe-disjunct', 'get-unsat-assumptions', 'get-unsat-core',
        'get-value', 'pop', 'push', 'reset', 'reset-assertions', 'set-info',
        'set-logic', 'set-option',
        # SyGuS v2
        'assume', 'check-synth', 'constraint', 'declare-var', 'inv-constraint',
        'synth-fun', 'synth-inv', 'declare-pool',
    ]
    SORTS = [
        'Array', 'BitVec', 'Bag', 'Bool', 'FloatingPoint', 'Float[0-9]+',
        'Int', 'Real', 'RegLan', 'RoundingMode', 'Set', 'Seq', 'String',
        'Tuple',
    ]
    OPERATORS = [
        # array
        'select', 'store',
        # bv
        'concat', 'extract', 'repeat', 'zero_extend', 'sign_extend',
        'rotate_left', 'rotate_right', 'bvnot', 'bvand', 'bvor', 'bvneg',
        'bvadd', 'bvmul', 'bvudiv', 'bvurem', 'bvshl', 'bvlshr', 'bvult',
        'bvnand', 'bvnor', 'bvxor', 'bvxnor', 'bvcomp', 'bvsub', 'bvsdiv',
        'bvsrem', 'bvsmod', 'bvashr', 'bvule', 'bvugt', 'bvuge', 'bvslt',
        'bvsle', 'bvsgt', 'bvsge',
        # core
        '=>', '=', 'true', 'false', 'not', 'and', 'or', 'xor', 'distinct',
        'ite',
        # datatypes
        'tuple', 'tuple\.project', 'tuple\.select', 'tuple\.update',
        # fp
        'RNE', 'RNA', 'RTP', 'RTN', 'RTZ', 'fp', 'NaN', 'fp\.abs', 'fp\.neg',
        'fp\.add', 'fp\.sub', 'fp\.mul', 'fp\.div', 'fp\.fma', 'fp\.sqrt',
        'fp\.rem', 'fp\.roundToIntegral', 'fp\.min', 'fp\.max', 'fp\.leq',
        'fp\.lt', 'fp\.geq', 'fp\.gt', 'fp\.eq', 'fp\.isNormal',
        'fp\.isSubnormal', 'fp\.isZero', 'fp\.isInfinite', 'fp\.isNaN',
        'fp\.isNegative', 'fp\.isPositive', 'to_fp', 'to_fp_unsigned',
        'fp\.to_ubv', 'fp\.to_sbv', 'fp\.to_real', '\+oo', '-oo', '\+zero',
        '-zero',
        # int / real
        '<', '>', '<=', '>=', '!=', '\+', '-', '\*', '/', 'div', 'mod', 'abs',
        'divisible', 'to_real', 'to_int', 'is_int', 'iand', 'int2bv',
        # separation logic
        'sep\.emp', 'pto', 'sep', 'wand', 'sep\.nil',
        # sets / relations
        'set\.union', 'set\.minus', 'set\.member', 'set\.subset', 'set\.empty',
        'set\.singleton', 'set\.card', 'set\.insert', 'set\.complement',
        'set\.universe', 'rel\.transpose', 'rel\.tclosure', 'rel\.join',
        'rel\.product', 'set\.inter',
        # string
        'char', 'str\.\+\+', 'str\.len', 'str\.<', 'str\.<=', 'str\.to_re',
        'str\.in_re', 're\.none', 're\.all', 're\.allchar', 're\.\+\+',
        're\.union', 're\.inter', 're\.*', 'str\.<=', 'str\.at', 'str\.substr',
        'str\.prefixof', 'str\.suffixof', 'str\.contains', 'str\.indexof',
        'str\.replace', 'str\.replace_all', 'str\.replace_re',
        'str\.replace_re_all', 're\.comp', 're\.diff', 're\.\+', 're\.opt',
        're\.range', 're\.^', 're\.loop', 'str\.is_digit', 'str\.to_code',
        'str\.from_code', 'str\.to_int', 'str\.from_int',
        # sequences
        'seq\.\+\+', 'seq\.len', 'seq\.extract', 'seq\.update', 'seq\.at',
        'seq\.contains', 'seq\.indexof', 'seq\.replace', 'seq\.prefixof',
        'seq\.suffixof', 'seq\.rev', 'seq\.replace_all', 'seq\.unit',
        'seq\.nth', 'seq\.empty',
        # others
        'witness',
    ]

    tokens = {
        'root': [
            # comment (see lexicon)
            (r';.*$', token.Comment),
            # whitespace
            (r'\s+', token.Text),
            # numeral (decimal, hexadecimal, binary, see lexicon)
            (r'[0-9]+', token.Number),
            (r'#x[0-9a-fA-F]+', token.Number),
            (r'#b[01]+', token.Number),
            # bv constant (see BV theory specification)
            (r'bv[0-9]+', token.Number),
            # string constant (including escaped "", see lexicon)
            (r'".*?"', token.String),
            # reserved words (non-word and regular, see lexicon)
            (r'[!_](?=\s)', token.Name.Attribute),
            ('(as|let|exists|forall|match|per)\\b', token.Keyword),
            # Keywords (:foo, see lexicon)
            (r':[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*',
             token.Name.Attribute),
            # parentheses
            (r'\(', token.Text),
            (r'\)', token.Text),
            (r'\{', token.Text),
            (r'\}', token.Text),
            # commands (terminated by whitespace or ")")
            ('(' + '|'.join(COMMANDS) + ')(?=(\s|\)))', token.Keyword),
            # sorts (terminated by whitespace or ")")
            ('(' + '|'.join(SORTS) + ')(?=(\s|\)))', token.Name.Attribute),
            # operators (terminated by whitespace or ")")
            ('(' + '|'.join(OPERATORS) + ')(?=(\s|\)))', token.Operator),
            # symbols (regular and quoted, see lexicon)
            (r'[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*', token.Name),
            (r'\|[^|\\]*\|', token.Name),
        ],
    }
