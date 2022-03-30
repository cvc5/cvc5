import re
import textwrap

CPP_JAVA_MAPPING = \
    {
        r"\bbool\b": "boolean",
        r"\bconst\b\s?": "",
        r"\bint32_t\b": "int",
        r"\bint64_t\b": "long",
        r"\buint32_t\b": "int",
        r"\buint64_t\b": "long",
        r"\bunsigned char\b": "byte",
        r"cvc5::": "cvc5.",
        r"Term::Term\(\)": "{@link Solver#getNullTerm()",
        r"Term::": "{@link Term#",
        r"Solver::": "{@link Solver#",
        r"std::vector<int>": "int[]",
        r"std::vector<Term>": "Term[]",
        r"std::string": "String",
        r"&": "",
        r"::": ".",
        r">": "&gt;",
        r"<": "&lt;",
        r"@f\[": "",
        r"@f\]": "",
        r"@note": "",
    }


# convert from c++ doc to java doc
def format_comment(comment):
    for pattern, replacement in CPP_JAVA_MAPPING.items():
        comment = re.sub(pattern, replacement, comment)
    comment = """  /**\n{}\n   */""".format(textwrap.indent(comment, '   * '))

    def close_link(match):
        link = match.group()
        link = link.replace(" ", "")
        link = link.replace("@link", "@link ")
        if "}" in link:
            return link
        return "{0}}} ".format(link)

    function_pattern = re.compile(r"{@link (.*?\))")
    comment = re.sub(function_pattern, close_link, comment)
    field_pattern = re.compile(r"{@link [a-zA-Z\.#]*\b")
    comment = re.sub(field_pattern, close_link, comment)
    return comment


c = ' Real value, i.e., Term::isRealValue() will return `false`  Real value, i.e., ' \
    'Solver::mkBitVector(uint32_t, uint64_t) will return `false`' \
    'Solver::mkBitVector::Pi will return `false`'
print(format_comment(c))
