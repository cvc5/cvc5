import os
import shutil
import sys
from subprocess import Popen, PIPE, STDOUT

g_id = 0


def fresh_name(prefix):
    global g_id
    g_id += 1
    return f'{prefix}{g_id}'


def format_cpp(s):
    if shutil.which('clang-format') is None:
        # If we clang-format is not installed, we don't format the output
        return s

    p = Popen(["clang-format"], stdout=PIPE, stdin=PIPE, stderr=STDOUT)
    out = p.communicate(input=s.encode())[0]
    return out.decode()


# TODO: refactor common code
def die(msg):
    sys.exit('[error] {}'.format(msg))


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
                            replace('${', '').replace('}$', '').\
                            replace('// clang-format on\n', '').\
                            replace('// clang-format off\n', '')
            return contents
    except IOError:
        die("Could not find '{}'. Aborting.".format(fname))
