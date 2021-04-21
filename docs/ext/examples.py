import os

from docutils import nodes
from docutils.parsers.rst import Directive
from docutils.statemachine import StringList


class APIExamples(Directive):
    """Add directive `api-examples` to be used as follows:

        .. api-examples::
            file1
            file2

        The arguments should be proper filenames to source files.
        This directives tries to detect the language from the file extension
        and supports the file extensions specified in `self.exts`.
    """

    # Set tab title and language for syntax highlighting
    exts = {
        '.cpp': {'title': 'C++', 'lang': 'c++'},
        '.java': {'title': 'Java', 'lang': 'java'},
        '.py': {'title': 'Python', 'lang': 'python'},
    }

    # The "arguments" are actually the content of the directive
    has_content = True

    def run(self):
        # collect everything in a list of strings
        content = ['.. tabs::', '']

        for file in self.content:
            # detect file extension
            _, ext = os.path.splitext(file)
            if ext in self.exts:
                title = self.exts[ext]['title']
                lang = self.exts[ext]['lang']
            else:
                title = ext
                lang = ext

            # generate tabs
            content.append(f'    .. tab:: {title}')
            content.append(f'')
            content.append(f'        .. literalinclude:: {file}')
            content.append(f'            :language: {lang}')
            content.append(f'            :linenos:')

        # parse the string list
        node = nodes.Element()
        self.state.nested_parse(StringList(content), 0, node)
        return node.children


def setup(app):
    app.setup_extension('sphinx_tabs.tabs')
    app.add_directive("api-examples", APIExamples)
    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
