import os

from docutils import nodes
from docutils.statemachine import StringList
from sphinx.util import logging
from sphinx.util.docutils import SphinxDirective


class APIExamples(SphinxDirective):
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
        '.smt2': {'title': 'SMT-LIBv2', 'lang': 'smtlib'},
        '.sy': {'title': 'SyGuS', 'lang': 'smtlib'},
    }

    # The "arguments" are actually the content of the directive
    has_content = True

    logger = logging.getLogger(__name__)

    def run(self):
        self.state.document.settings.env.note_dependency(__file__)
        # collect everything in a list of strings
        content = ['.. tabs::', '']

        remaining = set([self.exts[e]['lang'] for e in self.exts])
        location = '{}:{}'.format(*self.get_source_info())

        for file in self.content:
            # detect file extension
            _, ext = os.path.splitext(file)
            if ext in self.exts:
                title = self.exts[ext]['title']
                lang = self.exts[ext]['lang']
                remaining.remove(lang)
            else:
                self.logger.warning(f'{location} is using unknown file extension "{ext}"')
                title = ext
                lang = ext

            # generate tabs
            content.append(f'    .. tab:: {title}')
            content.append(f'')
            content.append(f'        .. literalinclude:: {file}')
            content.append(f'            :language: {lang}')
            content.append(f'            :linenos:')

        for r in remaining:
            self.logger.warning(f'{location} has no {r} example!')

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
