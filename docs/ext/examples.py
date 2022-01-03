import os
import re

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
    types = {
        '\.cpp$': {
            'title': 'C++',
            'lang': 'c++',
            'group': 'c++'
        },
        '\.java$': {
            'title': 'Java',
            'lang': 'java',
            'group': 'java'
        },
        '<examples>.*\.py$': {
            'title': 'Python',
            'lang': 'python',
            'group': 'py-regular'
        },
        '<z3pycompat>.*\.py$': {
            'title': 'Python z3py',
            'lang': 'python',
            'group': 'py-z3pycompat'
        },
        '\.smt2$': {
            'title': 'SMT-LIBv2',
            'lang': 'smtlib',
            'group': 'smt2'
        },
        '\.sy$': {
            'title': 'SyGuS',
            'lang': 'smtlib',
            'group': 'smt2'
        },
    }

    # The "arguments" are actually the content of the directive
    has_content = True

    logger = logging.getLogger(__name__)
    
    srcdir = None

    def run(self):
        self.state.document.settings.env.note_dependency(__file__)
        # collect everything in a list of strings
        content = ['.. tabs::', '']

        remaining = set([t['group'] for t in self.types.values()])
        location = '{}:{}'.format(*self.get_source_info())

        for file in self.content:
            # detect file extension
            lang = None
            title = None
            for type in self.types:
                if re.search(type, file) != None:
                    lang = self.types[type]['lang']
                    title = self.types[type]['title']
                    remaining.discard(self.types[type]['group'])
                    break
            if lang == None:
                self.logger.warning(
                    f'file type of {location} could not be detected')
                title = os.path.splitext(file)[1]
                lang = title

            for k, v in self.env.config.ex_patterns.items():
                file = file.replace(k, v)

            # generate tabs
            content.append(f'    .. tab:: {title}')
            content.append(f'')

            if file.startswith('/'):
                # if the file is "absolute", we can provide a download link
                urlname = os.path.relpath(os.path.join('..', file[1:]), os.path.join(self.srcdir, '..'))
                url = f'https://github.com/cvc5/cvc5/tree/master/{urlname}'
                content.append(f'        .. rst-class:: fa fa-download icon-margin')
                content.append(f'        ')
                content.append(f'        `{urlname} <{url}>`_')
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
    APIExamples.srcdir = app.srcdir
    app.setup_extension('sphinx_tabs.tabs')
    app.add_config_value('ex_patterns', {}, 'env')
    app.add_directive("api-examples", APIExamples)
    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
