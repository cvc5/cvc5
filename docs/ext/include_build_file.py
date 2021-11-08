import os

from docutils import nodes
from docutils.parsers.rst import Directive
from docutils.statemachine import StringList
from sphinx.util.docutils import SphinxDirective
from sphinx.util.nodes import nested_parse_with_titles

class IncludeBuildFile(SphinxDirective):
    """Add directive `include-build-file` to be used as follows:

        .. include-build-file:: <filename>

    The argument should be a filename of an rst files within one of the
    folders given by the `ibf_folders` config option.
    """

    # The "arguments" are actually the content of the directive
    has_content = True

    def run(self):
        self.state.document.settings.env.note_dependency(__file__)
        filename = ''.join(self.content)
        for folder in self.env.config.ibf_folders:
            candidate = os.path.join(folder, filename)
            if os.path.isfile(candidate):
                filename = candidate
                break
        content = open(filename).readlines()
        content = [line.rstrip('\n') for line in content]
        # parse the string list
        node = nodes.Element()
        nested_parse_with_titles(self.state, StringList(content), node)
        self.state.document.settings.env.note_dependency(filename)
        return node.children


def setup(app):
    app.add_config_value('ibf_folders', [], 'env')
    app.add_directive('include-build-file', IncludeBuildFile)
    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
