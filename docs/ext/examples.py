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
        and supports the file extensions specified in `examples_types`.
        Additionally, `examples_file_patterns` allows to specify file name
        patterns that allow using files from fixed directories more easily, and
        to add proper download links.

        examples_types:
            '<regex>': {
                'title': '<tab title>',
                'lang': '<language identifier for synatax highlighting>',
                'group': '<group identifier to detext missing examples>',
            }

        examples_file_patterns:
            '<regex>': { # match groups are used to format the strings below
                'local': '<pseudo-absolute path to local file>',
                'url': '<url to download this file>', # optional
                'urlname': '<text for the download link>',
            }
    """

    # The "arguments" are actually the content of the directive
    has_content = True

    logger = logging.getLogger(__name__)
    
    srcdir = None

    def run(self):
        self.state.document.settings.env.note_dependency(__file__)
        # collect everything in a list of strings
        content = ['.. tabs::', '']

        remaining = set([t['group'] for t in self.env.config.examples_types.values()])
        location = '{}:{}'.format(*self.get_source_info())

        for file in self.content:
            # detect file extension
            lang = None
            title = None
            for pattern,data in self.env.config.examples_types.items():
                if re.search(pattern, file) != None:
                    lang = data['lang']
                    title = data['title']
                    remaining.discard(data['group'])
                    break
            if lang == None:
                self.logger.warning(
                    f'file type of {location} could not be detected')
                title = os.path.splitext(file)[1]
                lang = title

            url = None
            urlname = None
            for k, v in self.env.config.examples_file_patterns.items():
                m = re.match(k, file)
                if m is not None:
                    file = v['local'].format(*m.groups())
                    if 'url' in v:
                        url = v['url'].format(*m.groups())
                        urlname = v['urlname'].format(*m.groups())
                    break

            # generate tabs
            content.append(f'    .. tab:: {title}')
            content.append(f'')

            if url is not None:
                # we can provide a download link
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
    app.add_config_value('examples_types', {}, 'env')
    app.add_config_value('examples_file_patterns', {}, 'env')
    app.add_directive("api-examples", APIExamples)
    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
