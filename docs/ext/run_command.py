from docutils import nodes
from docutils.parsers.rst import directives
from docutils.statemachine import StringList
from sphinx.util.docutils import SphinxDirective


class RunCommand(SphinxDirective):
    """Add directive `run-command` that enhances `command-output` by proper usage
        of the build directory. It is used just the same as `command-output`:

        .. run-command:: <command>
            :cwd: /directory
        
        The only difference to `command-output` is that the current working directory
        defaults to the current build folder, and the directory (optionally) given
        to the `cwd` option allows for the following placeholders:

        - `<build>`: current build folder

        The path of the build folder needs to be configured in the `runcmd_build` option.
    """

    has_content = True
    option_spec = {
        'cwd': directives.path
    }

    def run(self):
        self.state.document.settings.env.note_dependency(__file__)
        
        cwd = self.env.config.runcmd_build
        if 'cwd' in self.options:
            repl = {
                '<build>': self.env.config.runcmd_build,
            }
            cwd = self.options['cwd']
            for r,s in repl.items():
                cwd = cwd.replace(r, s)
        
        content = [
            '.. command-output:: ' + ''.join(self.content),
            '  :cwd: ' + cwd]

        node = nodes.Element()
        self.state.nested_parse(StringList(content), 0, node)
        return node.children


def setup(app):
    app.setup_extension('sphinxcontrib.programoutput')
    app.add_config_value('runcmd_build', '', 'env')
    app.add_directive("run-command", RunCommand)
    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
