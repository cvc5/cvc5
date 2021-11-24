import enum
from typing import Any, Optional

from docutils.statemachine import StringList
from sphinx.application import Sphinx
from sphinx.ext.autodoc import ClassDocumenter, bool_option

class EnumDocumenter(ClassDocumenter):
    objtype = 'enum'
    directivetype = 'class'
    priority = 10 + ClassDocumenter.priority
    option_spec = dict(ClassDocumenter.option_spec)

    @classmethod
    def can_document_member(cls, member: Any, membername: str, isattr: bool, parent: Any) -> bool:
        return isinstance(member, enum.Enum)

    def add_directive_header(self, sig: str) -> None:
        super().add_directive_header(sig)
        #self.add_line('   :type: Kind', self.get_sourcename()) 
    
    def add_content(self, more_content: Optional[StringList], no_docstring: bool = False) -> None:
        super().add_content(more_content, no_docstring)

        source_name = self.get_sourcename()
        for line in self.object.__doc__.split('\n'):
            self.add_line(line, source_name)
        self.add_line('', source_name)
        self.add_line('', source_name)
        #print('\n'.join(self.directive.result[-6:]))


def setup(app: Sphinx) -> None:
    app.setup_extension('sphinx.ext.autodoc')
    app.add_autodocumenter(EnumDocumenter)