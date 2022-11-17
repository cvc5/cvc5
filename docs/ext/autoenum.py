import enum
from typing import Any, Optional

from docutils.statemachine import StringList
from sphinx.application import Sphinx
from sphinx.ext.autodoc import ClassDocumenter, bool_option


class EnumDocumenter(ClassDocumenter):
    """Adds a custom "documenter" for the autodoc extension. This particular
    documenter is internally used for enum values of a ``enum.Enum`` base class.

    This documenter assumes that the enum class injects proper docstrings into
    the ``__doc__`` property of every single enum value.
    """

    objtype = 'enum'
    directivetype = 'class'
    priority = 10 + ClassDocumenter.priority
    option_spec = dict(ClassDocumenter.option_spec)

    @classmethod
    def can_document_member(cls, member: Any, membername: str, isattr: bool,
                            parent: Any) -> bool:
        """Document instances of (derived classes of) ``enum.Enum``."""
        return isinstance(member, enum.Enum)

    def add_content(self,
                    more_content: Optional[StringList]) -> None:
        """Add the docstring for this object."""

        # overriding this flag prints __doc__ just as we want to.
        self.doc_as_attr = False
        super().add_content(more_content)
        self.doc_as_attr = True


def setup(app: Sphinx) -> None:
    app.setup_extension('sphinx.ext.autodoc')
    app.add_autodocumenter(EnumDocumenter)
