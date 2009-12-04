SOURCES = \
	SmtLexer.g \
	SmtParser.g 
	SmtLexer.hpp \
	SmtLexer.cpp \
	SmtParser.hpp \
	SmtParser.cpp   

BUILT_SOURCES = \
	SmtLexer.hpp \
	SmtLexer.cpp \
	SmtParser.hpp \
	SmtParser.cpp 

SmtLexer.cpp SmtLexer.hpp: SmtLexer.g
	$(ANTLR) SmtLexer.g

SmtParser.cpp SmtParser.hpp: SmtParser.g
	$(ANTLR) SmtParser.g
