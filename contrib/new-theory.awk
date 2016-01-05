#!/bin/awk -v name=theory_new -f
#

# The do nothing rule
!/^OPTIONS_SRC_FILES = \\|^OPTIONS_TEMPS = \\|^OPTIONS_OPTIONS_FILES = \\|^OPTIONS_SEDS = \\|^OPTIONS_HEADS = \\|^OPTIONS_CPPS = \\/ {print$0}
# Add the name to the correct locations.
/^OPTIONS_SRC_FILES = \\/{print $0; printf "\t%s_options \\\n", name;}
/^OPTIONS_TEMPS = \\/{print $0; printf "\t%s_options.tmp \\\n", name;}
/^OPTIONS_OPTIONS_FILES = \\/{print $0; printf "\t%s_options.options \\\n", name;}
/^OPTIONS_SEDS = \\/{print $0; printf "\t%s_options.sed \\\n", name;}
/^OPTIONS_HEADS = \\/{print $0; printf "\t%s_options.h \\\n", name;}
/^OPTIONS_CPPS = \\/{print $0; printf "\t%s_options.cpp \\\n", name;}
# Add the rule for name_options.
END{printf "%s_options:;\n", name}
# Add the rules for name_options.tmp
END{printf ".PHONY: %s_options.tmp\n", name}
END{printf "%s_options.tmp:\n\techo \"$@\" \"$(@:.tmp=)\"\n\t$(AM_V_GEN)(cp \"@srcdir@/$(@:.tmp=)\" \"$@\" || true)\n", name}
