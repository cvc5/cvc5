#!/bin/awk -v name=theory_new -f
#

# Add the name to the correct locations.
/^OPTIONS_CONFIG_FILES = \\/{print $0; printf "\t%s_options.toml \\\n", name;}
