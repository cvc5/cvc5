#!/bin/awk -v name=theory_new -f
#

# Keep non-matching lines unchanged
!/^OPTIONS_CONFIG_FILES = \\/ {print$0}
# Add *_options.toml to OPTIONS_CONFIG_FILES
/^OPTIONS_CONFIG_FILES = \\/{print $0; printf "\t%s_options.toml \\\n", name;}
