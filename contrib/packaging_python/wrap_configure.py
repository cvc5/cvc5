
import subprocess
import sys

from skbuild.cmaker import CMaker

python_version = CMaker.get_python_version()
args = [
	'-DPYTHON_VERSION_STRING:STRING=' + sys.version.split(' ')[0],
	'-DPYTHON_INCLUDE_DIR:PATH=' +
			CMaker.get_python_include_dir(python_version),
	'-DPYTHON_LIBRARY:FILEPATH=' +
			CMaker.get_python_library(python_version),
]

subprocess.check_call(['./configure', *sys.argv[1:], '--name=build_wheel', *args])
