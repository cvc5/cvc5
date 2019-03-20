all: kinds pycvc4

kinds:
	./genkinds.py

pycvc4:
	python setup-pycvc4.py build_ext --inplace

clean:
	rm -rf build
	rm -f pycvc4.cpp
	rm -f pycvc4.cpython-*
