SHELL=bash

classes: FORCE
	scalac -d bin -classpath bin:lib:lib/jlatexmath.jar:lib/treelayout.jar:. `find src -maxdepth 2 -name "*.scala"`

gui: FORCE
	scala -classpath bin:lib/jlatexmath.jar:lib/treelayout.jar GUI2

clean: FORCE
	rm -rf bin
	mkdir bin

FORCE:
