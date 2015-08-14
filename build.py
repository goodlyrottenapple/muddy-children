#!/usr/bin/env python
import os,sys,time,getopt,shlex, shutil
from subprocess import Popen, PIPE
from glob import glob

LAST_COMPILE_TIME = 0

def cmd_output_throws_error(flags, response, err, error_msg):
	if "error" in response.lower() or "bad session" in response.lower() or "unfinished session" in response.lower():
		if "verbose" in flags: print response
		print "ERROR :", error_msg
		return True
	if err is not None and ("error" in err.lower() or "bad session" in err.lower()):
		if "verbose" in flags: print err
		print "ERROR :", error_msg
		return True
	if "verbose" in flags: print response
	return False

def usage():
	print "This is a Display Calculus project build script v0.1"
	print "Usage: ./build -c <calculus_file> -p <OUTPUT_PATH> -t <templates_path>"


def compile_scala(flags, classes):

	if not os.path.exists("bin"):
		os.makedirs("bin")

	pathsJava = glob("src/scala/*.java")
	pathsJava += glob("src/scala/gui/*.java")

	paths = glob("src/scala/*.scala")
	paths += glob("src/scala/gui/*.scala")
	libs = glob("lib/*.jar")
	if not "force" in flags:
		paths = [p for p in paths if int(os.path.getmtime(p)) > LAST_COMPILE_TIME]

	
	libs.append(".")
	libs.append("bin")

	fPathsJava = []
	if classes:
		for c in classes:
			for p in pathsJava:
				if c in p: fPathsJava.append(p)
	else : fPathsJava = pathsJava


	fPaths = []
	if classes:
		for c in classes:
			for p in paths:
				if c in p: fPaths.append(p)
	else : fPaths = paths

	for p in fPathsJava:
		print "compiling java:", p

	for p in fPaths:
		print "compiling:", p

	if fPathsJava:
		cmd = "javac -d bin -classpath " + ":".join(libs) + " " + " ".join(fPathsJava)
		response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()
		if cmd_output_throws_error(flags, response, err, "Build failed!"): return False


	if fPaths:
		cmd = "scalac -d bin -classpath " + ":".join(libs) + " " + " ".join(fPaths)
		response,err = Popen(shlex.split(cmd), stdout=PIPE, stderr=PIPE).communicate()
		if cmd_output_throws_error(flags, response, err, "Build failed!"): return False

		file = open('last_compile.txt', 'w')
		file.write( str(int(time.time())) )
		file.close()


def main(argv):
	try:
		opts, args = getopt.getopt(argv, "fvc:", ["force", "verbose", "class"])
	except getopt.GetoptError:
		usage()
		sys.exit(2)

	global LAST_COMPILE_TIME
	#user flag settings
	BUILD_FLAGS = []
	CLASSES = []

	for opt, arg in opts:
		if opt in ("-f", "--force"):
			BUILD_FLAGS.append("force")
		elif opt in ("-v", "--verbose"):
			BUILD_FLAGS.append("verbose")
		elif opt in ("-c", "--class"):
			CLASSES = arg.split(",")
	
	if os.path.exists("last_compile.txt"):
		file = open('last_compile.txt', 'r')
		LAST_COMPILE_TIME = int( file.readline() )
		file.close()

	#first compile the generator for core calculus
	compile_scala(BUILD_FLAGS, CLASSES)
	

if __name__ == "__main__":
	main(sys.argv[1:])