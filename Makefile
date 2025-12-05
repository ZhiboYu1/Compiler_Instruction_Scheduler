# Compiler
JAVAC = javac
JAVA = java
JAR = jar

SRC_DIR = src
BIN_DIR = bin
# Find all Java sources recursively
SOURCES := $(shell find $(SRC_DIR) -name "*.java")

# Main class
MAIN = Main

# Targets
all: build

build: lab3.jar schedule

# Compile all .java files at once into proper package folders
classes:
	mkdir -p $(BIN_DIR)
	$(JAVAC) -d $(BIN_DIR) $(SOURCES)

lab3.jar: classes
	$(JAR) cfe lab3.jar $(MAIN) -C $(BIN_DIR) .

schedule:
	echo '#!/bin/bash' > schedule
	echo 'java -jar lab3.jar "$$@"' >> schedule
	chmod a+x schedule

clean:
	rm -rf $(BIN_DIR) lab3.jar schedule

#create zy53.tar file under lab3-dist directory
dist:
	mkdir -p ../lab3-dist
	cp Makefile schedule README ../lab3-dist/
	cp -r src ../lab3-dist/
	cd ../lab3-dist && tar cvf ../zy53.tar .
	pwd
	mv ../zy53.tar ../l3auto/TarFileGoesHere/