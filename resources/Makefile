# Makefile for happiness 
############################################################################ Files of solution.  Add more files as needed.  'jlc.hs'  has to be first!
files=src/jlc.hs src/Javalette.cf Makefile src/Typechecker.hs
part=A
resubmission=1
tarfile = part$(part)-$(resubmission).tar.gz
############################################################################ List of goals not corresponding to file names.
.PHONY : all tar test clean
# 'jlc' is default goal and needs to remain first goal in this file!
# The extra dependency Javalette/Test ensures that the parser is built from Javalette.cf#######################################
############ Rules to build the compiler:
all : $(files) src/Javalette/Test

	ghc --make src/jlc.hs -isrc -o jlc
src/Javalette/Test : src/Javalette/Test.hs src/Javalette/Par.hs src/Javalette/Lex.hs
	ghc --make -isrc $< -o $@
#	happy --ghc --coerce --array --info $<
%.hs : %.y
	happy -gcai $<
%.hs : %.x
	alex --ghc $<
src/Javalette/Test.hs src/Javalette/Lex.x src/Javalette/Par.y : src/Javalette.cf
	bnfc -d $< -o src
#############################################
############ Rules for shipping the solution:
tar : clean $(tarfile)
src : src/**/*
lib : lib/**/*
doc : doc/**/*
tmpdir := $(shell mktemp -d)
$(tarfile) : src/ lib/ doc/ Makefile
	cp -r $^ $(tmpdir)/
	tar -C $(tmpdir) -czhf $@ $^

#################################
############ Rule for testing the 
test: $(tarfile)
	cd .. && cd tester && python3 testing.py ../resources/$^
###############################################
############ Rule for cleaning generated files:
clean :
	-rm -f src/*.hi src/*.o
	-rm -rf src/Javalette/
	-rm -f *.tar.gz jlc
# EOF