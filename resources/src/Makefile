all:
	happy -gca Javalette/Par.y
	alex -g Javalette/Lex.x
	ghc --make Javalette/Test.hs -o Javalette/Test

clean:
	-rm -f Javalette/*.log Javalette/*.aux Javalette/*.hi Javalette/*.o Javalette/*.dvi

distclean: clean
	-rm -f Javalette/Doc.* Javalette/Lex.* Javalette/Par.* Javalette/Layout.* Javalette/Skel.* Javalette/Print.* Javalette/Test.* Javalette/Abs.* Javalette/Test Javalette/ErrM.* Javalette/SharedString.* Javalette/ComposOp.* Javalette/Javalette.dtd Javalette/XML.* Makefile*
		-rmdir -p Javalette/

