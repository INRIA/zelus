anonymous-dist-src: dist-src-folder
	mv dist-src anonymous-dist-src
	find anonymous-dist-src \( \
		-name "*.ml" -o -name "*.mli" -o -name "*.mll" -o -name "*.mly" \
		-o -name "Makefile" -o -name "readme*" -o -name "README*" \
		-o -name "*.zls" -o -name "*.zli" \) \
		-exec sed -i "/Marc Pouzet/d;/Timothy Bourke/d;/PARKAS/d" {} +
	sed -i "190s/.*/let sensible_default pdesc =/" \
			anonymous-dist-src/compiler/typing/patternsig.ml # this line was mentioning Marc
	sed -i "5s/.*/contact='anonymous'/" anonymous-dist-src/configure # this line was mentioning Marc's email address
	sed -i "8s/.*/<anonymous>./" anonymous-dist-src/tools/readme.md.dist # this line was mentioning Marc's email address
	rm -rf anonymous-dist-src/examples/cantharide/slides # slides with marc's name
	rm -rf anonymous-dist-src/examples/backhoe/exercise # slides with tim's name
	# rm -rf anonymous-dist-src/man # lots of referenes to marc + not up to date anyway
	cd anonymous-dist-src; tar cvzf zelus_anonymous_src.tar.gz *; mv zelus_anonymous_src.tar.gz ..
	rm -rf anonymous-dist-src
