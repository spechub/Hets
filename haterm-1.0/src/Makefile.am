EXTRA_DIST =\
	ATermAbstractSyntax.hs\
	ATermReadWrite.hs\
	ATermConversion.hs\
	ATermLib.hs\
	Test.ds Test.hs Test.script

check-local:
	hugs -98 +o -P${top_srcdir}/src:\
	  ${srcdir}/Test.hs < ${srcdir}/Test.script


# For developers only:

regenerate-tests: Test.hs

%.hs: %.ds
	DrIFT $< > $@ 