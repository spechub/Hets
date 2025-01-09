GLIB_COMPILE_RESOURCES = $(shell which glib-compile-resources )

.PHONY: resources

hetsgui.gresource: hetsgui.gresource.xml $(shell $(GLIB_COMPILE_RESOURCES) --generate-dependencies --sourcedir="./" ./hetsgui.gresource.xml)
	glib-compile-resources --sourcedir="./" $< --target=$@


