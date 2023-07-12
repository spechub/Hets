GLIB_COMPILE_RESOURCES = $(shell which glib-compile-resources )

.PHONY: resources

src/hetsgui.gresource: src/hetsgui.gresource.xml $(shell $(GLIB_COMPILE_RESOURCES) --generate-dependencies --sourcedir="src/" src/hetsgui.gresource.xml)
	glib-compile-resources --sourcedir="src/" $< --target=$@


