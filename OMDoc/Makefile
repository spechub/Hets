# Makefile
# Stolen from HetCATS/Makefile
#
####################################################################
## Some varibles, which control the compilation

INCLUDE_PATH = ../. ../hxt ../syb-generics ../haifa-lite/src ../hcl/src

HC = ghc

HC_PROF = -prof -auto-all

# remove -fno-warn-orphans for older ghcs
HC_WARN = -Wall -fno-warn-orphans
HC_FLAGS = $(HC_WARN) -package fgl -fglasgow-exts -fno-monomorphism-restriction \
    -fallow-overlapping-instances -fallow-undecidable-instances \
	-ignore-package HaXml-1.12 \
	-H512m


# -ddump-minimal-imports 
# flags also come in via  ../uni/uni-package.conf
# but added it here in case of compilation without uni

HC_INCLUDE = $(addprefix -i, $(INCLUDE_PATH))

UNI_PACKAGE_CONF = $(wildcard ../../uni/uni-package.conf)
ifneq ($(strip $(UNI_PACKAGE_CONF)),)
HC_PACKAGE = -package-conf $(UNI_PACKAGE_CONF) -package uni-davinci \
    -package uni-server -DUNI_PACKAGE

endif

HCI_OPTS = $(HC_FLAGS) $(HC_INCLUDE) $(HC_PACKAGE) $(PFE_FLAGS)

####################################################################
### targets

.PHONY : build integrate profiling

build: integrate
integrate: Integrate.hs HetsInterface.hs XmlHandling.hs OMDocInput.hs Util.hs OMDocDefs.hs Container.hs KeyDebug.hs
	$(HC) --make -o $@ Integrate.hs $(HCI_OPTS) -main-is OMDoc.Integrate.main

profiling: Integrate.hs HetsInterface.hs XmlHandling.hs OMDocInput.hs Util.hs OMDocDefs.hs Container.hs KeyDebug.hs
	$(HC) --make -o integrate Integrate.hs $(HCI_OPTS) $(HC_PROF) -main-is OMDoc.Integrate.main

### interactive
interactive: ghci
ghci: 
	$(HC)i $(HCI_OPTS)

clean:
	rm *.hi *.o integrate
