# Makefile
# Stolen from HetCATS/Makefile
#
####################################################################
## Some varibles, which control the compilation

INCLUDE_PATH = ../../ ./hxt/ 

HC = ghc

# remove -fno-warn-orphans for older ghcs
HC_WARN = -Wall -fno-warn-orphans
HC_FLAGS = $(HC_WARN) -package fgl -fglasgow-exts -fno-monomorphism-restriction \
    -fallow-overlapping-instances -fallow-undecidable-instances \
	-ignore-package HaXml -ignore-package hxt-5.3 \
	-ignore-package Crypto-2.0.3 -ignore-package HTTP-2005.5.5 \
	-ignore-package NewBinary-0.1
# -ddump-minimal-imports 
# flags also come in via  ../uni/uni-package.conf
# but added it here in case of compilation without uni

HC_INCLUDE = $(addprefix -i, $(INCLUDE_PATH))

UNI_PACKAGE_CONF = $(wildcard ../../../uni/uni-package.conf)
ifneq ($(strip $(UNI_PACKAGE_CONF)),)
HC_PACKAGE = -package-conf $(UNI_PACKAGE_CONF) -package uni-davinci \
    -package uni-server -DUNI_PACKAGE

endif

HCI_OPTS = $(HC_FLAGS) $(HC_INCLUDE) $(HC_PACKAGE) $(PFE_FLAGS)

####################################################################
### targets

build: integrate
integrate: Integrate.hs HetsInterface.hs OmdocDevGraph.hs
	$(HC) --make -o $@ Integrate.hs $(HCI_OPTS) -main-is Integrate

### interactive
interactive: ghci
ghci: 
	$(HC)i $(HCI_OPTS)

clean:
	rm *.hi *.o integrate
