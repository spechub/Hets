PREFIX=
PROTO=/
GHC_PKG_CONF=/var/lib/ghc/package.conf.d/hets-api-0.100.0.conf
ROOT4BUILD=
GHC_CONF_OPTS=(
	--ghc '--prefix=/$PREFIX'
	--disable-executable-stripping --disable-benchmarks
	'--libdir=/lib/haskell-packages/ghc/lib/x86_64-linux-ghc-8.6.5'
	'--libsubdir=hets-api-0.100.0' '--datadir=share'
	'--datasubdir=hets-api'
	'--haddockdir=/lib/ghc-doc/haddock/hets-api-0.100.0'
	'--docdir=share/doc/hets-api-doc'
	"--package-db=${ROOT4BUILD}/var/lib/ghc/package.conf.d"
	--disable-profiling
)

runhaskell Setup.hs configure ${GHC_CONF_OPTS[@]}
runhaskell Setup.hs build
# rm -rf =${PROTO}/${PREFIX} ; mkdir -p ${PROTO}
# runhaskell Setup.hs copy --destdir=${PROTO}/${PREFIX}
# runhaskell Setup.hs register --gen-pkg-config=${PROTO}/${GHC_PKG_CONF}
runhaskell Setup.hs install
