# Hets (The heterogeneous tool set)

Hets is a parsing, static analysis and proof management tool incorporating various provers and different specification languages, thus providing a tool for heterogeneous specifications. Logic translations are first-class citizens.

### Supported languages

* general-purpose logics: [Propositional](http://en.wikipedia.org/wiki/Propositional_calculus), [QBF](http://en.wikipedia.org/wiki/QBF), [TPTP](http://www.tptp.org/)/SoftFOL, [CASL](http://www.informatik.uni-bremen.de/cofi/index.php/CASL) (FOL), [HasCASL](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/HasCASL/) (HOL)
* logical frameworks: [Isabelle](http://www.cl.cam.ac.uk/research/hvg/Isabelle/), [LF](http://en.wikipedia.org/wiki/LF_%28logical_framework%29), DFOL
* modeling languages: [Meta-Object Facility (MOF)](https://en.wikipedia.org/wiki/Meta-Object_Facility), [Query/View/Transformation (QVT)](https://en.wikipedia.org/wiki/QVT)
* ontologies and constraint languages: [OWL](http://www.w3.org/TR/owl2-overview/), [CommonLogic](https://en.wikipedia.org/wiki/Common_Logic), [RelScheme](http://en.wikipedia.org/wiki/Database_schema), ConstraintCASL
* reactive systems: CspCASL, [CoCASL](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/CoCASL/), ModalCASL, [Maude](http://maude.cs.uiuc.edu/)
* programming languages: [Haskell](http://www.haskell.org/), [VSE](https://link.springer.com/chapter/10.1007/3-540-60973-3_92)
* logics of specific tools: Reduce, DMU ([CATIA](http://en.wikipedia.org/wiki/CATIA))

### The following provers have been connected to Hets:

* [minisat](http://minisat.se/) and [zChaff](http://www.princeton.edu/~chaff/zchaff.html), which are SAT solvers,
* [SPASS](http://www.spass-prover.org/), [Vampire](http://en.wikipedia.org/wiki/Vampire_%28theorem_prover%29), [Darwin](http://combination.cs.uiowa.edu/Darwin/), [Hyper](https://link.springer.com/chapter/10.1007/978-3-540-73595-3_37) and MathServe, which are automatic first-order theorem provers,
* [Pellet](https://github.com/stardog-union/pellet) and [Fact++](http://owl.man.ac.uk/factplusplus/), description logic tableau provers,
* [Leo-II](http://page.mi.fu-berlin.de/cbenzmueller/leo/) and [Satallax](http://www.ps.uni-saarland.de/~cebrown/satallax/), automated higher-order provers,
* [Isabelle](http://www.cl.cam.ac.uk/Research/HVG/Isabelle/), an interactive higher-order theorem prover,
* [CSPCASL-prover](http://dx.doi.org/10.1016/j.entcs.2009.08.018), an Isabelle-based prover for CspCASL,
* [VSE](https://link.springer.com/chapter/10.1007/3-540-60973-3_92), an interactive prover for dynamic logic.

The structuring constructs of the heterogeneous specification language are those of the [OMG](http://www.omg.org)-standardised [Distributed Ontology, Model and Specification Language (DOL)](http://dol-omg.org), extending those of [CASL](http://www.informatik.uni-bremen.de/cofi/index.php/CASL). However, Hets can also read other structuring constructs, like those of Haskell, Maude or OWL. All these are mapped to so-called development graphs and processed with a proof calculus for heterogeneous development graphs that allows to decompose global proof obligations into local ones (during this, Hets also needs to compute [colimits](http://en.wikipedia.org/wiki/Limit_%28category_theory%29#Colimits_2) of theories over the involved logics).

Hets is based on a graph of logics and logic translations. The overall architecture is depicted below. Adding new logics and logic translations to Hets can be done with moderate effort by adding some Haskell code to the Hets source. With the [Latin](https://link.springer.com/chapter/10.1007/978-3-642-22673-1_24) project, this becomes much easier: logics (and in the near future also logic translations) can be declaratively specified in LF.

![Architecture of the heterogeneous tool set Hets](https://github.com/spechub/attachment/raw/a0f26aadac374988f7bee3e191e95ca30e7be511/hets2010.png)

### User Documentation

A good starting point is the [Hets user guide](https://github.com/spechub/Hets/blob/master/doc/UserGuide.pdf) and the [Hets user guide for Common Logic users](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/UserGuideCommonLogic.pdf). Furthermore two vidoes showing a heterogeneous proof are available:

* [A small video showing a heterogeneous proof](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/hets.m2v)
* [A new video (H.264-Codec) showing a heterogeneous proof](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/Hets.mov)

For a formal introduction to hets see the introductory paper [The Heterogeneous Tool Set](http://iks.cs.ovgu.de/~till/papers/hets-paper.pdf) by Till Mossakowski, Christian Maeder, Klaus Lüttich and Stefan Wölfl. For more in-depth information about Hets see the thesis [Heterogeneous specification and the heterogeneous tool set](http://iks.cs.ovgu.de/~till/papers/habil.pdf) by Till Mossakowski.

For questions related to hets there is a [mailing list](http://www.informatik.uni-bremen.de/mailman/listinfo/hets-users).

## Using Hets

You can try out Hets using the [Web-based interface](http://rest.hets.eu/)
or install it easily in a [docker container](https://github.com/spechub/Hets/wiki/How-to-use-the-Hets-Docker-Container).

### Installing Hets under Ubuntu

#### The basic system
```
sudo apt-get install software-properties-common
sudo dpkg --add-architecture i386			# not needed for hets-server
sudo apt-add-repository ppa:hets/hets
sudo apt-get update
sudo apt-get install hets-desktop
```

* for using Hets as a server providing a RESTful interface, use hets-server. This is a smaller version without GUI dependencies. Note that also hets-desktop can be used as as server.

#### Hets development
For Hets development additionally type in
```
sudo apt-add-repository -s "deb http://ppa.launchpad.net/hets/hets/ubuntu bionic main"
sudo apt-get update
sudo apt-get build-dep hets-desktop
```
Replace 'bionic' with the Ubuntu version that you use.
The Hets sources should be obtained from the git repository (see the end of this page).

### Installing Hets under Archlinux
We provide the AUR-packages [`hets-desktop-bin`](https://aur.archlinux.org/packages/hets-desktop-bin/) and [`hets-server-bin`](https://aur.archlinux.org/packages/hets-server-bin/) to install 64 bit binaries of Hets/Hets-server.
If you would like to compile Hets yourself, you can install one of the AUR-packages [`hets-desktop`](https://aur.archlinux.org/packages/hets-desktop/) and [`hets-server`](https://aur.archlinux.org/packages/hets-server/).

### Installing Hets under OS X/macOS (10.9 (Mavericks) and greater)
* Install Homebrew: See [https://brew.sh](https://brew.sh)
* Install Java: `brew cask install java`
* Install the Hets-Repository to Homebrew: `brew tap spechub/hets`
* Only for Hets-Desktop, install X11: `brew cask install xquartz`
* Either install hets-desktop: `brew install spechub/hets/hets-desktop`
* Or install hets-server: `brew install spechub/hets/hets-server`

This installs Hets along with all its dependencies.
Some of the dependencies are optional, but recommended, especially the provers.
You can install Hets without these by adding a flag `--without-*` where `*` is one of these recommended dependencies.
For instance, you can run `brew install spechub/hets/hets-desktop --without-leo2` to skip the installation of Leo2.
For a list of these flags, run `brew info hets-desktop`.

### Hets libraries
Download the [Hets libraries](https://github.com/spechub/Hets-lib) and set $HETS_LIB to the folder containing these.

### Quickstart

Hets is called with
```
hets filename
```
or
```
hets -g filename
```
For entering the command line mode, just call
```
hets -I
```
For a short description of the options, call
```
hets --help
```

### Restful Interface
See [RESTful Interface](https://github.com/spechub/Hets/wiki/RESTful-Interface)


### Emacs Mode for CASL specifications

To support writing CASL specifications we have an [emacs mode](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/emacs_mode)

### Including specifications in LaTeX documents

With the option "-o pp.tex" hets can produce nice LaTeX output from your specifictions that can be embedded in your publications using the [hetcasl.sty](http://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/hetcasl.sty) style file.

## Development

A good starting point is the code documentation for [Hets - the Heterogeneous Tool Set](http://hets.eu/docs/).

Since Hets is rather large and complex we recommend following the interactive session in [Debugging and Testing Hets](https://github.com/spechub/Hets/wiki/Debugging-and-Testing-Hets) to get familiar with the central datastructures of Hets.

The formal background and the general structure of Hets is described in chapter 7 of [Heterogeneous specification and the heterogeneous tool set](http://iks.cs.ovgu.de/~till/papers/habil.pdf).

### Haskell

Hets is written in [Haskell](http://www.haskell.org), and is compiled using [GHC](http://www.haskell.org/ghc) using a couple of language extensions. Among the Haskell [books and tutorials](http://www.haskell.org/haskellwiki/Books_and_tutorials) we recommend [Real World Haskell](http://book.realworldhaskell.org/).
The [language definition](http://www.haskell.org/onlinereport) covers the Haskell98 standard which we are supposed to stick to in most cases. Make sure that you are familiar with at least the most common [library functions of the Prelude](http://www.haskell.org/onlinereport/prelude-index.html).
For searching or looking up any [library functions](http://www.haskell.org/ghc/docs/latest/html/libraries) you may also try [Hoogle](http://www.haskell.org/hoogle).

Also look into [programming guidelines](http://www.haskell.org/haskellwiki/Programming_guidelines) and [things to avoid in Haskell](http://www.haskell.org/haskellwiki/Things_to_avoid).

### Dependencies
Dependencies can be installed as specified in [Hets Development](#hets-development)

### Contributing changes

Before committing haskell source files you may check compliance to the programming guidelines:
* Use scan which can be installed by `cabal install scan`.
* The comments in your haskell sources should not cause `haddock` to fail. After `make` (for re-compiling changed sources) `make docs` will call `haddock`.
* Also check your source with hlint which you may install by `cabal install hlint`.

Also have a look at the current [Release Notes](https://github.com/spechub/Hets/releases/latest), [Debugging and Testing Hets](https://github.com/spechub/Hets/wiki/Debugging-and-Testing-Hets),[Code Review](https://github.com/spechub/Hets/wiki/Code-Review) and [Branching](https://github.com/spechub/Hets/wiki/Branching).

If you want to participate in the Hets development feel free to tell us via our [mailing list](http://www.informatik.uni-bremen.de/mailman/listinfo/hets-devel) for Hets developers.

If you wish to make larger changes we generally recommend [forking](https://help.github.com/articles/fork-a-repo) this repository. You can however request access to this repository if you plan on contributing regularly.


### Build Hets using Stack
* Get the git repository and its submodules
    ```
    git clone https://github.com/spechub/Hets.git
    cd Hets
    git submodule update --init --recursive
    ```
* [Install Stack](https://docs.haskellstack.org/en/stable/install_and_upgrade) (use the generic Linux option if you are on Ubuntu).
* Install build- and GUI-dependencies
  * Ensure a JDK is installed (version >= 1.7)
  * Automatically install dependencies with
  ```
  ./install_dependencies.sh
  ```
  * Manual install
    * Ubuntu:
      ```
      sudo apt install libglib2.0-dev libcairo2-dev libpango1.0-dev libgtk2.0-dev libglade2-dev libncurses-dev
      sudo apt install postgresql postgresql-server-dev-9.5
      sudo apt install ant
      ```
    * macOS:
      ```
      brew cask install xquartz
      brew install binutils glib libglade cairo gtk fontconfig freetype gettext spechub/hets/udrawgraph
      brew install ant
      ```
* If you work with OWL ontologies, build OWL tools before running hets. Warnings produced by stack (like "You are not the owner of '/.stack-work/'. Aborting to protect file permissions")
  can be ignored as the script doesn't use ghc or stack in general.
  ```
  sudo make install-owl-tools
  ```
* Setup Stack for Hets (this needs to be done only once after every time the stack.yaml has changed):
  ```
  stack setup
  make restack
  ```
  When you invoke `make` for the first time, this will give you warnings about not having found a compiler ("No compiler found, expected minor version match with ghc-...").
  Don't let this discourage you - it's normal.
  Running `make stack` will take care of it and install the compiler.
  Running `make restack` does the same thing, as `make stack`, but needs to be run every time the dependencies (`stack.yaml`) change.
* Build Hets with one of the following:
  ```
    make
    make hets
    make hets_server
    make docs
  ```
  This uses Stack to build the Hets[-Server] binary (or, in the last case, the Hets code documentation, using haddock).
  During this process, the specified version of GHC is installed in the user directory, all dependencies are built and finally, the Hets[-Server] binary is compiled.
* If you want to clean the extra-dependencies of Stack that are put into the Hets working directory, run
  ```
  make clean_stack
  ```


## Troubleshooting & Useful Tools

## Hints for contributors switching from svn to git

* We recommend the [Git - SVN Crash Course](http://git-scm.com/course/svn.html).
* For github specific info on checking out this repository see [Fetching a remote](https://help.github.com/articles/fetching-a-remote).

## License

The Hets source code is licensed under the GPLv2 or higher
