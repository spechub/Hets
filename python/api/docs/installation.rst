Installation
============

.. contents::
    :local:

Docker
------
The simplest way to use the hets api is the docker image `spechub2/hets-api <https://hub.docker.com/repository/docker/spechub2/hets-api>`_. Use one of the following commands to get an interactive session:

.. code-block:: bash

    # Get an interactive python session
    docker run -it --rm spechub2/hets-api python

    # Get an interactive ghci session
    docker run -it --rm spechub2/hets-api ghci

    # Get an interactive bash session
    docker run -it --rm spechub2/hets-api bash

Optionally mount volumes to access your local files inside the docker container. The following command starts an interactive python session with the current working directory mounted inside the container at ``./files/``

.. code-block:: bash

    docker run -it --rm -v  $PWD:/home/hets/files spechub2/hets-api python


Prerequisites
-------------

Hyphen
""""""

The python hets API utilises `hyphen <https://github.com/tbarnetlamb/hyphen/>`_ to access the haskell interface from python. To install it, first install its dependencies::

    sudo apt install git python3-dev ghc-dynamic ghc python3 python3-pip libghc-ghc-paths-dev libghc-parser-combinators-dev libghc-unordered-containers-dev

Then, clone the source code and build the project::

    git clone https://github.com/tbarnetlamb/hyphen.git
    cd hyphen
    python3 hyphen/build-extn.py

Create a ``pyproject.toml`` in the root folder of the project with the following content

.. code-block:: toml

    [project]
    name = "hyphen"
    version = "0.1.0.0"

    [tool.setuptools]
    packages = [ "hyphen" ]

    [tool.setuptools.package-data]
    "*" = [ "hslowlevel.*" ]

Finally install hyphen with ::

    python3 -m pip install .

.. hint::
    If you get errors during the installation try updating setuptools with
    ``python3 -m pip install --upgrade pip setuptools``


Haskell and python API
----------------------

To build the haskell API packages from the hets ppa are required. Add the ppa with ::

    sudo apt install -y software-properties-common apt-utils make
    sudo apt-add-repository -y ppa:hets/hets
    sudo apt update

Then, install the dependencies for building the library ::

    sudo apt install openjdk-8-jdk-headless ant cabal-install ksh perl-base tar xz-utils zip libmysqlclient-dev ghc-haddock libghc-missingh-dev ghc>=7.10.3 happy libghc-mutable-containers-dev libghc-haxml-dev libghc-tar-dev libghc-random-dev libghc-parsec3-dev libghc-fgl-dev libghc-xml-dev libghc-http-dev libghc-warp-dev libghc-wai-extra-dev libghc-split-dev libghc-file-embed-dev libghc-monad-logger-dev libghc-yaml-dev libghc-esqueleto-dev>=2.5.3 libghc-persistent-dev>=2.7.0 libghc-persistent-template-dev>=2.5.2 libghc-persistent-postgresql-dev>=2.6.1 libghc-persistent-sqlite-dev>=2.6.2 libghc-utf8-string-dev libghc-relation-dev libghc-persistent-mysql-dev libghc-hexpat-dev libghc-aterm-dev libghc-xeno-dev libghc-heap-dev

Clone the hets repository ::

    git clone https://github.com/spechub/Hets.git
    cd Hets

Build the library ::

    make derived
    runhaskell Setup.hs configure
        --ghc --prefix=/
        --disable-executable-stripping
        --disable-benchmarks
        --libdir=/lib/haskell-packages/ghc/lib/x86_64-linux-ghc-8.6.5
        --libsubdir=hets-api-0.100.0
        --datadir=share
        --datasubdir=hets-api
        --haddockdir=/lib/ghc-doc/haddock/hets-api-0.100.0
        --docdir=share/doc/hets-api-doc
        --package-db=/var/lib/ghc/package.conf.d
        --disable-profiling
        lib:Hets
    runhaskell Setup.hs build -j$(nproc) lib:Hets
    sudo runhaskell Setup.hs install

Finally, install the python API ::

    python3 -m pip install ./python/api


Provers and Library
-------------------

It is recommend to install additional tools for automatic theorem proving as well as to download basic libraries and other examples

.. code-block:: bash

    # Install provers. Choose any subset.
    apt-get install -y cvc-47 darwin eprover fact++ maude minisat pellet spass vampire yices z3 zchaff

    # Download the hets library
    git clone https://github.com/spechub/Hets-lib.git
    export HETS_LIB=$(realpath Hets-lib)


