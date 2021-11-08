#!/usr/bin/bash

echo "Installing dependencies..."

which javac > /dev/null
if [ $? -ne 0 ]
then
    echo "JDE not found. Install JDE to use Hets."
    exit 0
fi

case $OSTYPE in
    "linux-gnu")
        sudo apt install libglib2.0-dev libcairo2-dev libpango1.0-dev libgtk2.0-dev libglade2-dev libncurses-dev
        sudo apt install postgresql postgresql-server-dev-9.5
        sudo apt install ant
        ;;
    "darwin*")
        brew cask install xquartz
        brew install binutils glib libglade cairo gtk fontconfig freetype gettext spechub/hets/udrawgraph
        brew install ant
        ;;

    *)
        echo "Unsupported OS"
        ;;
esac