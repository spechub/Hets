--------------------
-- OWL-API 4 Hets --
--------------------

To build the OWL-API4Hets following software is needed:

- curl 
- Sun Java SDK 1.5 or Sun Java SDK 1.6
- the program "jar" provided by the above SDKs
- unzip
- make

on Ubuntu you can run 

update-alternatives --config jar

to make sure that the correct implementation of jar is used,
other implementation may work, but we do not officially support 
them.

To build the library from scratch (including downloading the required
files from sourceforge) run:

make

to build without downloading run the command:

make small-world

With

make clean

you can cleanup the directory.
