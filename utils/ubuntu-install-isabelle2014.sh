#!/bin/bash
if [[ $EUID -ne 0 ]]; then
   echo "This script must be run as root" 1>&2
   exit 1
fi

ISABELLE_TGZ=Isabelle2014_linux.tar.gz

ISABELLE_DIR=/usr/share/Isabelle2014

wget http://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/$ISABELLE_TGZ -O - \
  | tar -xzf - -v -C /usr/share

sed -i~ '128iinit_component \"\$ISABELLE_HOME/contrib/ProofGeneral-4.2-2\"' \
  $ISABELLE_DIR/etc/settings

$ISABELLE_DIR/bin/isabelle components -a
$ISABELLE_DIR/bin/isabelle install /usr/bin
$ISABELLE_DIR/bin/isabelle build -s -b -v HOLCF

ISABELLE_UNINST=/usr/bin/isabelle_uninstall.sh

echo "creating uninstall script: $ISABELLE_UNINST"

cat > $ISABELLE_UNINST <<EOF
#!/bin/bash
if [[ $EUID -ne 0 ]]; then
   echo "This script must be run as root" 1>&2
   exit 1
fi
rm -rf $ISABELLE_DIR
rm /usr/bin/isabelle
rm /usr/bin/isabelle_*
EOF

chmod a+x $ISABELLE_UNINST
