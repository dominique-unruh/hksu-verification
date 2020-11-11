#!/bin/bash

# This script downloads and installs Isabelle and qrhl-tool and runs the proofs (in a subdir of the current directory).

# This means that you will end up with a second copy of Isabelle if you already have Isabelle installed.

# It only work on Linux.

# If this script does not work correctly, follow the manual installation instructions from the README.


set -e

VERSION=0.6

if ! [ -e quick-test.sh ]; then
  echo You need to run this script in the hksu-verification directory.
  exit 1
fi

if ! [ -d Isabelle2019 ]; then
  echo
  echo '*** Installing Isabelle2019 ***'
  echo
  wget https://isabelle.in.tum.de/website-Isabelle2019/dist/Isabelle2019_linux.tar.gz -O isabelle.tgz
  tar xf isabelle.tgz
  rm isabelle.tgz
fi

if ! [ -d afp-2019-08-19 ]; then
  echo
  echo '*** Installing Archive of Formal Proofs (AFP 2019) ***'
  echo
  wget https://sourceforge.net/projects/afp/files/afp-Isabelle2019/afp-2019-08-19.tar.gz/download -O afp.tgz
  tar xf afp.tgz
  rm afp.tgz
fi

if ! [ -d qrhl-$VERSION ]; then
  echo
  echo "*** Installing qrhl-tool $VERSION ***"
  echo
  wget https://github.com/dominique-unruh/qrhl-tool/releases/download/v$VERSION/qrhl.zip -O qrhl.zip
  unzip qrhl.zip
  rm qrhl.zip
fi

echo
echo '*** Configuring qrhl-tool ***'
echo
cat> qrhl-$VERSION/qrhl-tool.conf <<EOT
isabelle-home = ../Isabelle2019
afp-root = ../afp-2019-08-19
isabelle-user = ../.isabelle
EOT

echo
echo '*** Executing proofs ***'
echo
time qrhl-$VERSION/bin/qrhl all.qrhl

echo
echo '*** Proofs executed successfully ***'
echo
