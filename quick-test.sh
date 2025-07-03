#!/bin/bash

# This script downloads and installs Isabelle and qrhl-tool and runs the proofs (in a subdir of the current directory).

# This means that you will end up with a second copy of Isabelle if you already have Isabelle installed.

# It only work on Linux.

# If this script does not work correctly, follow the manual installation instructions from the README.


set -e

VERSION=0.7.3

if ! [ -e quick-test.sh ]; then
  echo You need to run this script in the hksu-verification directory.
  exit 1
fi

if ! [ -d Isabelle2025 ]; then
  echo
  echo '*** Installing Isabelle2025 ***'
  echo
  wget https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz -O isabelle.tgz
  tar xf isabelle.tgz
  rm isabelle.tgz
fi

if ! [ -d afp-2025-03-17 ]; then
  echo
  echo '*** Installing Archive of Formal Proofs (AFP 2025) ***'
  echo
  wget https://www.isa-afp.org/release/afp-2025-03-17.tar.gz -O afp.tgz
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
isabelle-home = ../Isabelle2025
afp-root = ../afp-2025-03-17
EOT

if [ -e ~/.isabelle/Isabelle2025 ]; then
    echo
    echo
    echo "~/.isabelle/Isabelle2025 already exists."
    echo "May be incompatible with the paths configured here."
    echo "Optionally delete it first (unless it has your valuable config!)"
    echo "Press ENTER to continue anyway."
    echo
    read
fi

echo
echo '*** Executing proofs ***'
echo
time qrhl-$VERSION/bin/qrhl all.qrhl

echo
echo '*** Proofs executed successfully ***'
echo
echo "You may want to delete ~/.isabelle/Isabelle2025 if you don't use Isabelle otherwise since it uses a lot of space."
echo
