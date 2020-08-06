This repository contains the formalized proofs from the paper
"Post-Quantum Verification of Fujisaki-Okamoto" by Dominique Unruh.



## Installing qrhl-tool

To execute the proofs, you need the qrhl-tool version 0.5. You need
Linux to run that tool.

The binary distribution is available here:
https://github.com/dominique-unruh/qrhl-tool/releases/download/v0.5/qrhl.zip

To install, simply unpack the archive. This will create a directory
named qrhl-0.5. In the following, let QRHL-DIR denote the full (or
relative) path to that directory.

We have tested this version of qrhl-tool with Ubuntu 19.10 and 20.04,
Java 11 and 13, and Emacs 26.

For more information, see the
[README](https://github.com/dominique-unruh/qrhl-tool/blob/v0.5/README.md)
of qrhl-tool.

qrhl-tool will required about 2GB of disk space (including files
created during the first run which will also be stored inside QRHL-DIR).

You can check whether the tool works correctly by running

```
QRHL-DIR/bin/qrhl QRHL-DIR/examples/example.qrhl
```

NOTE: The first run of the tool will compile Isabelle/HOL (and the
contributed theory files). This will take *very* long. (About 1 hour
on our Intel Core i7 @ 3.4GHz with 12 GB RAM.)  During that initial
build, do not start a second instance of the qrhl-tool or Isabelle/HOL
(using any of the three methods below).



## Installing the proofs

Either clone the [git
repository](https://github.com/dominique-unruh/hksu-verification)
containing the proofs, or download them as an
[archive](https://github.com/dominique-unruh/hksu-verification/archive/master.zip)
and unzip them. We will refer the the directory containing the proofs
as PROOF-DIR.


## Batch mode verification

To verify all proofs on the command line, run

```
QRHL-DIR/bin/qrhl all.qrhl
```

in PROOF-DIR.



## Interactive mode

To verify individual .qrhl files interactively and to edit the proofs, run

```
QRHL-DIR/proofgeneral.sh filename.qrhl
```

in PROOF-DIR.  (filename.qrhl is optional)

This opens the file in ProofGeneral/Emacs.

Push "Use" button in the toolbar to check the whole file, and "Next"
to check the next proof step.



## Running Isabelle

To verify, inspect, or edit .thy files, run Isabelle/HOL using the following command:

```
QRHL-DIR/run-isabelle.sh filename.thy
```

in PROOF-DIR.  (filename.thy is optional)

This opens Isabelle/HOL, preconfigured with the background theories
used by the qrhl-tool.

