This repository contains the formalized proofs from the paper
"Post-Quantum Verification of Fujisaki-Okamoto" by Dominique Unruh
(https://eprint.iacr.org/2020/962).



## Installing qrhl-tool

To execute the proofs, you need the qrhl-tool version 0.6.
It supports Linux, OS/X, and Windows.

(As an alternative to the following installation instructions, Linux shell script `quick-test.sh`.
See the comments in that file.)

The binary distribution is available here:
https://github.com/dominique-unruh/qrhl-tool/releases/download/v0.6/qrhl.zip

For installation instructions, see the
[README](https://github.com/dominique-unruh/qrhl-tool/blob/v0.6/README.md)
of qrhl-tool. 

In the following, let `QRHL-DIR` denote the installation directory of qrhl-tool.

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

