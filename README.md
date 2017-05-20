# Directory Structure

The are three top-level directories:
* AbstractPlatform (The TAP)
* Sanctum (Sanctum Model)
* SGX (SGX model).

# Setup

First, you will need to install [boogie](https://github.com/boogie-org/boogie). You'll also need to set the BOOGIE environment variable to point to the boogie executable on your system. For example, I set it as follows:

    $ export BOOGIE="mono ~/research/verification/boogie/Binaries/Boogie.exe"

# Abstract Trusted Platform

The trusted abstract platform (TAP) is in AbstractPlatform.

## Running The TAP Proofs

    $ cd AbstractPlatform
    $ make

Don't forget to set $BOOGIE

# Refinement Proofs

The code is in SanctumRefinementProof.bpl and SGXRefinementProof.bpl.

## Running the Refinement Proofs.
    
Just run make!

# Sanctum Model

Sanctum contains all of the Sanctum model.

* Sanctum/Common defines common, types, constants and functions.
* Sanctum/Host/OS.bpl contains functions that would be implemented in the operating system.
* Sanctum/MMU contains the MMU. See below for details.
* Sanctum/Sanctum contains the Sanctum model and non-interference proofs.

## Executing the Proofs

To run all proofs for the Sanctum model (including the MMU proof), just run make in Sanctum.

    $ cd Sanctum
    $ make

Running all the proofs may take several minutes. (There are a couple of extra proofs that aren't mentioned in the paper here.)

# SGX Model
    
The SGX model is in SGX.  There is nothing to run here.

