# Rascal Light
An expressive subset of [Rascal](www.rascal-mpl.org) with a formal semantics is described in [The Formal Semantics of Rascal Light](https://arxiv.org/abs/1703.02312).

# Rabit
![GPLv3 licensed](README/GPLv3-badge.png)

A static analysis tool for analysing Rascal Light programs, based on Abstract Interpretation.
It is an artefact related to the work presented in [Verification of High-Level Transformation Languages using Inductive Refinement Types](https://dl.acm.org/citation.cfm?doid=3278122.3278125) (joint work with Thomas P. Jensen, Aleksandar S. Dimovski and Andrzej Wasowski).

### Prerequisites

* Java (tested with OpenJDK 11)
* Scala (tested with 2.12.7)
* SBT (tested with 1.2.4)
* Internet access for SBT to download dependencies

### Installation

* Use `git lfs pull` to get Rascal binaries required for parsing Rascal files in the project.

### To build:
Use `sbt compile` to get dependencies and compile the project.

### To run tests:
Call `sbt test` in the project directory, to run unit tests and evaluation.
See the `log` directory for detailed output.
