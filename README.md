# Rabit
![GPLv3 licensed](README/GPLv3-badge.png)

Static analysis tool for analysing Rascal Light programs.

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
