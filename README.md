## What is this?
*satsuma* is a SAT preprocessor with the goal of automatically tackling *symmetry* in CNF formulas.
The goal of the tool is to treat symmetry as well as possible, while incurring only little overhead.

## Compilation
The project depends on [dejavu](https://www.automorphisms.org) and [boost](https://www.boost.org/).
Using *cmake*, all dependencies should however be automatically satisfied, if *boost* is available:
```text
cmake .
make satsuma
```
Compilation produces a binary *satsuma*. It accepts a DIMACS CNF formula as input, and outputs the formula with additional symmetry breaking constraints. 
You may consult `satsuma -h` for more options.

## Usage

Let's say we have a CNF SAT instance `hole010.cnf`, for which we want to apply symmetry breaking.
An example use of  *satsuma* with the SAT solver *cryptominisat* may look as follows:
```text 
satsuma -f hole010.cnf > hole010.break.cnf
cryptominisat5 hole010.break.cnf
```
This will pass `hole010.cnf` to satsuma, which will attempt to break symmetries, and write the resulting formula to the file `hole010.break.cnf`.
The formula `hole010.cnf` is satisfiable, if and only if `hole010.break.cnf` is satisfiable.
We can then pass `hole010.break.cnf` to a SAT solver of choice, in the case above to cryptominisat.

There are more options available to influence the generation of symmetry breaking constraints. 
You may see a description with `satsuma -h`.

## Bugs & Feedback
If you encounter any bugs or have any feedback to share, please feel free to reach out to me at\
`markus.anders (at) kuleuven.be`.

## Publications
The design of *satsuma* is based on the following papers. If you use the tool in your research work, please cite one of the papers.

"Satsuma: Structure-based Symmetry Breaking in SAT" (SAT '24)\
by Markus Anders, Sofia Brenner, Gaurav Rattan

"Algorithms Transcending the SAT-Symmetry Interface" (SAT '23)\
by Markus Anders, Mate Soos, Pascal Schweitzer

"SAT Preprocessors and Symmetry" (SAT '22)\
by Markus Anders

## Related Software
The tool is built on top of the practical graph isomorphism solver [dejavu](https://www.automorphisms.org). 
Many of the implemented procedures are descended from the symmetry breaking tool [BreakID](https://bitbucket.org/krr/breakid/).



## License
All of the code is licensed under the MIT license (see `LICENSE` for the main copyright notice). 
The files `robin_set.h`, `robin_hash.h`, and `robin_growth_policy.h` are by Thibaut Goetghebuer-Planchon, see the respective files for more information. 
