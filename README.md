*satsuma* is a SAT preprocessor for automatically handling *symmetries* in CNF formulas. Its goal is to exploit symmetry as effectively as possible while adding only little preprocessing overhead. Given a DIMACS CNF formula, *satsuma* produces an equisatisfiable formula that can then be passed to any SAT solver.

## Compilation
Using *cmake*, the tool can be built as follows:
```text
cmake .
make satsuma
```
This produces a binary *satsuma*. The project depends on [dejavu](https://www.automorphisms.org), 
but this dependency should be automatically met when running *cmake*.

## Usage
Satsuma supports *two distinct approaches* to symmetry breaking: 
1. Fixing and 
2. Lex-Leader constraints. 

Suppose we have a CNF SAT instance `hole010.cnf`, for which we want to handle symmetry before solving.
An example use of  *satsuma* with the SAT solver *cryptominisat* may look as follows. 

Using fixing:
```text 
satsuma fix hole010.cnf > hole010.break.cnf
cryptominisat5 hole010.break.cnf
```

Using lex-leader constraints:
```text 
satsuma lex hole010.cnf > hole010.break.cnf
cryptominisat5 hole010.break.cnf
```

Each of these passes `hole010.cnf` to satsuma, which will write the resulting formula to the file `hole010.break.cnf`.
The formula `hole010.cnf` is satisfiable, if and only if `hole010.break.cnf` is satisfiable.
We then pass `hole010.break.cnf` to a SAT solver of choice, in the case above to cryptominisat.

Additional options are available to. Run `satsuma -h` to see a full list. 

The default settings aim to provide a good balance between overhead and effectiveness. 
However, the tool can be configured in many ways to attempt weaker, stornger, or diversified breaking. 
Which parameters work best will depend on the instance, mode, and SAT solver used. 
Here are some settings to try: 
```text 
satsuma lex --opt -f formula.cnf
satsuma lex --opt-reopt -f formula.cnf
satsuma lex --opt-reopt --opt-conjugations 5000 -f formula.cnf  // (or >5000)
satsuma lex --schreier-cuts -f formula.cnf
```

## Proofs 
In *fixing* mode, the tool can output *SR*, *binary SR*, and *VeriPB proofs. 
In lex-leader mode, the tool can output *VeriPB* proofs.
Note that in order to obtain a full proof, the proof of *satsuma* then needs to be combined 
with a proof of the SAT solver.

For example, running 
```text 
satsuma fix hole010.cnf --proof-file proof.out > hole010.break.cnf
```
will output a binary SR proof to the file `proof.out`.

## Bugs & Feedback
If you encounter any bugs or have any feedback to share, please feel free to reach out to me at\
`anders (at) cs.uni-kl.de`.

## Publications
The design of *satsuma* is based on the following papers. 
If you use the tool in your research work, please cite at least one of the papers.

"Satsuma: Structure-based Symmetry Breaking in SAT" at SAT '24 ([paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.4), [bibtex](https://dblp.uni-trier.de/rec/conf/cp/AndersBR24.html?view=bibtex))\
by Markus Anders, Sofia Brenner, Gaurav Rattan

"Algorithms Transcending the SAT-Symmetry Interface" at SAT '23 ([paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.1), [bibtex](https://dblp.uni-trier.de/rec/conf/sat/AndersSS23.html?view=bibtex))\
by Markus Anders, Mate Soos, Pascal Schweitzer

"SAT Preprocessors and Symmetry" at SAT '22 ([paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2022.1), [bibtex](https://dblp.uni-trier.de/rec/conf/sat/Anders22.html?view=bibtex))\
by Markus Anders

The symmetry fixing algorithm is described in the following papers.

"Simplify, Break, Order, Repeat" at SAT '26\
by Markus Anders, Cayden Codel, Marijn J.H. Heule

"Orbitopal Fixing in SAT" at TACAS '26 ([paper](https://arxiv.org/abs/2601.16855), [bibtex](https://dblp.uni-trier.de/rec/conf/tacas/AndersCH26.html?view=bibtex))\
by Markus Anders, Cayden Codel, Marijn J.H. Heule

## Related Software
The tool heavily uses the practical graph isomorphism solver [dejavu](https://www.automorphisms.org). 
Some of the implemented procedures are descended from 
- the stable set solver [BACS](https://github.com/dopt-TUDa/bacs),
- the MIP solver [SCIP](https://www.scipopt.org/), and
- the SAT symmetry breaking tool [BreakID](https://bitbucket.org/krr/breakid/).

## Why “satsuma”?

Because we thought it was fun. We did, however, prepare a haphazard explanation in case anyone asked: tools like *BreakID* and *Shatter* sound as if they violently destroy symmetries, 
while *satsuma* peels them apart more carefully, one piece at a time — like eating a satsuma.

## License
All of the code is licensed under the MIT license (see `LICENSE` for the main copyright notice).

(A) The files `robin_set.h`, `robin_map.h`, `robin_hash.h`, and `robin_growth_policy.h` are by Thibaut Goetghebuer-Planchon, see the respective files for more information.\
(B) The file `proof.h` is authored by Wietze Koops and Markus Anders.\
(C) All files not falling in either (A) or (B) are by Markus Anders.
