# sequent
Proof checker for sequent [calculus proofs](https://en.wikipedia.org/wiki/Sequent_calculus)

The goal of this project is to be able to express theorems and proof them in the sequent calculus.

Technically, the project is a rewrite engine, taking as an input a theorem and appyling a sequence (or tree) or
rewrite commands, succeeding once every branch of the proof tree comes to a tautology (a |- a) and failing otherwise.

Some very simple proofs are already implemented and seems to check properly, they are all in the `test/` folder and running the test will check the proofs.
