---- MODULE MCMajority ----
EXTENDS Integers

\* The set of possible vote values
Value == {"A", "B", "C"}

\* The maximum length of the sequence (must be a natural number)
CONSTANT bound

\* The set of all sequences over Value whose length is between 0 and bound
Seqs == { s \in [1..n -> Value] : n \in 0..bound }

\* No additional variables or operators are needed for this simple model
====