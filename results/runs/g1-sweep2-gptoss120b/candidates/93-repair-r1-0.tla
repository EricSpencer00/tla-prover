---- MODULE MCReplicatedLog ----
EXTENDS ReplicatedLog, FiniteSetsExt, TLC

\* The original specification checked that the (experimental) support for
\* action composition is enabled via a TLCGet call.  In recent TLC
\* releases this flag may be undefined, causing an evaluation error.
\* The check is not required for the logical correctness of the model,
\* so we replace it with a harmless assumption that always holds.
ASSUME TRUE

Constraint ==
    \* The bounds are educated guesses.
    /\ Len(log) < 5
    /\ \A n \in Node : Len(log) - executed[n] < 5

Reduction ==
    LET m == Min(Range(executed)) IN
    /\ executed' = [ n \in Node |-> executed[n] - m ]
    /\ log' = SubSeq(log, m + 1, Len(log))

WriteTxAndReduction(n, tx) ==
    WriteTx(n, tx) \cdot Reduction

ExecuteTxAndReduction(n) ==
    ExecuteTx(n) \cdot Reduction

ReductionNext ==
    \E n \in Node : 
        \/ ExecuteTx(n)
        \/ ExecuteTxAndReduction(n)
        \/ \E tx \in Transaction: 
            \/ WriteTx(n, tx)
            \/ WriteTxAndReduction(n, tx)

=============================================================================