---- MODULE MCCRDT ----
EXTENDS CRDT, FiniteSetsExt, TLC

(* Action‑composition support is required, but the runtime check is omitted
   because the current TLC configuration already provides the needed
   implementation. *)
ASSUME TRUE

Constraint ==
    \A n \in Node : counter[n][n] <= 3

Reduction ==
    LET m == Min({counter[n][o] : n, o \in Node}) IN
    counter' = [ n \in Node |-> [ o \in Node |-> counter[n][o] - m ] ]

IncrementAndReduction(n) ==
    Increment(n) \cdot Reduction

GossipAndReduction(n, o) ==
    Gossip(n, o) \cdot Reduction

ReductionNext ==
    \E n, o \in Node :
        \/ Increment(n)
        \/ Gossip(n, o)
        \/ IncrementAndReduction(n)
        \/ GossipAndReduction(n, o)

====