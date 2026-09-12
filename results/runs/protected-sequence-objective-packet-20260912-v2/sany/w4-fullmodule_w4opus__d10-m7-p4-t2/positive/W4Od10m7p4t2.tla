---- MODULE W4Od10m7p4t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Controllers, Blocks, PoolCap, NoBlock, NoRead

ASSUME NoBlock \notin Blocks

VARIABLES reg, snap, claim, powered, refused

Vars == <<reg, snap, claim, powered, refused>>

\* The substation pool can energise at most PoolCap track blocks at once.
\* The two line controllers share nothing but the register `reg`.
Energised == UNION {powered[c] : c \in Controllers}

TypeOK ==
    /\ reg \in 0..Cardinality(Blocks)
    /\ snap \in [Controllers -> {NoRead} \union (0..Cardinality(Blocks))]
    /\ claim \in [Controllers -> {NoBlock} \union Blocks]
    /\ powered \in [Controllers -> SUBSET Blocks]
    /\ refused \subseteq Controllers

Init ==
    /\ reg = 0
    /\ snap = [c \in Controllers |-> NoRead]
    /\ claim = [c \in Controllers |-> NoBlock]
    /\ powered = [c \in Controllers |-> {}]
    /\ refused = {}

\* A controller latches the register value it saw together with the block
\* it wants; that pair is its compare-and-swap expectation.
Latch(c, b) ==
    /\ snap[c] = NoRead
    /\ b \notin Energised
    /\ snap' = [snap EXCEPT ![c] = reg]
    /\ claim' = [claim EXCEPT ![c] = b]
    /\ UNCHANGED <<reg, powered, refused>>

\* Headroom is judged from the latched snapshot, so the swap must also
\* confirm that nothing moved the register since the read.
Swap(c) ==
    /\ snap[c] # NoRead
    /\ snap[c] < PoolCap
    /\ snap[c] = reg
    /\ claim[c] \notin Energised
    /\ reg' = reg + 1
    /\ powered' = [powered EXCEPT ![c] = @ \union {claim[c]}]
    /\ snap' = [snap EXCEPT ![c] = NoRead]
    /\ claim' = [claim EXCEPT ![c] = NoBlock]
    /\ UNCHANGED refused

\* Stale expectation: some other controller advanced the register first.
SwapFails(c) ==
    /\ snap[c] # NoRead
    /\ snap[c] # reg
    /\ snap' = [snap EXCEPT ![c] = NoRead]
    /\ claim' = [claim EXCEPT ![c] = NoBlock]
    /\ UNCHANGED <<reg, powered, refused>>

Refuse(c) ==
    /\ snap[c] # NoRead
    /\ snap[c] >= PoolCap
    /\ snap[c] = reg
    /\ snap' = [snap EXCEPT ![c] = NoRead]
    /\ claim' = [claim EXCEPT ![c] = NoBlock]
    /\ refused' = refused \union {c}
    /\ UNCHANGED <<reg, powered>>

Deenergise(c, b) ==
    /\ b \in powered[c]
    /\ powered' = [powered EXCEPT ![c] = @ \ {b}]
    /\ reg' = reg - 1
    /\ refused' = refused \ {c}
    /\ UNCHANGED <<snap, claim>>

Next ==
    \/ \E c \in Controllers, b \in Blocks : Latch(c, b)
    \/ \E c \in Controllers : Swap(c)
    \/ \E c \in Controllers : SwapFails(c)
    \/ \E c \in Controllers : Refuse(c)
    \/ \E c \in Controllers, b \in Blocks : Deenergise(c, b)

Spec == Init /\ [][Next]_Vars

\* Bounded capacity: the pool is never over-drawn, however the two
\* independent controllers interleave their latch/swap attempts.
PoolNeverOverdrawn == Cardinality(Energised) <= PoolCap
====