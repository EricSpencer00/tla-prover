---- MODULE W4Od9m0p2t0 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Controllers, Blocks, Feeders, MaxVersion, Unallocated, NoStage

\* A staging records the table version it was read against; it deliberately does
\* not move the block, which is why a controller dying mid-decision is harmless.
Stagings == [block : Blocks, feeder : Feeders, base : 0..MaxVersion]

VARIABLES committed, allocation, escrow, version, staged, dead

vars == <<committed, allocation, escrow, version, staged, dead>>

TypeOK ==
    /\ committed \in SUBSET Blocks
    /\ allocation \in [Blocks -> {Unallocated} \cup Feeders]
    /\ escrow \in SUBSET Blocks
    /\ version \in 0..MaxVersion
    /\ staged \in [Controllers -> {NoStage} \cup Stagings]
    /\ dead \in SUBSET Controllers

Init ==
    /\ committed = {}
    /\ allocation = [b \in Blocks |-> Unallocated]
    /\ escrow = {}
    /\ version = 0
    /\ staged = [c \in Controllers |-> NoStage]
    /\ dead = {}

CommitBlock(b) ==
    /\ b \notin committed
    /\ committed' = committed \cup {b}
    /\ escrow' = escrow \cup {b}
    /\ UNCHANGED <<allocation, version, staged, dead>>

Stage(c, b, f) ==
    /\ c \notin dead
    /\ staged[c] = NoStage
    /\ b \in escrow
    /\ staged' = [staged EXCEPT ![c] = [block |-> b, feeder |-> f, base |-> version]]
    /\ UNCHANGED <<committed, allocation, escrow, version, dead>>

Usable(c) ==
    /\ c \notin dead
    /\ staged[c].base = version
    /\ staged[c].block \in escrow
    /\ version < MaxVersion

\* The block leaves escrow and lands on the feeder in the same step, so the
\* accounting never has it in both places or in neither.
Apply(c) ==
    /\ staged[c] # NoStage
    /\ Usable(c)
    /\ allocation' = [allocation EXCEPT ![staged[c].block] = staged[c].feeder]
    /\ escrow' = escrow \ {staged[c].block}
    /\ version' = version + 1
    /\ staged' = [staged EXCEPT ![c] = NoStage]
    /\ UNCHANGED <<committed, dead>>

StartOver(c) ==
    /\ staged[c] # NoStage
    /\ ~Usable(c)
    /\ staged' = [staged EXCEPT ![c] = NoStage]
    /\ UNCHANGED <<committed, allocation, escrow, version, dead>>

Fail(c) ==
    /\ c \notin dead
    /\ Cardinality(dead) < Cardinality(Controllers)
    /\ dead' = dead \cup {c}
    /\ UNCHANGED <<committed, allocation, escrow, version, staged>>

Revive(c) ==
    /\ c \in dead
    /\ dead' = dead \ {c}
    /\ UNCHANGED <<committed, allocation, escrow, version, staged>>

Release(b) ==
    /\ allocation[b] # Unallocated
    /\ allocation' = [allocation EXCEPT ![b] = Unallocated]
    /\ escrow' = escrow \cup {b}
    /\ UNCHANGED <<committed, version, staged, dead>>

Decommit(b) ==
    /\ b \in escrow
    /\ committed' = committed \ {b}
    /\ escrow' = escrow \ {b}
    /\ UNCHANGED <<allocation, version, staged, dead>>

Reindex ==
    /\ version = MaxVersion
    /\ version' = 0
    /\ staged' = [c \in Controllers |-> NoStage]
    /\ UNCHANGED <<committed, allocation, escrow, dead>>

Settle(c) == Apply(c) \/ StartOver(c)

Next ==
    \/ \E b \in Blocks : CommitBlock(b) \/ Release(b) \/ Decommit(b)
    \/ \E c \in Controllers, b \in Blocks, f \in Feeders : Stage(c, b, f)
    \/ \E c \in Controllers : Settle(c) \/ Fail(c) \/ Revive(c)
    \/ Reindex

Spec == Init /\ [][Next]_vars
        /\ \A c \in Controllers : WF_vars(Settle(c))

BlocksAccountedFor ==
    committed = escrow \cup {b \in Blocks : allocation[b] # Unallocated}

EveryStagingClears ==
    \A c \in Controllers : (staged[c] # NoStage) ~> (staged[c] = NoStage)

====