-------------------------- MODULE W4Od7m5p1t3 --------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Cranes, Quorum, MaxLen

VARIABLES
    log,        \* committed revisions, a sequence of [pr, base] records
    active,     \* is there an open proposal?
    proposer,   \* crane owning the open proposal
    base,       \* revision number the open proposal snapshotted
    votes       \* set of cranes that have voted for the open proposal

vars == << log, active, proposer, base, votes >>

Entry == [pr : Cranes, base : 0..MaxLen]

TypeOK ==
    /\ log \in Seq(Entry)
    /\ active \in BOOLEAN
    /\ proposer \in Cranes
    /\ base \in 0..MaxLen
    /\ votes \subseteq Cranes

Init ==
    /\ log = << >>
    /\ active = FALSE
    /\ proposer = CHOOSE c \in Cranes : TRUE
    /\ base = 0
    /\ votes = {}

\* A crane opens a proposal, snapshotting the current revision number.
Propose(c) ==
    /\ ~active
    /\ active' = TRUE
    /\ proposer' = c
    /\ base' = Len(log)
    /\ votes' = {c}
    /\ UNCHANGED log

\* Any crane casts its single vote for the open proposal.
Vote(c) ==
    /\ active
    /\ c \notin votes
    /\ votes' = votes \cup {c}
    /\ UNCHANGED << log, active, proposer, base >>

\* Once a quorum is reached, the revision is appended to the plan's log.
Commit ==
    /\ active
    /\ Len(log) < MaxLen
    /\ Cardinality(votes) >= Quorum
    /\ base = Len(log)
    /\ log' = Append(log, [pr |-> proposer, base |-> base])
    /\ active' = FALSE
    /\ UNCHANGED << proposer, base, votes >>

\* A proposal that cannot make progress is aborted.
Abort ==
    /\ active
    /\ active' = FALSE
    /\ UNCHANGED << log, proposer, base, votes >>

Next ==
    \/ \E c \in Cranes : Propose(c)
    \/ \E c \in Cranes : Vote(c)
    \/ Commit
    \/ Abort

Spec == Init /\ [][Next]_vars

\* No lost updates: each committed revision was built directly on top of its
\* predecessor, so the log is an unbroken chain with no discarded revision.
ChainIntact == \A i \in 1..Len(log) : log[i].base = i - 1

=============================================================================
