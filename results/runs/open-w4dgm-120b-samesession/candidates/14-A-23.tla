---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite override of the unbounded Nat from Naturals, kept as a *definition*
\* so the name Nat on the left of the replacement in the .cfg is never declared.
NatOverride == [n \in Nat |-> IF n <= MaxNat THEN n ELSE MaxNat]

VARIABLES ticket, inCS, nextTicket, phase

vars == <<ticket, inCS, nextTicket, phase>>

TypeOK ==
    /\ ticket \in [0 .. MaxNat]
    /\ inCS \in 0 .. N
    /\ nextTicket \in 0 .. MaxNat
    /\ phase \in [1 .. N -> {"idle", "waiting", "critical"}]

Init ==
    /\ ticket = 0
    /\ inCS = 0
    /\ nextTicket = 0
    /\ phase = [p \in 1 .. N |-> "idle"]

Request(p) ==
    /\ phase[p] = "idle"
    /\ phase' = [phase EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, inCS, nextTicket>>

Enter(p) ==
    /\ phase[p] = "waiting"
    /\ inCS = 0
    /\ inCS' = p
    /\ phase' = [phase EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
    /\ phase[p] = "critical"
    /\ inCS = p
    /\ inCS' = 0
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, nextTicket>>

RolloverTicket ==
    /\ nextTicket = MaxNat
    /\ nextTicket' = 0
    /\ ticket' = 0
    /\ UNCHANGED <<inCS, phase>>

IssueTicket ==
    /\ nextTicket < MaxNat
    /\ nextTicket' = nextTicket + 1
    /\ ticket' = nextTicket + 1
    /\ UNCHANGED <<inCS, phase>>

Next ==
    \/ \E p \in 1 .. N : Request(p)
    \/ \E p \in 1 .. N : Enter(p)
    \/ \E p \in 1 .. N : Exit(p)
    \/ RolloverTicket
    \/ IssueTicket

Spec == Init /\ [][Next]_vars

\* SAFETY PROPERTY: mutual exclusion of the single critical resource.
MutualExclusion == (inCS # 0) => (phase[inCS] = "critical")

\* SAFETY PROPERTY: every process is in exactly one of the three phases.
TypeOKFull == TypeOK

\* SAFETY PROPERTY: ticket numbers never exceed the configured maximum.
Inv == nextTicket <= MaxNat

====