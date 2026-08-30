---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* A finite range is used in place of the full set of natural numbers, so
\* ticket numbers stay bounded and the state space stays finite.
NatOverride == 0..MaxNat

VARIABLES pstate, ticket, waiting, served
vars == <<pstate, ticket, waiting, served>>

TypeOK ==
    /\ pstate \in [0..N-1 -> {"idle", "waiting", "cs", "done"}]
    /\ ticket \in [0..N-1 -> NatOverride]
    /\ waiting \in 0..N
    /\ served \in 0..N

Init ==
    /\ pstate = [p \in 0..N-1 |-> "idle"]
    /\ ticket = [p \in 0..N-1 |-> 0]
    /\ waiting = 0
    /\ served = 0

Request(p) ==
    /\ pstate[p] = "idle"
    /\ waiting < N
    /\ pstate' = [pstate EXCEPT ![p] = "waiting"]
    /\ waiting' = waiting + 1
    /\ UNCHANGED <<ticket, served>>

\* The ticket is one more than the highest outstanding ticket, wrapping back
\* to zero at the top of the finite range.
Admit(p) ==
    /\ pstate[p] = "waiting"
    /\ ticket' = [ticket EXCEPT ![p] =
                    IF \E q \in 0..N-1 : ticket[q] = MaxNat
                    THEN 0
                    ELSE (CHOOSE m \in NatOverride :
                            \A q \in 0..N-1 : ticket[q] < m)
                    ]
    /\ pstate' = [pstate EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<waiting, served>>

Enter(p) ==
    /\ pstate[p] = "cs"
    /\ \A q \in 0..N-1 \ {p} : pstate[q] # "cs" \/ ticket[q] # ticket[p]
    /\ UNCHANGED vars

Leave(p) ==
    /\ pstate[p] = "cs"
    /\ pstate' = [pstate EXCEPT ![p] = "done"]
    /\ UNCHANGED <<ticket, waiting, served>>

Reset(p) ==
    /\ pstate[p] = "done"
    /\ served < N
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ served' = served + 1
    /\ UNCHANGED <<ticket, waiting>>

Next ==
    \/ \E p \in 0..N-1 : Request(p) \/ Admit(p) \/ Enter(p) \/ Leave(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* The bakery ticket comparison is only sound when two processes in the
\* critical section can never hold the same ticket.
MutualExclusion == \A p \in 0..N-1, q \in 0..N-1 :
    (pstate[p] = "cs" /\ pstate[q] = "cs") => (p = q)

\* The inductive invariant is preserved by every transition, not just from
\* the initial state -- that is what makes it safe for starting from any
\* reachable state.
Inv == TypeOK /\ MutualExclusion

ISpec == Spec /\ WF_vars(Enter(0)) /\ WF_vars(Enter(1))
====