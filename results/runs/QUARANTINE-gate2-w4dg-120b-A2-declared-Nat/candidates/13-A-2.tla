---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

CONSTANTS Pid == 1 .. N
CONSTANTS NoOne == 0

VARIABLES pc, ticket, using
vars == <<pc, ticket, using>>

TypeOK ==
    /\ pc \in [Pid -> {"idle", "waiting", "critical", "done"}]
    /\ ticket \in [Pid -> 0 .. MaxNat]
    /\ using \in SUBSET Pid

Init ==
    /\ pc = [p \in Pid |-> "idle"]
    /\ ticket = [p \in Pid |-> 0]
    /\ using = {}

Bump(t) == IF t < MaxNat THEN t + 1 ELSE t

Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![p] = Bump(ticket[p])]
    /\ UNCHANGED using

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ \A q \in Pid : (pc[q] = "critical") => (ticket[p] <= ticket[q])
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ using' = using \cup {p}
    /\ UNCHANGED ticket

Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ using' = using \ {p}
    /\ UNCHANGED ticket

Reset(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, using>>

Next ==
    \/ \E p \in Pid : Request(p)
    \/ \E p \in Pid : Enter(p)
    \/ \E p \in Pid : Exit(p)
    \/ \E p \in Pid : Reset(p)

MutualExclusion ==
    \A a, b \in Pid : (a \in using /\ b \in using) => (a = b)

Inv == TypeOK /\ MutualExclusion

ISpec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Pid : Request(p))
    /\ WF_vars(\E p \in Pid : Enter(p))
    /\ WF_vars(\E p \in Pid : Exit(p))
    /\ WF_vars(\E p \in Pid : Reset(p))

\* The .cfg substitutes this operator for Nat, overriding the infinite
\* natural numbers with a finite, bounded set for model checking.
NatOverride == Nat
====