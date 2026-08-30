---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES phase, cs, ticket, nextTicket

vars == <<phase, cs, ticket, nextTicket>>

TypeOK ==
  /\ phase \in {"idle", "waiting", "critical"}
  /\ cs \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ phase = "idle"
  /\ cs = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

RequestTicket(p) ==
  /\ phase = "idle"
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ phase' = "waiting"
  /\ cs' = {}

EnterCritical(p) ==
  /\ phase = "waiting"
  /\ \A q \in 1..N : ticket[q] = 0 \/ ticket[q] > ticket[p]
  /\ cs' = {p}
  /\ phase' = "critical"
  /\ UNCHANGED <<ticket, nextTicket>>

LeaveCritical(p) ==
  /\ phase = "critical"
  /\ p \in cs
  /\ cs' = {}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ phase' = "idle"
  /\ UNCHANGED nextTicket

Next ==
  \/ \E p \in 1..N : RequestTicket(p)
  \/ \E p \in 1..N : EnterCritical(p)
  \/ \E p \in 1..N : LeaveCritical(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in cs : Cardinality(cs) = 1

Inv ==
  /\ MutualExclusion
  /\ TypeOK

StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

====