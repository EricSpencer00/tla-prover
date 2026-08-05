---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES status, choosing, ticket

vars == <<status, choosing, ticket>>

RECURSIVE LessThan(_)
LessThan(S) ==
  LET f[T \in SUBSET [1..N -> 0..MaxNat]] ==
        IF T = {} THEN TRUE
        ELSE LET x == CHOOSE y \in T : TRUE IN \A z \in T : f[T \ {z}] /\ x > z
  IN f[S]

NatOverride == Nat

Init ==
  /\ status = [p \in 1..N |-> "idle"]
  /\ choosing = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
  /\ status[p] = "idle"
  /\ status' = [status EXCEPT ![p] = "waiting"]
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ UNCHANGED ticket

TakeTicket(p) ==
  /\ choosing[p]
  /\ ticket[p] = 0
  /\ ticket' = [ticket EXCEPT ![p] = 1 + CHOOSE q \in 1..N: IF ticket[q] > 0 THEN ticket[q] ELSE 0]
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ UNCHANGED status

Enter(p) ==
  /\ status[p] = "waiting"
  /\ \A q \in 1..N : (status[q] # "critical") \/ (ticket[p] < ticket[q])
  /\ status' = [status EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<choosing, ticket>>

Exit(p) ==
  /\ status[p] = "critical"
  /\ status' = [status EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED choosing

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : TakeTicket(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : status[p] = "critical" => (\A q \in 1..N : status[q] = "critical" => q = p)

TypeOK ==
  /\ status \in [1..N -> {"idle", "waiting", "critical"}]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

Inv == MutualExclusion /\ TypeOK

====