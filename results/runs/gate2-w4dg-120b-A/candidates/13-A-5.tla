---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES phase, ticket, cur

vars == <<phase, ticket, cur>>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "waiting", "cs"}]
  /\ ticket \in [1..N -> Nat]
  /\ cur \in Nat

MutualExclusion ==
  \A i \in 1..N : phase[i] = "cs" => (\A j \in 1..N : j # i => phase[j] # "cs")

BoundedTicket ==
  \A i \in 1..N : ticket[i] <= MaxNat

Inv == TypeOK /\ MutualExclusion /\ BoundedTicket

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ cur = 0

Request(i) ==
  /\ phase[i] = "idle"
  /\ phase' = [phase EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = IF cur < MaxNat THEN cur + 1 ELSE MaxNat]
  /\ UNCHANGED cur

Enter(i) ==
  /\ phase[i] = "waiting"
  /\ \A j \in 1..N : phase[j] # "cs"
  /\ phase' = [phase EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, cur>>

Exit(i) ==
  /\ phase[i] = "cs"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ cur' = IF ticket[i] > cur THEN ticket[i] ELSE cur
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

ISpec == Init /\ [][Next]_vars
====