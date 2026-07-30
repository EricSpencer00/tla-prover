---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

ASSUME N \in Nat \ {0}
ASSUME MaxNat \in Nat

VARIABLES pc, ticket, nextTicket
vars == <<pc, ticket, nextTicket>>

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

MutualExclusion ==
  \A p \in 1..N : \A q \in 1..N : (p # q /\ pc[p] = "cs") => pc[q] # "cs"

Inv ==
  /\ MutualExclusion
  /\ TypeOK

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

Enter(p) ==
  /\ pc[p] = "trying"
  /\ \A q \in 1..N : pc[q] # "cs" => (ticket[q] = 0 \/ ticket[q] > ticket[p])
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED nextTicket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

ISpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Request(p))
  /\ WF_vars(\E p \in 1..N : Enter(p))
  /\ WF_vars(\E p \in 1..N : Exit(p))

====