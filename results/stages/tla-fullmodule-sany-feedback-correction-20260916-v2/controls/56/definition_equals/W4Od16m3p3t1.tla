-------------------------- MODULE W4Od16m3p3t1 --------------------------
EXTENDS Naturals
CONSTANTS Nodes, Slots, Scripts, MaxTerm
ASSUME MaxTerm \in Nat

VARIABLES term, leader, owner, requests, log
vars = <<term, leader, owner, requests, log>>

None == "none"
Bump(t) == IF t < MaxTerm THEN t + 1 ELSE t

Reqs == [script : Scripts, slot : Slots]
Entries == [slot : Slots, script : Scripts, term : 0..MaxTerm]

TypeOK ==
  /\ term \in 0..MaxTerm
  /\ leader \in (Nodes \cup {None})
  /\ owner \in [Slots -> (Scripts \cup {None})]
  /\ requests \in SUBSET Reqs
  /\ log \in SUBSET Entries

Allocated(sc) == \E s \in Slots : owner[s] = sc

Init ==
  /\ term = 0
  /\ leader = None
  /\ owner = [s \in Slots |-> None]
  /\ requests = {}
  /\ log = {}

ElectLeader(n) ==
  /\ leader = None
  /\ leader' = n
  /\ term' = Bump(term)
  /\ UNCHANGED <<owner, requests, log>>

FailLeader(n) ==
  /\ leader = n
  /\ leader' = None
  /\ UNCHANGED <<term, owner, requests, log>>

SubmitRequest(sc, s) ==
  /\ ~Allocated(sc)
  /\ [script |-> sc, slot |-> s] \notin requests
  /\ requests' = requests \cup {[script |-> sc, slot |-> s]}
  /\ UNCHANGED <<term, leader, owner, log>>

\* Leader allocates a free slot; reordered requests handled in any order.
Allocate(r) ==
  /\ leader # None
  /\ r \in requests
  /\ owner[r.slot] = None
  /\ ~Allocated(r.script)
  /\ owner' = [owner EXCEPT ![r.slot] = r.script]
  /\ log' = log \cup {[slot |-> r.slot, script |-> r.script, term |-> term]}
  /\ requests' = requests \ {r}
  /\ UNCHANGED <<term, leader>>

RejectRequest(r) ==
  /\ r \in requests
  /\ owner[r.slot] # None
  /\ requests' = requests \ {r}
  /\ UNCHANGED <<term, leader, owner, log>>

Next ==
  \/ \E n \in Nodes : ElectLeader(n) \/ FailLeader(n)
  \/ \E sc \in Scripts, s \in Slots : SubmitRequest(sc, s)
  \/ \E r \in requests : Allocate(r) \/ RejectRequest(r)

Spec == Init /\ [][Next]_vars

\* The allocation log is functional on slots: one slot never maps to two scripts.
NoDoubleAllocation ==
  \A e1, e2 \in log : (e1.slot = e2.slot) => (e1.script = e2.script)
=============================================================================