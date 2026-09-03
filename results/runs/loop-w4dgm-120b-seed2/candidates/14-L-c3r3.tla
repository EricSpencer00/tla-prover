---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N \in Nat /\ N >= 1
ASSUME MaxNat \in Nat /\ MaxNat >= 1

VARIABLES leader, ticket, requesting, slow, served

vars == <<leader, ticket, requesting, slow, served>>

Nodes == 1..N

Init ==
  /\ leader = 0
  /\ ticket = [p \in Nodes |-> 0]
  /\ requesting = [p \in Nodes |-> FALSE]
  /\ slow = [p \in Nodes |-> FALSE]
  /\ served = [p \in Nodes |-> FALSE]

RequestEnter(p) ==
  /\ ~requesting[p]
  /\ ~served[p]
  /\ requesting' = [requesting EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<leader, ticket, slow, served>>

GrantLeadership(p) ==
  /\ leader = 0
  /\ requesting[p]
  /\ ~slow[p]
  /\ leader' = p
  /\ ticket' = [ticket EXCEPT ![p] = IF @ < MaxNat THEN @ + 1 ELSE @]
  /\ requesting' = [requesting EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<slow, served>>

ReleaseLeadership(p) ==
  /\ leader = p
  /\ ~slow[p]
  /\ leader' = 0
  /\ served' = [served EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, requesting, slow>>

MarkSlow(p) ==
  /\ ~slow[p]
  /\ slow' = [slow EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<leader, ticket, requesting, served>>

Resume(p) ==
  /\ slow[p]
  /\ slow' = [slow EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<leader, ticket, requesting, served>>

Next ==
  \/ \E p \in Nodes : RequestEnter(p)
  \/ \E p \in Nodes : GrantLeadership(p)
  \/ \E p \in Nodes : ReleaseLeadership(p)
  \/ \E p \in Nodes : MarkSlow(p)
  \/ \E p \in Nodes : Resume(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in Nodes : (leader = p) => (~\E q \in Nodes : q # p /\ leader = q)
TypeOK ==
  /\ leader \in 0..N
  /\ ticket \in [Nodes -> 0..MaxNat]
  /\ requesting \in [Nodes -> BOOLEAN]
  /\ slow \in [Nodes -> BOOLEAN]
  /\ served \in [Nodes -> BOOLEAN]
Inv == MutualExclusion
TicketBound == \A p \in Nodes : ticket[p] <= MaxNat

Properties == Inv /\ TicketBound

NatOverride == Nat

====