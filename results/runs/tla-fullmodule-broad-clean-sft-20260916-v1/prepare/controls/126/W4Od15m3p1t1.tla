-------------------------- MODULE W4Od15m3p1t1 --------------------------
EXTENDS Naturals, FiniteSets

(* A stock exchange opening auction with a single shared record (the       *)
(* auction book) maintained by an elected leader.  Leaders can fail and a   *)
(* new leader is elected on a fresh term (failover).  Client update         *)
(* messages may be committed in any order (reordering).  An update that has *)
(* been acknowledged to the client must never be lost from the shared       *)
(* record.                                                                   *)

Nodes   == {1, 2, 3}
Updates == {1, 2, 3}
MaxTerm == 3

VARIABLES leader, term, ledger, pending, acked

vars == << leader, term, ledger, pending, acked >>

TypeOK ==
    /\ leader  \in Nodes \cup {0}
    /\ term    \in 0..MaxTerm
    /\ ledger  \subseteq Updates
    /\ pending \subseteq Updates
    /\ acked   \subseteq Updates

Init ==
    /\ leader  = 0
    /\ term    = 0
    /\ ledger  = {}
    /\ pending = {}
    /\ acked   = {}

\* Failover: with no active leader, some node takes leadership, advancing
\* the term until the bound is reached.
Elect(n) ==
    /\ leader = 0
    /\ leader' = n
    /\ term'   = IF term < MaxTerm THEN term + 1 ELSE term
    /\ UNCHANGED << ledger, pending, acked >>

\* The current leader crashes.
Crash ==
    /\ leader # 0
    /\ leader' = 0
    /\ UNCHANGED << term, ledger, pending, acked >>

\* A client submits an update; it joins the reorderable pending set.
Submit(u) ==
    /\ u \notin pending
    /\ u \notin ledger
    /\ pending' = pending \cup {u}
    /\ UNCHANGED << leader, term, ledger, acked >>

\* The leader durably commits any pending update (reordered commit).
Commit(u) ==
    /\ leader # 0
    /\ u \in pending
    /\ ledger'  = ledger \cup {u}
    /\ pending' = pending \ {u}
    /\ UNCHANGED << leader, term, acked >>

\* An update is acknowledged to the client only after it is durable.
Ack(u) ==
    /\ u \in ledger
    /\ u \notin acked
    /\ acked' = acked \cup {u}
    /\ UNCHANGED << leader, term, ledger, pending >>

Next ==
    \/ \E n \in Nodes   : Elect(n)
    \/ Crash
    \/ \E u \in Updates : Submit(u)
    \/ \E u \in Updates : Commit(u)
    \/ \E u \in Updates : Ack(u)

Spec == Init /\ [][Next]_vars

\* No lost updates: every update acknowledged to a client is present in the
\* durable shared record.
NoLostUpdates == acked \subseteq ledger

=============================================================================