---------------------------- MODULE W4Od12m0p1t3 ----------------------------
(* Blood-bank inventory tracker: a shared versioned record updated under
   optimistic concurrency control (read-version, prepare, compare-and-commit,
   retry-on-stale). Slow-but-not-failed terminals. *)
EXTENDS Naturals, FiniteSets

Procs   == {"p1", "p2"}
Updates == {"u1", "u2"}
NoUpd   == "none"

VARIABLES applied, version, rv, pend, ack

TypeOK ==
    /\ applied \subseteq Updates
    /\ version \in 0..Cardinality(Updates)
    /\ rv \in [Procs -> 0..Cardinality(Updates)]
    /\ pend \in [Procs -> Updates \cup {NoUpd}]
    /\ ack \in [Procs -> SUBSET Updates]

Init ==
    /\ applied = {}
    /\ version = 0
    /\ rv = [p \in Procs |-> 0]
    /\ pend = [p \in Procs |-> NoUpd]
    /\ ack = [p \in Procs |-> {}]

Prepare(p, u) ==
    /\ pend[p] = NoUpd
    /\ pend' = [pend EXCEPT ![p] = u]
    /\ UNCHANGED <<applied, version, rv, ack>>

Read(p) ==
    /\ rv' = [rv EXCEPT ![p] = version]
    /\ UNCHANGED <<applied, version, pend, ack>>

Commit(p) ==
    /\ pend[p] # NoUpd
    /\ pend[p] \notin applied
    /\ rv[p] = version
    /\ applied' = applied \cup {pend[p]}
    /\ version' = version + 1
    /\ ack' = [ack EXCEPT ![p] = ack[p] \cup {pend[p]}]
    /\ pend' = [pend EXCEPT ![p] = NoUpd]
    /\ UNCHANGED rv

Retry(p) ==
    /\ pend[p] # NoUpd
    /\ rv[p] # version
    /\ rv' = [rv EXCEPT ![p] = version]
    /\ UNCHANGED <<applied, version, pend, ack>>

Next ==
    \/ \E p \in Procs, u \in Updates : Prepare(p, u)
    \/ \E p \in Procs : Read(p)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : Retry(p)

NoLostUpdate == \A p \in Procs : ack[p] \subseteq applied

vars == <<applied, version, rv, pend, ack>>
Spec == Init /\ [][Next]_vars
=============================================================================