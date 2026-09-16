------------------------- MODULE W4Od13m2p5t5 -------------------------
EXTENDS Naturals

CONSTANTS Txns, Suppliers

VARIABLES prepared, committed, aborted, votes, audit
vars == <<prepared, committed, aborted, votes, audit>>

TypeOK ==
    /\ prepared \subseteq Txns
    /\ committed \subseteq Txns
    /\ aborted \subseteq Txns
    /\ votes \in [Txns -> SUBSET Suppliers]
    /\ audit \subseteq Txns

Init ==
    /\ prepared = {}
    /\ committed = {}
    /\ aborted = {}
    /\ votes = [t \in Txns |-> {}]
    /\ audit = {}

Prepare(t) ==
    /\ t \notin prepared
    /\ t \notin committed
    /\ t \notin aborted
    /\ prepared' = prepared \cup {t}
    /\ UNCHANGED <<committed, aborted, votes, audit>>

CastVote(s, t) ==
    /\ t \in prepared
    /\ s \notin votes[t]
    /\ votes' = [votes EXCEPT ![t] = votes[t] \cup {s}]
    /\ UNCHANGED <<prepared, committed, aborted, audit>>

Commit(t) ==
    /\ t \in prepared
    /\ votes[t] = Suppliers
    /\ t \notin aborted
    /\ committed' = committed \cup {t}
    /\ prepared' = prepared \ {t}
    /\ UNCHANGED <<aborted, votes, audit>>

AdminCommit(t) ==
    /\ t \in prepared
    /\ t \notin aborted
    /\ committed' = committed \cup {t}
    /\ prepared' = prepared \ {t}
    /\ UNCHANGED <<aborted, votes, audit>>

Abort(t) ==
    /\ t \in prepared
    /\ t \notin committed
    /\ aborted' = aborted \cup {t}
    /\ prepared' = prepared \ {t}
    /\ UNCHANGED <<committed, votes, audit>>

RaiseAudit(t) ==
    /\ t \notin audit
    /\ audit' = audit \cup {t}
    /\ UNCHANGED <<prepared, committed, aborted, votes>>

LowerAudit(t) ==
    /\ t \in audit
    /\ audit' = audit \ {t}
    /\ UNCHANGED <<prepared, committed, aborted, votes>>

Next ==
    \/ \E t \in Txns : Prepare(t)
    \/ \E s \in Suppliers, t \in Txns : CastVote(s, t)
    \/ \E t \in Txns : Commit(t)
    \/ \E t \in Txns : AdminCommit(t)
    \/ \E t \in Txns : Abort(t)
    \/ \E t \in Txns : RaiseAudit(t)
    \/ \E t \in Txns : LowerAudit(t)

Spec == Init /\ [][Next]_vars

Disjoint == committed \cap aborted = {}
=============================================================================