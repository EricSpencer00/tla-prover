---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets
CONSTANTS Value

ASSUME Value \in NONEMPTY

VARIABLES seq, scanned, candidate, observed, pos, pval

vars == <<seq, scanned, candidate, observed, pos, pval>>

Range(f, S) == { f[i] : i \in S }

TypeOK ==
    /\ seq \in [1..4 -> Value]
    /\ scanned \in 0..4
    /\ candidate \in Value
    /\ observed \in Nat
    /\ pos \subseteq (1..4)
    /\ pval \in [1..4 -> Value]

Init ==
    /\ seq = <<1, 2, 1, 1>>
    /\ scanned = 0
    /\ candidate = 1
    /\ observed = 0
    /\ pos = {}
    /\ pval = <<1, 2, 1, 1>>

Scan(n) ==
    /\ scanned < 4
    /\ n \in {1, 2}
    /\ seq' = [seq EXCEPT ![scanned + 1] = n]
    /\ scanned' = scanned + 1
    /\ UNCHANGED <<candidate, observed, pos, pval>>

Accept ==
    /\ scanned >= 1
    /\ seq[scanned] = candidate
    /\ scanned \notin pos
    /\ pos' = pos \cup {scanned}
    /\ pval' = [pval EXCEPT ![scanned] = candidate]
    /\ observed' = Cardinality(pos \cup {scanned})
    /\ UNCHANGED <<seq, scanned, candidate>>

Reject ==
    /\ scanned >= 1
    /\ seq[scanned] # candidate
    /\ scanned \notin pos
    /\ pos' = pos \cup {scanned}
    /\ pval' = [pval EXCEPT ![scanned] = seq[scanned]]
    /\ UNCHANGED <<seq, scanned, candidate, observed>>

PassCandidate(n) ==
    /\ n \in {1, 2}
    /\ candidate' = n
    /\ observed' = 0
    /\ pos' = {}
    /\ UNCHANGED <<seq, scanned, pval>>

Next ==
    \/ \E n \in {1, 2} : Scan(n)
    \/ Accept
    \/ Reject
    \/ \E n \in {1, 2} : PassCandidate(n)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ TypeOK
    /\ observed = Cardinality(pos)
    /\ pval \in [pos -> {candidate}]

Correct ==
    /\ scanned = 4
    /\ (2 * observed > 4) => (candidate \in Range(pval, pos))
====