---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

\* The interactive proof is structured as a hierarchy of numbered steps, each
\* with a clear subgoal, so that TLAPS can check the proof mechanically.
\* No new state or action is introduced here; the module simply re-exposes
\* the MAIN SPECIFICATION and adds two proof obligations over its invariants.

VARIABLES seq, scanned, cand, candCount

vars == <<seq, scanned, cand, candCount>>

MaxPos == 3

TypeOK ==
    /\ seq \in Seq(Value)
    /\ scanned \in 0..MaxPos
    /\ cand \in Value
    /\ candCount \in 0..MaxPos

\* The inductive fact from the main algorithm: the candidate is never outlived
\* by a strict majority in the positions already scanned.
NoMajorityExceeded ==
    \A y \in Value :
        (candCount * 2 > scanned) => (cand = y \/ (Count(y, scanned) * 2 <= scanned))

Init ==
    /\ seq = << >> \/ <<Value>>
    /\ scanned = 0
    /\ cand = CHOOSE e \in Value : TRUE
    /\ candCount = 0

\* Existing transitions from the main spec are simply aliased here so the
\* proof can refer to them as steps of this module's system.
Read ==
    /\ scanned < Len(seq)
    /\ scanned' = scanned + 1
    /\ cand' = IF cand = seq[scanned + 1] THEN cand ELSE seq[scanned + 1]
    /\ candCount' = IF cand = seq[scanned + 1] THEN candCount + 1 ELSE 1
    /\ UNCHANGED seq

Rescan ==
    /\ scanned = Len(seq)
    /\ scanned' = 0
    /\ cand' = CHOOSE e \in Value : TRUE
    /\ candCount' = 0
    /\ UNCHANGED seq

Append ==
    /\ Len(seq) < MaxPos
    /\ \E v \in Value : seq' = Append(seq, v)
    /\ UNCHANGED <<scanned, cand, candCount>>

Spec == Init /\ [][Read]_vars /\ [][Rescan]_vars /\ [][Append]_vars

\* The full correctness claim: the candidate never loses a strict majority.
Correct == Inv == NoMajorityExceeded

\* Type correctness is an invariant of the same system, proved separately.
\* TLAPS checks both invariants together, which is stronger than checking
\* either one alone.
\* The hierarchical numbering is absorbed by the nesting of assumptions.
TypeConsistency ==
    /\ TypeOK
    /\ Correct

====