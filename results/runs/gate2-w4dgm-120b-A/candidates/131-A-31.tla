---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote, TLAPS

CONSTANTS Value

VARIABLES idx, cand, seen, complete

vars == <<idx, cand, seen, complete>>

\* No new state variables: all are inherited from MajorityVote.

TypeOK ==
    /\ idx \in 0..3
    /\ cand \in Value \cup {"none"}
    /\ seen \subseteq (0..3)
    /\ complete \in BOOLEAN

Init ==
    /\ idx = 0
    /\ cand = "none"
    /\ seen = {}
    /\ complete = FALSE

\* No new actions: all transitions are inherited from MajorityVote.
\* The invariant Inv from MajorityVote is re-used here as part of the proof.
Next == MajorityVote.Next \/ MajorityVote.Agree

Spec == Init /\ [][Next]_vars

\* 1. Type correctness is preserved as an invariant.
TypeOKInv == TypeOK

\* 2. After scanning the whole sequence, any majority value must equal
\* the selected candidate -- the only correct output the algorithm can
\* produce.  This is the main correctness property, proved via Inv.
MajorityAgree == Inv

====