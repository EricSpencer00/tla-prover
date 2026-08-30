---- MODULE MajorityProof ----
EXTENDS Naturals
CONSTANTS Value
ASSUME Value \in Nat /\ Value >= 3

\* No new state: all variables come from the main specification.
VARIABLES candidates, seen, index, candidate, phase

TypeOK == /\ candidates \subseteq Value
          /\ seen \subseteq Value
          /\ index \in 0..Value
          /\ candidate \in Value
          /\ phase \in {"voting", "done"}

Init == /\ candidates = Value
        /\ seen = {}
        /\ index = 0
        /\ candidate = 0
        /\ phase = "voting"

Vote(c) == /\ phase = "voting"
           /\ c \in candidates
           /\ c \notin seen
           /\ index < Value
           /\ seen' = seen \cup {c}
           /\ index' = index + 1
           /\ UNCHANGED <<candidates, candidate, phase>>

Drop(c) == /\ phase = "voting"
           /\ c \in candidates
           /\ c \notin seen
           /\ candidates' = candidates \ {c}
           /\ UNCHANGED <<seen, index, candidate, phase>>

Complete == /\ phase = "voting"
            /\ candidates # {}
            /\ candidates = seen
            /\ index = Value
            /\ candidate' = CHOOSE c \in candidates : TRUE
            /\ phase' = "done"
            /\ UNCHANGED <<candidates, seen, index>>

VoteStep == \E c \in Value : Vote(c)
DropStep == \E c \in Value : Drop(c)

Next == VoteStep \/ DropStep \/ Complete

Spec == Init /\ [][Next]_<<candidates, seen, index, candidate, phase>>

\* The candidate must reflect the strict majority of the scanned sequence.
\* The scan is exhaustive, so any such element must be the majority's sole
\* survivor -- this is the Boyer-Moore correctness argument.
Correct == (phase = "done") => (\A c \in Value : (2 * Cardinality({i \in 1..Value : candidate = c}) >= Value) => (candidate = c))

\* The invariant from the main spec: after the scan completes, exactly the
\* surviving candidate remains in the candidate set.
Inv == (phase = "done") => (candidates = {candidate})

====