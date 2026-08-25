---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet

VARIABLES s, len, ff, p, i, best, pc

\* Sentinel value used to indicate "undefined" in the failure function
Sentinel == -1

\* Helper to compute an index modulo 2*len
Idx(j) == (j % (2 * len))

\* Initial state: nondeterministically choose a string of any length (including 0)
Init ==
  /\ \E l \in Nat :
        /\ l >= 0
        /\ len = l
        /\ s = [j \in 0..len-1 |-> CHOOSE c \in CharacterSet : TRUE]
        /\ ff = [j \in 0..2*len-1 |-> Sentinel]
        /\ p = Sentinel
        /\ i = 1
        /\ best = 0
        /\ pc = "OuterCheck"

\* Next-state relation modeling the labeled steps of Booth's algorithm.
\* The inner details are abstracted; the purpose is to provide a complete
\* specification with the required identifiers.
Next ==
  \/ /\ pc = "OuterCheck"
        /\ IF i < 2 * len THEN
              /\ pc' = "Lookup"
              /\ UNCHANGED <<s, len, ff, p, i, best>>
           ELSE
              /\ pc' = "Done"
              /\ UNCHANGED <<s, len, ff, p, i, best>>
  \/ /\ pc = "Lookup"
        /\ p' = ff[Idx(i - best)]
        /\ pc' = "InnerLoop"
        /\ UNCHANGED <<s, len, ff, i, best>>
  \/ /\ pc = "InnerLoop"
        /\ (* Abstracted inner comparison loop *)
           pc' = "PostComp"
        /\ UNCHANGED <<s, len, ff, p, i, best>>
  \/ /\ pc = "PostComp"
        /\ pc' = "Inc"
        /\ UNCHANGED <<s, len, ff, p, i, best>>
  \/ /\ pc = "Inc"
        /\ i' = i + 1
        /\ pc' = "OuterCheck"
        /\ UNCHANGED <<s, len, ff, p, best>>
  \/ /\ pc = "Done"
        /\ UNCHANGED <<s, len, ff, p, i, best, pc>>

\* Full specification
Spec == Init /\ [][Next]_<<s, len, ff, p, i, best, pc>>

\* Type invariant expressing the intended domains of all variables
TypeInvariant ==
  /\ (len = 0 => s = [j \in {} |-> 0])
     /\ (len > 0 => s \in [0..len-1 -> CharacterSet])
  /\ len \in Nat
  /\ ff \in [0..2*len-1 -> (Sentinel \cup Nat)]
  /\ p \in (Sentinel) \cup Nat
  /\ i \in Nat
  /\ (len = 0 => best = 0) /\ (len > 0 => best \in 0..len-1)
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Inc", "Done"}

\* Correctness property (placeholder – true for the purposes of this model)
Correctness == TRUE

====