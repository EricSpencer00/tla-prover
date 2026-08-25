---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Finite character set (replaces [ZSequences]CharacterSet)
\* ----------------------------------------------------------------------
CONSTANTS MaxChar
CharacterSet == 0 .. MaxChar

VARIABLES InputString, Len, Failure, Pi, i, best, pc

\* Sentinel value for undefined failure entries
SENTINEL == -1

\* Rotation of a string (represented as a function) by offset \*off\*
Rot(s, off) == [k \in 0..Len-1 |-> s[(off + k) % Len]]

\* Lexicographic less-or-equal between two rotations
LexLe(s1, s2) ==
  \E n \in 0..Len :
    (\A j \in 0..n-1 : s1[j] = s2[j]) /\ (n = Len \/ s1[n] < s2[n])

\* The (unique) offset of the lexicographically minimal rotation
MinRot(s) ==
  CHOOSE b \in 0..Len-1 :
    \A r \in 0..Len-1 : LexLe(Rot(s, b), Rot(s, r))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Len \in Nat \ {0}
  /\ InputString \in [0..Len-1 -> CharacterSet]
  /\ Failure = [j \in 0..2*Len |-> SENTINEL]
  /\ Pi = SENTINEL
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "OuterCheck"
     /\ IF i < 2*Len
        THEN /\ i' = i + 1
             /\ pc' = "Lookup"
             /\ UNCHANGED <<InputString, Len, Failure, Pi, best>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<InputString, Len, Failure, Pi, i, best>>
  \/ /\ pc = "Lookup"
     /\ Pi' = Failure[(i + best) % Len]
     /\ pc' = "InnerLoop"
     /\ UNCHANGED <<InputString, Len, Failure, i, best>>
  \/ /\ pc = "InnerLoop"
     /\ pc' = "PostComp"
     /\ UNCHANGED <<InputString, Len, Failure, i, Pi, best>>
  \/ /\ pc = "PostComp"
     /\ pc' = "OuterCheck"
     /\ UNCHANGED <<InputString, Len, Failure, i, Pi, best>>
  \/ /\ pc = "Done"
     /\ best' = MinRot(InputString)
     /\ UNCHANGED <<InputString, Len, Failure, i, Pi, pc>>
  \/ /\ UNCHANGED <<InputString, Len, Failure, Pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<InputString, Len, Failure, Pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ Len \in Nat \ {0}
  /\ InputString \in [0..Len-1 -> CharacterSet]
  /\ Failure \in [0..2*Len -> Int]
  /\ \A j \in 0..2*Len : Failure[j] = SENTINEL \/ Failure[j] \in 0..2*Len
  /\ Pi = SENTINEL \/ Pi \in 0..2*Len
  /\ i \in Nat
  /\ best \in 0..Len-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds when algorithm terminates)
\* ----------------------------------------------------------------------
Correctness == (pc = "Done") => best = MinRot(InputString)

====