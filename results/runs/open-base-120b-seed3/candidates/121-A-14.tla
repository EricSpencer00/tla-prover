---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

\* ----------------------------------------------------------------------
\* Sentinel value for undefined entries of the failure function
\* ----------------------------------------------------------------------
Sentinel == -1

VARIABLES str, len, fail, k, i, best, pc

vars == << str, len, fail, k, i, best, pc >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Return the character at position j (modulo the length of the string)
CharAt(j) == str[(j) % len]

\* Rotation starting at offset off, represented as a function from 0..len-1
Rotation(off) == [j \in 0..len-1 |-> CharAt(off + j)]

\* Lexicographic less‑or‑equal between two rotations
LexLe(s1, s2) ==
  \A j \in 0..len-1 :
    (s1[j] = s2[j]) \/
    (s1[j] < s2[j] /\ \A k \in 0..j-1 : s1[k] = s2[k])

\* The (abstract) minimal rotation of a given string
MinimalRotation(s) ==
  CHOOSE off \in 0..(Len(s)-1) :
    \A shift \in 0..(Len(s)-1) :
      LexLe( [j \in 0..Len(s)-1 |-> s[(off + j) % Len(s)]],
             [j \in 0..Len(s)-1 |-> s[(shift + j) % Len(s)]] )

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ \E n \in Nat : n > 0 /\ len = n
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail = [j \in 0..(2*len) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* One abstract step of the algorithm
\* ----------------------------------------------------------------------
OuterStep ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*len THEN
        /\ i' = i + 1
        /\ UNCHANGED << str, len, fail, k, best, pc >>
     ELSE
        /\ best' = MinimalRotation([j \in 0..len-1 |-> str[j]])
        /\ pc' = "Done"
        /\ UNCHANGED << str, len, fail, k, i >>

Next ==
  \/ OuterStep
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..len-1 -> CharacterSet]
  /\ len = Len([j \in 0..len-1 |-> str[j]])   \* length matches the domain of str
  /\ fail \in [0..2*len -> (0..2*len) \cup {Sentinel}]
  /\ k \in (0..2*len) \cup {Sentinel}
  /\ i \in 1..2*len
  /\ best \in 0..len-1
  /\ pc \in {"OuterCheck", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A shift \in 0..len-1 :
        LexLe( Rotation(best), Rotation(shift) )

====