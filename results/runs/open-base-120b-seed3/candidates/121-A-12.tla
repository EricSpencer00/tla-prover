---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, ZSequences

\*----------------------------------------------------------------------
\* Constants
\*----------------------------------------------------------------------
CONSTANTS CharacterSet

\*----------------------------------------------------------------------
\* Variables
\*----------------------------------------------------------------------
VARIABLES inputString, len, fail, k, i, best, pc

\*----------------------------------------------------------------------
\* Definitions
\*----------------------------------------------------------------------
SENTINEL == -1

PCs == {"OuterCheck", "Compare", "Update", "Inc", "Done"}

\* Rotation of the string starting at offset \*off\*
Rot(s, off) ==
  [j \in 0..(len-1) |-> s[(off + j) % len]]

\* Lexicographic less‑or‑equal on two rotations
LexLeq(s1, s2) ==
  \/ s1 = s2
  \/ \E p \in 0..(len-1) :
        ( \A q \in 0..(p-1) : s1[q] = s2[q] )
        /\ s1[p] < s2[p]

\*----------------------------------------------------------------------
\* Type invariant
\*----------------------------------------------------------------------
TypeInvariant ==
  /\ inputString \in Seq(CharacterSet)
  /\ len = Len(inputString)
  /\ fail \in [0..(2*len) -> (SENTINEL \cup 0..(2*len))]
  /\ k \in (SENTINEL \cup 0..(2*len))
  /\ i \in 1..(2*len)
  /\ best \in 0..(len-1)
  /\ pc \in PCs

\*----------------------------------------------------------------------
\* Correctness property: best points to a lexicographically minimal rotation
\*----------------------------------------------------------------------
Correctness ==
  /\ len >= 0
  /\ \A off \in 0..(len-1) :
        LexLeq(Rot(inputString, best), Rot(inputString, off))

\*----------------------------------------------------------------------
\* Initialization
\*----------------------------------------------------------------------
Init ==
  \E s \in Seq(CharacterSet) :
    /\ inputString = s
    /\ len = Len(s)
    /\ fail = [j \in 0..(2*len) |-> SENTINEL]
    /\ k = SENTINEL
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\*----------------------------------------------------------------------
\* Algorithm actions (a faithful rendition of Booth's algorithm)
\*----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*len
        THEN pc' = "Compare"
        ELSE pc' = "Done"
  /\ UNCHANGED << inputString, len, fail, k, i, best >>

Compare ==
  /\ pc = "Compare"
  /\ (* ensure k is a natural number for the comparison *)
     k' = IF k = SENTINEL THEN 0 ELSE k
  /\ a == inputString[(i + k') % len]
  /\ b == inputString[(best + k') % len]
  /\ IF a = b
        THEN /\ k'' = k' + 1
              /\ IF k'' = len
                    THEN /\ i' = 2*len           \* all characters matched; terminate
                         /\ pc' = "Done"
                    ELSE /\ k' = k''            \* continue matching
                         /\ i' = i
                         /\ pc' = "Compare"
        ELSE IF a # b
                THEN /\ IF a > b
                         THEN /\ i' = i + k' + 1
                              /\ best' = best
                     ELSE /\ i' = i + k' + 1
                          /\ best' = i
                     /\ k' = 0
                     /\ pc' = "OuterCheck"
        ELSE /\ UNCHANGED << >>  \* unreachable
  /\ UNCHANGED << inputString, len, fail >>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << inputString, len, fail, k, best >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED << inputString, len, fail, k, i, best, pc >>

\* The NEXT relation allows the algorithm to take the defined steps.
Next ==
  \/ OuterCheck
  \/ Compare
  \/ Inc
  \/ Done

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
vars == << inputString, len, fail, k, i, best, pc >>

Spec == Init /\ [][Next]_vars

\*----------------------------------------------------------------------
\* Invariants for the model checker
\*----------------------------------------------------------------------
INVARIANTS TypeInvariant, Correctness

====