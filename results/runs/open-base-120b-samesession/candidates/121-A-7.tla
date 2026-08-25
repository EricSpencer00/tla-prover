---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, ZSequences

\* --------------------------------------------------------------
\* Finite character set (overriding the one from ZSequences)
\* --------------------------------------------------------------
CONSTANT MaxChar
ASSUME MaxChar \in Nat
CharacterSet == 0 .. MaxChar

\* --------------------------------------------------------------
\* State variables
\* --------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

\* Sentinel value used for “undefined’’ entries
Sentinel == -1

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
CharAt(p) == 
  IF n = 0 THEN Sentinel 
  ELSE str[(p % n) + 1]          \* Sequences in TLA+ are 1‑indexed

Rotation(off) ==
  << str[( (j + off) % n) + 1] : j \in 0..(n-1) >>

LexLessOrEq(s, t) ==
  \A j \in 1..Len(s) : 
    IF s[j] # t[j] THEN s[j] < t[j] ELSE TRUE

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
  /\ str \in Seq(CharacterSet)          \* nondeterministic input string
  /\ n   = Len(str)                     \* length of the input
  /\ fail = [j \in 0..(2*n) |-> Sentinel]
  /\ k   = Sentinel
  /\ i   = 1
  /\ best = 0
  /\ pc  = "OuterCheck"

\* --------------------------------------------------------------
\* Next‑state relation (algorithmic steps)
\* --------------------------------------------------------------
Next ==
  \/ /\ pc = "OuterCheck"
     /\ i < 2*n
     /\ pc' = "Lookup"
     /\ UNCHANGED <<str, n, fail, k, best, i>>
  \/ /\ pc = "OuterCheck"
     /\ i >= 2*n
     /\ pc' = "Done"
     /\ UNCHANGED <<str, n, fail, k, best, i>>
  \/ /\ pc = "Lookup"
     /\ pos  = i - 1
     /\ k'   = fail[best + pos]
     /\ pc'  = "InnerLoop"
     /\ UNCHANGED <<str, n, fail, best, i>>
  \/ /\ pc = "InnerLoop"
     /\ cur  = CharAt(i)
     /\ cand = CharAt(best + k)
     /\ IF cur = cand THEN
          /\ fail' = [fail EXCEPT ![best + i] = k + 1]
          /\ k'    = Sentinel
          /\ pc'   = "OuterInc"
          /\ UNCHANGED <<str, n, best, i>>
        ELSE IF k # Sentinel THEN
          /\ k'   = fail[best + k]
          /\ pc'  = "InnerLoop"
          /\ UNCHANGED <<str, n, fail, best, i, cur, cand>>
        ELSE
          /\ IF cur < cand THEN best' = i ELSE best' = best
          /\ fail' = [fail EXCEPT ![best + i] = Sentinel]
          /\ k'    = Sentinel
          /\ pc'   = "OuterInc"
          /\ UNCHANGED <<str, n, i>>
  \/ /\ pc = "OuterInc"
     /\ i'  = i + 1
     /\ pc' = "OuterCheck"
     /\ UNCHANGED <<str, n, fail, k, best>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

\* --------------------------------------------------------------
\* Invariants
\* --------------------------------------------------------------
TypeInvariant ==
  /\ str \in Seq(CharacterSet)
  /\ n   = Len(str)
  /\ fail \in [0..2*n -> Nat \cup {Sentinel}]
  /\ k   \in Nat \cup {Sentinel}
  /\ i   \in Nat
  /\ best \in (IF n = 0 THEN {0} ELSE 0..(n-1))
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "OuterInc", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A shift \in (IF n = 0 THEN {} ELSE 0..(n-1)) :
        LexLessOrEq(Rotation(best), Rotation(shift))

\* --------------------------------------------------------------
\* End of module
\* --------------------------------------------------------------
====