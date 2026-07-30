---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  CharacterSet

\* The algorithm runs over a zero-indexed string held in a record field
\* named "seq".  The whole record is a structure so that any string of any
\* length up to the bound can appear nondeterministically in the initial
\* state -- the record wrapper keeps the values of the other fields fixed
\* as the string is swapped in.
StringRecord == [seq : Seq(CharacterSet)]

VARIABLES
  str,
  n,
  fail,
  patIdx,
  i,
  best,
  pc

vars == <<str, n, fail, patIdx, i, best, pc>>

NotYet == 0
Sentinel == 0
MaxLen == 2

TypeInvariant ==
  /\ str \in StringRecord
  /\ n = Len(str.seq)
  /\ fail \in [0 .. 2 * n] -> (0 .. 2 * n) \cup {Sentinel}
  /\ patIdx \in 0 .. 2 * n
  /\ i \in 1 .. 2 * n - 1
  /\ best \in 0 .. n - 1
  /\ pc \in {"outer", "lookup", "inner", "checkless", "follow", "post", "increment", "done"}

\* Lexicographic order on strings of equal length: two strings compare
\* less-than if, at the first position where they differ, one's character
\* has a smaller value.  The "lessOrEqualAll" test below is the rotation
\* version of that: every rotation of the input is >= the one at "best".
LessThan(s, t) ==
  \E k \in 1 .. Len(s) :
    /\ \A m \in 1 .. k - 1 : s[m] = t[m]
    /\ s[k] < t[k]

Rotate(s, k) ==
  \A i \in 1 .. Len(s) : s[i] = s[(i + k - 1) % Len(s) + 1]

LessOrEqualAll(k) ==
  \A r \in 0 .. n - 1 : Rotate(str.seq, k) <= Rotate(str.seq, r)

Correctness == \A k \in 0 .. n - 1 : LessOrEqualAll(best)

Init ==
  /\ \E txt \in StringRecord : str = txt
  /\ n = Len(str.seq)
  /\ fail = [j \in 0 .. 2 * n |-> Sentinel]
  /\ patIdx = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "outer"

Lookup ==
  /\ fail[i - best] # Sentinel
  /\ patIdx' = fail[i - best]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, fail, i, best>>

Outer ==
  /\ i < 2 * n
  /\ pc = "outer"
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

InnerLoop ==
  /\ pc = "inner"
  /\ str.seq[(i) % n + 1] # str.seq[(patIdx) % n + 1]
  /\ patIdx # Sentinel
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

CheckLess ==
  /\ pc = "inner"
  /\ str.seq[(i) % n + 1] # str.seq[(patIdx) % n + 1]
  /\ patIdx = Sentinel
  /\ str.seq[(i) % n + 1] < str.seq[(patIdx) % n + 1]
  /\ best' = i - patIdx
  /\ pc' = "post"
  /\ UNCHANGED <<str, n, fail, patIdx, i>>

Follow ==
  /\ pc = "inner"
  /\ patIdx # Sentinel
  /\ str.seq[(i) % n + 1] = str.seq[(patIdx) % n + 1]
  /\ patIdx' = fail[patIdx]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, fail, i, best>>

Post ==
  /\ pc = "inner"
  /\ str.seq[(i) % n + 1] # str.seq[(patIdx) % n + 1]
  /\ patIdx = Sentinel
  /\ fail' = [fail EXCEPT ![i - best] = IF str.seq[(i) % n + 1] < str.seq[(patIdx) % n + 1]
                                      THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<str, n, patIdx, i, best>>

Increment ==
  /\ pc = "post"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, fail, patIdx, best>>

Done ==
  /\ pc = "outer"
  /\ i >= 2 * n
  /\ pc' = "done"
  /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Outer \/ Lookup \/ InnerLoop \/ CheckLess \/ Follow \/ Post \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)

Terminating == <>(pc = "done")

====