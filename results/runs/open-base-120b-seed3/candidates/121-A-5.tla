---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS CharacterSet

(*-----------------------------------------------------------------
  Definitions
-----------------------------------------------------------------*)
\* Sentinel value used to denote an undefined entry in the failure
\* function and an undefined pattern‑match index.
Sentinel == -1

\* The set of all possible program‑counter values.
PCVals == {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Inc", "Done"}

\* Helper to compute the index modulo the length of the string.
Mod(i, n) == IF n = 0 THEN 0 ELSE i % n

\* The rotation of the input string starting at offset o.
Rotation(o) == [j \in 0..(n-1) |-> str[Mod(o + j, n)]]

\* Lexicographic less‑or‑equal on two functions with domain 0..(n-1).
LexLeq(s, t) ==
  \E k \in 0..(n-1) :
    ( \A j \in 0..(k-1) : s[j] = t[j] ) /\ s[k] <= t[k]
  \/ ( \A j \in 0..(n-1) : s[j] = t[j] )

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES str, n, fail, p, i, best, pc

vars == << str, n, fail, p, i, best, pc >>

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ n >= 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN pc' = "Lookup"
        ELSE pc' = "Done"
  /\ UNCHANGED << str, n, fail, p, i, best >>

Lookup ==
  /\ pc = "Lookup"
  /\ (* retrieve failure function entry for the current position        *)
     idx == Mod(best + i, 2 * n)
  /\ p' = fail[idx]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED << str, n, fail, i, best >>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ curPos == Mod(i, n)
  /\ candPos == Mod(best + p, n)
  /\ curChar == str[curPos]
  /\ candChar == str[candPos]
  /\ IF curChar = candChar
        THEN /\ p' = p + 1
             /\ pc' = "InnerLoop"
        ELSE IF curChar # candChar
                THEN /\ pc' = "PostComp"
                     /\ UNCHANGED p
                ELSE /\ pc' = "InnerLoop"  \* unreachable
  /\ UNCHANGED << str, n, fail, i, best >>

PostComp ==
  /\ pc = "PostComp"
  /\ curPos == Mod(i, n)
  /\ candPos == Mod(best + p, n)
  /\ curChar == str[curPos]
  /\ candChar == str[candPos]
  /\ IF curChar # candChar /\ p = Sentinel
        THEN /\ IF curChar < candChar
                THEN best' = i
                ELSE best' = best
        ELSE best' = best
  /\ (* update failure function entry                                  *)
     idx == Mod(best + i, 2 * n)
  /\ fail' = [fail EXCEPT ![idx] = IF curChar = candChar
                                        THEN p + 1
                                        ELSE Sentinel]
  /\ pc' = "Inc"
  /\ UNCHANGED << str, n, p, i >>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << str, n, fail, p, best >>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostComp
  \/ Inc
  \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n-1) -> (Sentinel \cup Nat)]
  /\ p \in (Sentinel \cup Nat)
  /\ i \in 1..(2*n)
  /\ best \in 0..(n-1)
  /\ pc \in PCVals

Correctness ==
  /\ pc = "Done"
  /\ \A k \in 0..(n-1) : LexLeq(Rotation(best), Rotation(k))

(*-----------------------------------------------------------------
  The required identifiers
-----------------------------------------------------------------*)
SPECIFICATION == Spec
INVARIANTS == TypeInvariant, Correctness

====