---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANTS CharacterSet

\*--------------------------------------------------------------------
\* Sentinel value for undefined entries
\*--------------------------------------------------------------------
Sentinel == -1

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES str, n, f, p, i, best, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
CharAt(pos) == 
  IF n = 0 THEN 0 ELSE str[pos % n]

Rotation(off) == [k \in 0..(n-1) |-> CharAt(off + k)]

RotLessOrEq(off1, off2) ==
  \A k \in 0..(n-1) :
    IF Rotation(off1)[k] # Rotation(off2)[k] 
      THEN Rotation(off1)[k] < Rotation(off2)[k] 
      ELSE TRUE

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f = [j \in 0..(2*n) |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
Check ==
  /\ pc = "Check"
  /\ IF i < 2*n
        THEN /\ pc' = "Lookup"
        ELSE /\ pc' = "Done"
  /\ UNCHANGED <<str, n, f, p, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ idx == (i + best) % n
  /\ p' = f[idx]
  /\ pc' = "Compare"
  /\ UNCHANGED <<str, n, f, i, best>>

Compare ==
  LET cur  == CharAt(i)
      cand == CharAt((best + (p + 1)) % n)
  IN
    /\ pc = "Compare"
    /\ IF cur = cand
          THEN /\ p' = p + 1
               /\ pc' = "Compare"
          ELSE /\ pc' = "Post"
    /\ UNCHANGED <<str, n, f, i, best>>

Post ==
  LET cur  == CharAt(i)
      cand == CharAt((best + (p + 1)) % n)
      idx  == (i + best) % n
  IN
    /\ pc = "Post"
    /\ IF cur # cand /\ p = Sentinel
          THEN /\ IF cur < cand THEN best' = i % n ELSE UNCHANGED best
               /\ f' = [f EXCEPT ![idx] = Sentinel]
          ELSE /\ IF cur < cand THEN best' = i % n ELSE UNCHANGED best
               /\ f' = [f EXCEPT ![idx] = p + 1]
    /\ pc' = "Inc"
    /\ UNCHANGED <<str, n, i, p>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "Check"
  /\ UNCHANGED <<str, n, f, p, best>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, p, i, best, pc>>

Next == \/ Check \/ Lookup \/ Compare \/ Post \/ Inc \/ Stutter

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, f, p, i, best, pc>>

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f \in [0..(2*n) -> (Nat \cup {Sentinel})]
  /\ p \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ (n = 0 => best = 0) /\ (n # 0 => best \in 0..(n-1))
  /\ pc \in {"Check", "Lookup", "Compare", "Post", "Inc", "Done"}

\*--------------------------------------------------------------------
\* Correctness property
\*--------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A j \in 0..(n-1) : RotLessOrEq(best, j)

\*--------------------------------------------------------------------
\* The exported identifiers required by the .cfg file
\*--------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeInvariant, Correctness

====