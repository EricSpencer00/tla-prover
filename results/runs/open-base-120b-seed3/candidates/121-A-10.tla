---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\*--------------------------------------------------------------------
\* Finite character set (default bound, can be overridden in the .cfg)
\*--------------------------------------------------------------------
MaxChar == 9
CharacterSet == 0..MaxChar

\* Sentinel value for undefined entries
Sentinel == -1

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES str, n, fail, k, i, j, best, pc

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Rot(offset) ==
  [p \in 0..(n-1) |-> str[(offset + p) % n]]

LexLe(off1, off2) ==
  \A p \in 0..(n-1) :
    ( \A q \in 0..(p-1) : Rot(off1)[q] = Rot(off2)[q] ) => Rot(off1)[p] <= Rot(off2)[p]

MinimalRotation ==
  \A off \in 0..(n-1) :
    /\ LexLe(best, off)
    /\ (Rot(best) = Rot(off) => best <= off)

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ n \in Nat \ {0}
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [p \in 0..(2*n) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 0
  /\ j = 1
  /\ best = 0
  /\ pc = "Start"

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
StartAction ==
  /\ pc = "Start"
  /\ pc' = "Loop"
  /\ UNCHANGED <<str, n, fail, k, i, j, best>>

LoopAction ==
  /\ pc = "Loop"
  /\ IF i < n /\ j < n /\ k < n THEN
        LET ci == str[(i + k) % n]
            cj == str[(j + k) % n] IN
        IF ci = cj THEN
           /\ k' = k + 1
           /\ UNCHANGED <<i, j, best, pc, str, n, fail>>
        ELSE IF ci > cj THEN
           /\ i' = i + k + 1
           /\ i' = IF i' = j THEN i' + 1 ELSE i'
           /\ k' = 0
           /\ UNCHANGED <<j, best, pc, str, n, fail>>
        ELSE
           /\ j' = j + k + 1
           /\ j' = IF j' = i THEN j' + 1 ELSE j'
           /\ k' = 0
           /\ UNCHANGED <<i, best, pc, str, n, fail>>
        END
     ELSE
        /\ pc' = "Done"
        /\ best' = IF i < j THEN i ELSE j
        /\ UNCHANGED <<i, j, k, str, n, fail>>
  /\ UNCHANGED <<fail>>

DoneAction ==
  /\ pc = "Done"
  /\ pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, j, best>>

Next ==
  \/ StartAction
  \/ LoopAction
  \/ DoneAction

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, k, i, j, best, pc>>

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat \ {0}
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> (Sentinel \cup Nat)]
  /\ k \in (Sentinel \cup Nat)
  /\ i \in Nat
  /\ j \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"Start", "Loop", "Done"}

Correctness ==
  (pc = "Done") => MinimalRotation

====