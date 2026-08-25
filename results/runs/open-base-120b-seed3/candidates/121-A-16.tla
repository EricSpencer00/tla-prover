---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS CharacterSet

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
(* sentinel value used for undefined entries in the failure function *)
sentinel == -1

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES str, n, fail, k, i, best, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
CharAt(pos) == str[pos % n]

Rot(off, j) == CharAt((off + j) % n)

(* A finite version of Nat for modules that expect a bounded Nat set *)
FiniteNat == CharacterSet

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ n \in Nat \ {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail = [j \in 0..(2*n-1) |-> sentinel]
    /\ k = sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ i < 2 * n
    /\ pc' = "Lookup"
    /\ UNCHANGED <<str, n, fail, k, best, i>>

DoneCheck ==
    /\ pc = "OuterCheck"
    /\ i >= 2 * n
    /\ pc' = "Done"
    /\ UNCHANGED <<str, n, fail, k, best, i>>

Lookup ==
    /\ pc = "Lookup"
    /\ best' = IF CharAt(i % n) < CharAt(best) THEN i % n ELSE best
    /\ pc' = "PostComp"
    /\ UNCHANGED <<str, n, fail, k, i>>

PostComp ==
    /\ pc = "PostComp"
    /\ i' = i + 1
    /\ pc' = IF i' < 2 * n THEN "OuterCheck" ELSE "Done"
    /\ UNCHANGED <<str, n, fail, k, best>>

DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

Next ==
    \/ OuterCheck
    \/ DoneCheck
    \/ Lookup
    \/ PostComp
    \/ DoneStutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ n \in Nat \ {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail \in [0..2*n-1 -> (sentinel \cup 0..n-1)]
    /\ k = sentinel \/ k \in 0..2*n-1
    /\ i \in 0..2*n
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck", "Lookup", "PostComp", "Done"}

Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..n-1 :
         ( \E j \in 0..n-1 :
               /\ \A k \in 0..j-1 : Rot(best, k) = Rot(off, k)
               /\ Rot(best, j) < Rot(off, j) )
         \/ (\A k \in 0..n-1 : Rot(best, k) = Rot(off, k))

(*-----------------------------------------------------------------
  Exported identifiers required by the .cfg file
-----------------------------------------------------------------*)
SPECIFICATION Spec
INVARIANTS TypeInvariant, Correctness

====