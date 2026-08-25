---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

(* sentinel value for undefined entries in the failure function *)
Sentinel == -1

VARIABLES str, n, fail, p, i, best, pc

vars == <<str, n, fail, p, i, best, pc>>

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
 /\ n \in Nat \ {0}
 /\ str \in [0..n-1 -> CharacterSet]
 /\ fail = [j \in 0..2*n |-> Sentinel]
 /\ p = Sentinel
 /\ i = 1
 /\ best = 0
 /\ pc = "Step"

(* ----------------------------------------------------------------------
   Helper: rotation of the string starting at a given offset
   ---------------------------------------------------------------------- *)
Rot(offset) ==
   [k \in 0..n-1 |-> str[(offset + k) % n]]

(* ----------------------------------------------------------------------
   Main step: compare the current rotation with the best one seen so far
   ---------------------------------------------------------------------- *)
Step ==
 /\ pc = "Step"
 /\ i <= 2*n
 /\ LET cur == Rot(i % n) IN
    IF cur \prec Rot(best) THEN
        /\ best' = i % n
    ELSE
        /\ best' = best
 /\ i' = i + 1
 /\ pc' = IF i' < 2*n THEN "Step" ELSE "Done"
 /\ UNCHANGED <<str, n, fail, p>>

(* ----------------------------------------------------------------------
   Stuttering after termination
   ---------------------------------------------------------------------- *)
Done ==
 /\ pc = "Done"
 /\ UNCHANGED vars

Next ==
 \/ Step
 \/ Done

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeInvariant ==
 /\ n \in Nat \ {0}
 /\ str \in [0..n-1 -> CharacterSet]
 /\ fail \in [0..2*n -> (Nat \cup {Sentinel})]
 /\ p \in Nat \cup {Sentinel}
 /\ i \in Nat
 /\ best \in 0..n-1
 /\ pc \in {"Step", "Done"}

(* ----------------------------------------------------------------------
   Correctness: best offset yields the lexicographically minimal rotation
   ---------------------------------------------------------------------- *)
Correctness ==
 /\ pc = "Done"
 /\ \A offset \in 0..n-1 : Rot(best) \preceq Rot(offset)

====