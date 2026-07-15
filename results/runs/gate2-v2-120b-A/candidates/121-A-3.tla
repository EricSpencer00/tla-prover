---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet
ASSUME CharacterSet \subseteq Nat

\* Sentinel value for "undefined" entries in the failure function and pattern index
Sentinel == -1

VARIABLES
    str,        \* input string (a sequence of characters)
    n,          \* length of str
    k,          \* failure function array indexed 0..2*n
    pi,         \* pattern-match index (current failure function lookup)
    i,          \* outer loop counter (1..2*n)
    best,       \* best rotation offset (0..n-1)
    pc          \* program counter (labels of the algorithm steps)

(* ------------------------------------------------------------------------ *)
(* Initialization *)
Init ==
    /\ str \in [0..] -> CharacterSet   \* nondeterministically choose a finite sequence
    /\ n   = Len(str)
    /\ n >= 0
    /\ k   = [j \in 0..2*n |-> Sentinel]
    /\ pi  = Sentinel
    /\ i   = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(* ------------------------------------------------------------------------ *)
(* Helper definitions *)

CharAt(offset) == str[(offset % n)]

(* ------------------------------------------------------------------------ *)
(* Actions for each program-counter label *)

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i >= 2*n
          THEN /\ pc' = "Done"
               /\ UNCHANGED <<str, n, k, pi, i, best>>
          ELSE /\ pc' = "Lookup"
               /\ UNCHANGED <<str, n, k, pi, i, best>>

Lookup ==
    /\ pc = "Lookup"
    /\ LET idx == (i + best) % n IN
       /\ pi' = k[idx]
    /\ pc' = "InnerCompare"
    /\ UNCHANGED <<str, n, k, i, best>>

InnerCompare ==
    /\ pc = "InnerCompare"
    /\ LET cur == CharAt(i)
           cand == CharAt(best + pi + 1) IN
       IF cur # cand
          THEN IF pi # Sentinel
                  THEN /\ pc' = "InnerCompare"
                       /\ pi' = k[pi]   \* follow failure link
                       /\ UNCHANGED <<str, n, k, i, best>>
                  ELSE /\ pc' = "PostCompare"
                       /\ UNCHANGED <<str, n, k, i, best, pi>>
          ELSE /\ pc' = "PostCompare"
               /\ UNCHANGED <<str, n, k, i, best, pi>>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ LET cur == CharAt(i)
           cand == CharAt(best + pi + 1) IN
       IF cur < cand
          THEN /\ best' = i % n
               /\ pc' = "FollowFail"
               /\ UNCHANGED <<str, n, k, i, pi>>
          ELSE /\ UNCHANGED <<best>>
               /\ pc' = "FollowFail"

FollowFail ==
    /\ pc = "FollowFail"
    /\ pi' = IF pi = Sentinel THEN Sentinel ELSE pi + 1
    /\ LET idx == (i + best) % n IN
       /\ k' = [k EXCEPT ![idx] = pi']
    /\ pc' = "Inc"
    /\ UNCHANGED <<str, n, i, best>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET cur == CharAt(i)
           cand == CharAt(best + pi + 1) IN
       IF cur # cand /\ pi = Sentinel
          THEN IF cur < cand
                  THEN /\ best' = i % n
                  ELSE UNCHANGED best
               /\ pi' = 0
          ELSE /\ UNCHANGED <<best>>
               /\ pi' = IF pi = Sentinel THEN 0 ELSE pi + 1
    /\ LET idx == (i + best) % n IN
       /\ k' = [k EXCEPT ![idx] = (IF pi = Sentinel THEN 0 ELSE pi + 1)]
    /\ pc' = "Inc"
    /\ UNCHANGED <<str, n, i>>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, k, pi, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, k, pi, i, best, pc>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerCompare
    \/ UpdateBest
    \/ FollowFail
    \/ PostCompare
    \/ Inc
    \/ Done

(* ------------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_<<str, n, k, pi, i, best, pc>>

(* ------------------------------------------------------------------------ *)
(* Type invariant, matching the description *)
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ k \in [0..2*n -> (Sentinel \cup 0..n)]
    /\ pi = Sentinel \/ pi \in 0..n
    /\ 1 <= i <= 2*n + 1
    /\ best \in 0..Max(1, n) \ {n}   \* best is a valid index when n>0
    /\ pc \in {"OuterCheck","Lookup","InnerCompare","UpdateBest",
               "FollowFail","PostCompare","Inc","Done"}

(* ------------------------------------------------------------------------ *)
(* Correctness invariant: best points to the lexicographically minimal rotation *)
Correctness ==
    /\ n = 0 \/ \A j \in 0..n-1 :
         Rotate(str, best) <= Rotate(str, j)

Rotate(s, off) ==
    s[(off) % n] \* first character
    @@ s[(off+1) % n .. n-1] \* the rest of the rotation

(* ------------------------------------------------------------------------ *)
(* The .cfg expects the following identifiers *)
=============================================================================