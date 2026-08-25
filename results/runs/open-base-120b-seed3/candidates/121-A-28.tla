---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(*-------------------------------------------------------------------*)
(* Constants *)
CONSTANTS CharacterSet

(*-------------------------------------------------------------------*)
(* Sentinel value for undefined entries in the failure function *)
Sentinel == -1

(*-------------------------------------------------------------------*)
(* State variables *)
VARIABLES str, n, fail, k, i, best, pc

vars == << str, n, fail, k, i, best, pc >>

(*-------------------------------------------------------------------*)
(* Helper definitions *)

(* Circular indexing modulo the length of the string *)
Idx(j) == IF n = 0 THEN 0 ELSE (j % n)

(* The rotation of the string starting at offset o *)
Rotation(o) == [j \in 0..(n-1) |-> str[Idx(o + j)]]

(* Lexicographic less-or-equal between two rotations *)
LexLe(s1, s2) ==
    \E d \in 0..(n) :
        ( \A j \in 0..(d-1) : s1[j] = s2[j] ) /\
        ( d = n \/ s1[d] < s2[d] )

(*-------------------------------------------------------------------*)
(* Type invariant *)

TypeInvariant ==
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ n = Cardinality(DOMAIN str)
    /\ fail \in [0..(2*n) -> Sentinal .. n]      \* values are -1 (sentinel) or a valid index
    /\ k \in Sentinal .. n
    /\ i \in 1..(2*n)
    /\ best \in 0..(MAX(0, n-1))
    /\ pc \in {"Check","Lookup","Compare","Update","Follow","Post","Inc","Done","Stutter"}

(*-------------------------------------------------------------------*)
(* Initial state *)

Init ==
    /\ n \in Nat
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ fail = [j \in 0..(2*n) |-> Sentinal]
    /\ k = Sentinal
    /\ i = 1
    /\ best = 0
    /\ pc = "Check"

(*-------------------------------------------------------------------*)
(* Algorithm actions *)

Check ==
    /\ pc = "Check"
    /\ IF i < 2*n
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED << str, n, fail, k, i, best >>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << str, n, fail, k, i, best >>
    /\ UNCHANGED pc

Lookup ==
    /\ pc = "Lookup"
    /\ k' = fail[i]
    /\ pc' = "Compare"
    /\ UNCHANGED << str, n, fail, i, best >>

Compare ==
    /\ pc = "Compare"
    /\ LET cur  == str[Idx(i)] 
           cand == str[Idx(best + k + 1)]
       IN 
       IF cur = cand
          THEN /\ k' = k + 1
               /\ pc' = "Compare"    \* stay in compare loop
          ELSE IF cur < cand
               THEN /\ best' = i - k - 1
                    /\ pc' = "Post"
               ELSE /\ pc' = "Post"
    /\ UNCHANGED << str, n, fail, i >>

Post ==
    /\ pc = "Post"
    /\ IF k = Sentinal
          THEN /\ fail' = [fail EXCEPT ![i] = Sentinal]
          ELSE /\ fail' = [fail EXCEPT ![i] = k + 1]
    /\ pc' = "Inc"
    /\ UNCHANGED << str, n, k, i, best >>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "Check"
    /\ UNCHANGED << str, n, fail, k, best >>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Check
    \/ Lookup
    \/ Compare
    \/ Post
    \/ Inc
    \/ Stutter

(*-------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_vars

(*-------------------------------------------------------------------*)
(* Correctness property: upon termination, best points to the lexicographically
   smallest rotation of the input string. *)

Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..(n-1) : LexLe(Rotation(best), Rotation(off))

(*-------------------------------------------------------------------*)
(* The required identifiers for the configuration file *)

SPECIFICATION Spec
INVARIANTS TypeInvariant, Correctness

====