---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS CharacterSet, Nat

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
Sentinel == -1

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES str, len, fail, p, i, best, pc

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
Chars == CharacterSet

ZeroIdxSeq(s) == s           \* already zero-indexed, defined in Sequences

Idx(j) == j % len            \* circular indexing

(* ----------------------------------------------------------------------
   Type (safety) invariant
   ---------------------------------------------------------------------- *)
TypeInvariant ==
  /\ str \in [0..len-1 -> Chars]
  /\ len \in Nat \ {0}
  /\ fail \in [0..2*len-1 -> (0..2*len-1) \cup {Sentinel}]
  /\ p \in (0..2*len-1) \cup {Sentinel}
  /\ i \in 1..2*len
  /\ best \in 0..len-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostCmp", "Inc",
             "Done", "Stutter"}

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ \E n \in Nat \ {0} :
        /\ len = n
        /\ str \in [0..len-1 -> Chars]
  /\ fail = [j \in 0..2*len-1 |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*len THEN
        /\ pc' = "Lookup"
        /\ UNCHANGED <<str, len, fail, p, i, best>>
     ELSE
        /\ pc' = "Done"
        /\ UNCHANGED <<str, len, fail, p, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ pc' = "InnerLoop"
  /\ p' = fail[ best + i ]
  /\ UNCHANGED <<str, len, fail, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ LET cur == str[Idx(i)]
         cand == str[Idx(best + i)] IN
     IF cur = cand THEN
        /\ pc' = "Inc"
        /\ UNCHANGED <<str, len, fail, p, i, best>>
     ELSE IF p # Sentinel THEN
        /\ pc' = "Lookup"
        /\ p' = fail[p]
        /\ UNCHANGED <<str, len, fail, i, best>>
     ELSE
        /\ pc' = "PostCmp"
        /\ UNCHANGED <<str, len, fail, p, i, best>>

PostCmp ==
  /\ pc = "PostCmp"
  /\ LET cur == str[Idx(i)]
         cand == str[Idx(best + i)] IN
     /\ IF cur # cand THEN
          /\ IF cur < cand THEN best' = i
             ELSE best' = best
        ELSE best' = best
     /\ IF cur # cand THEN
          /\ fail' = [fail EXCEPT ![best + i] = Sentinel]
        ELSE
          /\ fail' = [fail EXCEPT ![best + i] = 
                        IF p = Sentinel THEN 0 ELSE p + 1]
     /\ pc' = "Inc"
     /\ UNCHANGED <<str, len, p, i>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, len, fail, p, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, len, fail, p, i, best, pc>>

Stutter ==
  /\ pc = "Stutter"
  /\ UNCHANGED <<str, len, fail, p, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostCmp
  \/ Inc
  \/ Done
  \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<str, len, fail, p, i, best, pc>>

(* ----------------------------------------------------------------------
   Correctness invariant (lexicographically minimal rotation)
   ---------------------------------------------------------------------- *)
Rot(i) == << [j \in 0..len-1 |-> str[Idx(i + j)] ] >>

Correctness ==
  /\ pc = "Done"
  /\ \A j \in 0..len-1 :
        Rot(best) <=_lex Rot(j)

(* Lexicographic comparison for sequences of characters *)
_<=_lex(s, t) ==
  \A k \in 0..len-1 :
        ( \E m \in 0..k-1 : s[m] # t[m] ) => FALSE
        \/ ( k = len ) \/ s[k] <= t[k]

=============================================================================