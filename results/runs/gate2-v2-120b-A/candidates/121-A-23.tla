---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet, Nat

(*---------------------------------------------------------------------
-- Constants
---------------------------------------------------------------------*)
Sentinel == -1

(*---------------------------------------------------------------------
-- Variables
---------------------------------------------------------------------*)
VARIABLES 
    inputString,        \* sequence of characters (zero-indexed)
    n,                  \* length of inputString
    failure,            \* function [0..2*n-1] -> Nat ∪ {Sentinel}
    patIdx,             \* pattern-match index (Nat ∪ {Sentinel})
    i,                  \* outer loop counter (Nat)
    best,               \* best rotation offset (0..n-1)
    pc                  \* program counter (label of current step)

vars == << inputString, n, failure, patIdx, i, best, pc >>

(*---------------------------------------------------------------------
-- Helper definitions
---------------------------------------------------------------------*)
CharSeq == { s \in Seq(CharacterSet) : Len(s) = n }

CharAt(i_) == inputString[(i_ % n) + 1]   \* Seq is 1-indexed; we map 0-index to 1-index

(* Equality modulo length, used for failure function entries *)
ValidIndex(j) == 0 <= j /\ j < 2 * n

(*---------------------------------------------------------------------
-- Initialization
---------------------------------------------------------------------*)
Init ==
    /\ inputString \in Seq(CharacterSet)      \* nondeterministic input
    /\ n = Len(inputString)
    /\ failure = [j \in 0..(2*n-1) |-> Sentinel]
    /\ patIdx = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*---------------------------------------------------------------------
-- Actions (one per labeled step)
---------------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i >= 2 * n
          THEN /\ pc' = "Done"
               /\ UNCHANGED << inputString, n, failure, patIdx, i, best >>
          ELSE /\ pc' = "Lookup"
               /\ UNCHANGED << inputString, n, failure, patIdx, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ idx = (best + i) % n
    /\ patIdx' = failure[idx]
    /\ pc' = "InnerComp"
    /\ UNCHANGED << inputString, n, failure, i, best >>

InnerComp ==
    /\ pc = "InnerComp"
    /\ IF patIdx = Sentinel 
          THEN /\ pc' = "PostComp"
               /\ UNCHANGED << inputString, n, failure, i, best, patIdx >>
          ELSE /\ curChar = CharAt(i)
               /\ candChar = CharAt(best + i - patIdx)
               /\ IF curChar = candChar
                     THEN /\ pc' = "PostComp"
                          /\ UNCHANGED << inputString, n, failure, i, best, patIdx >>
                     ELSE IF curChar < candChar
                              THEN /\ best' = i - patIdx
                                   /\ pc' = "FollowFailure"
                                   /\ UNCHANGED << inputString, n, failure, i, patIdx >>
                              ELSE /\ patIdx' = failure[(best + i - patIdx) % n]
                                   /\ pc' = "InnerComp"
                                   /\ UNCHANGED << inputString, n, failure, i, best >>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ patIdx' = Sentinel
    /\ pc' = "PostComp"
    /\ UNCHANGED << inputString, n, failure, i, best >>

PostComp ==
    /\ pc = "PostComp"
    /\ curChar = CharAt(i)
    /\ candChar = CharAt(best + i)
    /\ IF curChar # candChar /\ patIdx = Sentinel
          THEN IF curChar < candChar
                  THEN /\ best' = i
                  ELSE UNCHANGED best
          ELSE UNCHANGED best
    /\ IF curChar = candChar
          THEN /\ failure[(best + i) % n]' = patIdx + 1
          ELSE /\ failure[(best + i) % n]' = Sentinel
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << inputString, n, patIdx >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == 
    \/ OuterCheck
    \/ Lookup
    \/ InnerComp
    \/ FollowFailure
    \/ PostComp
    \/ Done
    \/ Stutter

(*---------------------------------------------------------------------
-- Specification
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*---------------------------------------------------------------------
-- Type invariant (ensures all variables stay within their domains)
---------------------------------------------------------------------*)
TypeInvariant ==
    /\ inputString \in Seq(CharacterSet)
    /\ n = Len(inputString)
    /\ failure \in [0..(2*n-1) -> (Nat \cup {Sentinel})]
    /\ patIdx \in Nat \cup {Sentinel}
    /\ i \in Nat
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerComp", "FollowFailure",
               "PostComp", "Done"}

(*---------------------------------------------------------------------
-- Correctness invariant (lexicographically minimal rotation)
---------------------------------------------------------------------*)
Correctness ==
    /\ pc = "Done"
    /\ \A k \in 0..(n-1) :
         LET rotB == [j \in 0..(n-1) |-> CharAt(best + j)] IN
         LET rotK == [j \in 0..(n-1) |-> CharAt(k + j)] IN
         ( \A j \in 0..(n-1) :
               rotB[j] = rotK[j] ) => best <= k

=============================================================================