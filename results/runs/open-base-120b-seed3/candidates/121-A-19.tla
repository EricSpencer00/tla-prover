---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Finite version of Nat used for model checking
--------------------------------------------------------------------*)
CharacterSet == 0..9

(*--------------------------------------------------------------------
  Sentinel value for undefined entries in the failure function
--------------------------------------------------------------------*)
Sentinel == -1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES str, n, fail, k, i, best, pc

vars == <<str, n, fail, k, i, best, pc>>

(*--------------------------------------------------------------------
  Helper functions
--------------------------------------------------------------------*)
CharAt(pos) == 
    /\ n > 0
    /\ str[ ((pos % n) + 1) ]

PosRel == i - best

CandPos == best + PosRel

CharI == CharAt(i)

CharC == CharAt(CandPos)

Rot(s, off) == 
    << s[ ((off + (j-1)) % Len(s)) + 1 ] : j \in 1..Len(s) >>

LexLe(seq1, seq2) ==
    \/ seq1 = seq2
    \/ \E j \in 1..Len(seq1) :
          (\A k \in 1..(j-1) : seq1[k] = seq2[k]) /\ seq1[j] < seq2[j]

MinimalRotation ==
    \A off \in 0..(n-1) : LexLe(Rot(str, best), Rot(str, off))

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ fail \in [0..2*n -> Sentinel \cup Nat]
    /\ \A idx \in 0..2*n : fail[idx] = Sentinel
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Actions corresponding to each labeled step
--------------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2*n
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED <<str, n, fail, k, i, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<str, n, fail, k, i, best>>
    /\ UNCHANGED <<>>

Lookup ==
    /\ pc = "Lookup"
    /\ pos = PosRel % (2*n + 1)  \* keep index in domain
    /\ k' = fail[pos]
    /\ pc' = "InnerCompare"
    /\ UNCHANGED <<str, n, fail, i, best>>

InnerCompare ==
    /\ pc = "InnerCompare"
    /\ IF CharI = CharC
          THEN /\ pc' = "Inc"
               /\ UNCHANGED <<str, n, fail, k, i, best>>
          ELSE IF k # Sentinel
               THEN /\ pc' = "FollowFail"
                    /\ UNCHANGED <<str, n, fail, i, best>>
               ELSE /\ pc' = "PostComp"
                    /\ UNCHANGED <<str, n, fail, i, best>>
    /\ IF CharI # CharC /\ CharI < CharC
          THEN best' = i % n
          ELSE UNCHANGED best
    /\ UNCHANGED k

FollowFail ==
    /\ pc = "FollowFail"
    /\ k' = fail[k]
    /\ pc' = "InnerCompare"
    /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
    /\ pc = "PostComp"
    /\ pos = PosRel % (2*n + 1)
    /\ IF CharI < CharC
          THEN fail' = [fail EXCEPT ![pos] = Sentinel]
          ELSE fail' = [fail EXCEPT ![pos] = k + 1]
    /\ pc' = "Inc"
    /\ UNCHANGED <<str, n, k, i, best>>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerCompare
    \/ FollowFail
    \/ PostComp
    \/ Inc
    \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ fail \in [0..2*n -> Sentinel \cup Nat]
    /\ k \in Sentinel \cup Nat
    /\ i \in 0..(2*n)
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck","Lookup","InnerCompare","FollowFail",
               "PostComp","Inc","Done"}

Correctness ==
    /\ pc = "Done"
    => MinimalRotation

(*--------------------------------------------------------------------
  Liveness property (termination)
--------------------------------------------------------------------*)
Termination == <> (pc = "Done")

====================================