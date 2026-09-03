---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, ZSequences

(* The circular-substring algorithm is guarded by a loop counter that runs      *)
(* up to twice the string length, so the inner comparison step never needs an    *)
(* explicit "i < j" guard -- the counter is what keeps it in range.              *)

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

VARIABLES str, n, failure, pat, i, offset, pc
vars == <<str, n, failure, pat, i, offset, pc>>

Undefined == n
Sentinel == n + 1

TypeInvariant ==
    /\ str \in [1..n -> CharacterSet]
    /\ n \in Nat
    /\ failure \in [0..2*n -> 0..(n + 1)]
    /\ pat \in 0..(n + 1)
    /\ i \in 0..(2 * n)
    /\ offset \in 0..(n - 1)
    /\ pc \in {"loop", "lookup", "inner", "less", "follow", "post", "final"}

\* The loop counter is the only guard against i going past the doubled length.
Init ==
    /\ \E s \in [1..n -> CharacterSet] : str = s
    /\ n \in Nat
    /\ failure = [k \in 0..2*n |-> n + 1]
    /\ pat = n + 1
    /\ i = 1
    /\ offset = 0
    /\ pc = "loop"

\* Outer loop guard: i < 2*n is the only thing keeping the inner block safe.
OuterLoop ==
    /\ pc = "loop"
    /\ i < 2 * n
    /\ pc' = "lookup"
    /\ UNCHANGED <<str, n, failure, pat, i, offset>>

LookupFailure(k) ==
    failure[(i + k + n) % n]

\* The inner block runs on while the characters differ and the chain has not
\* run out; the loop counter is what stops it from looping forever.
Compare ==
    /\ pc = "lookup"
    /\ LET k == LookupFailure(offset) IN
        /\ pat' = k
        /\ pc' = IF k # Undefined /\ str[i % n] # str[(i + k) % n]
                   THEN "inner"
                   ELSE "post"
    /\ UNCHANGED <<str, n, failure, i, offset>>

Less ==
    /\ pc = "inner"
    /\ str[i % n] < str[(i + offset) % n]
    /\ offset' = i % n
    /\ pc' = "follow"
    /\ UNCHANGED <<str, n, failure, pat, i>>

Follow ==
    /\ pc = "inner"
    /\ pat # Undefined
    /\ pc' = "follow"
    /\ UNCHANGED <<str, n, failure, pat, i, offset>>

FollowFailureChain ==
    /\ pc = "follow"
    /\ LET k == LookupFailure(offset) IN
        /\ pat' = k
        /\ pc' = IF k = Undefined THEN "post" ELSE "inner"
    /\ UNCHANGED <<str, n, failure, i, offset>>

\* When the chain is exhausted, a new mismatch either moves the best offset
\* or fixes the failure function entry for the next round.
PostCompare ==
    /\ pc = "post"
    /\ LET k == LookupFailure(offset) IN
        /\ failure' = [failure EXCEPT ![(i + offset) % n] =
                         IF k = Undefined /\ str[i % n] = str[(i + offset) % n]
                         THEN Undefined ELSE pat + 1]
    /\ offset' = IF pat = Undefined /\ str[i % n] < str[(i + offset) % n]
                 THEN i % n ELSE offset
    /\ pc' = "final"
    /\ UNCHANGED <<str, n, pat, i>>

Advance ==
    /\ pc = "final"
    /\ i' = i + 1
    /\ pc' = "loop"
    /\ UNCHANGED <<str, n, failure, pat, offset>>

Terminate ==
    /\ pc = "final"
    /\ i = 2 * n
    /\ UNCHANGED vars

Stall == Terminate

Next == OuterLoop \/ Compare \/ Less \/ Follow \/ FollowFailureChain
        \/ PostCompare \/ Advance \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Advance) /\ WF_vars(Stall)

\* The best offset must also be shift-minimal among equal rotations.
Correctness ==
    /\ \A j \in 0..(n - 1) :
        LET rot(k) == <<str[(k + i) % n] : i \in 0..(n - 1)>> IN
            (rot(j) \preceq rot(offset) /\ (rot(j) = rot(offset) => j >= offset))
    /\ \A i \in 0..(n - 1) : str[i] = str[(offset + i) % n]

Termination == (pc # "final") ~> (pc = "final")

====