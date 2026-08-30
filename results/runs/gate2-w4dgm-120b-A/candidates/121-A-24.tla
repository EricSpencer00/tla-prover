---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

\* The character set is a finite subset of Nat; the model checking config
\* binds CharacterSet so the state space stays finite.
\* Input strings are zero-indexed sequences over CharacterSet.
\* The algorithm tracks its own program counter (pc) over the labeled steps.
\* The failure function f is indexed over a doubled string length (mod arithmetic)
\* so the circular wrap-around needs no separate logic.
\* The invariant (type checking + correctness) is what the 1980 Booth paper
\* claims: the reported rotation is the lexicographically smallest.
\* The liveness property is literal termination: the outer loop always ends.

MaxLen == 3
MaxChar == 1
Sentinel == 9999

VARIABLES str, n, f, j, k, best, pc

vars == <<str, n, f, j, k, best, pc>>

Corpus == [1..MaxLen -> CharacterSet]

Rot(s, off) == [i \in 1..n |-> s[((i + off - 1) % n) + 1]]

TypeInvariant ==
  /\ str \in Corpus
  /\ n = Len(str)
  /\ f \in [0..2 * n -> (0..2 * n) \cup {Sentinel}]
  /\ j \in 0..(2 * n)
  /\ k \in 1..(2 * n)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outerCheck", "lookupFail", "innerLoop", "updateBest", "followFail", "postCompare", "incLoop", "done"}

Init ==
  /\ \E s \in Corpus : str = s
  /\ n = Len(str)
  /\ f = [i \in 0..(2 * n) |-> Sentinel]
  /\ j = Sentinel
  /\ k = 1
  /\ best = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ pc' = IF k < 2 * n THEN "lookupFail" ELSE "done"
  /\ UNCHANGED <<str, n, f, j, k, best>>

LookupFail ==
  /\ pc = "lookupFail"
  /\ j' = f[k - best]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, f, k, best>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF str[(k % n) + 1] = str[((k - j) % n) + 1]
     THEN pc' = "postCompare"
     ELSE IF j # Sentinel
          THEN pc' = "innerLoop"
          ELSE pc' = "postCompare"
  /\ UNCHANGED <<str, n, f, j, k, best>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ best' = k - j
  /\ pc' = "followFail"
  /\ UNCHANGED <<str, n, f, j, k>>

FollowFail ==
  /\ pc = "followFail"
  /\ j' = IF j # Sentinel THEN f[j] ELSE Sentinel
  /\ pc' = "postCompare"
  /\ UNCHANGED <<str, n, f, k, best>>

PostCompare ==
  /\ pc = "postCompare"
  /\ IF str[(k % n) + 1] = str[((k - j) % n) + 1]
     THEN pc' = "incLoop"
     ELSE pc' = "updateBest"
  /\ f' = [f EXCEPT ![k] = IF j = Sentinel THEN Sentinel ELSE j + 1]
  /\ UNCHANGED <<str, n, j, k, best>>

IncLoop ==
  /\ pc = "incLoop"
  /\ k' = k + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, n, f, j, best>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == OuterCheck \/ LookupFail \/ InnerLoop \/ UpdateBest \/ FollowFail \/ PostCompare \/ IncLoop \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Incr(k)) /\ WF_vars(IncLoop)

Correctness ==
  /\ \A o \in 0..(n - 1) : Rot(str, o) >= Rot(str, best)
  /\ \A o \in 0..(n - 1) : Rot(str, o) = Rot(str, best) => o >= best

Termination == <>(pc = "done")

====