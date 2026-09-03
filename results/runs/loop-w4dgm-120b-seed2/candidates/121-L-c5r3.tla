---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, ZSequences

(* The lexicographically-least circular substring algorithm from Booth's   *)
(* 1980 paper, modeled as a sequential loop over a nondeterministically      *)
(* chosen input string.  See the specification comment for the full          *)
(* system description.                                                     *)

CONSTANT CharacterSet

ASSUME CharacterSet \subseteq Nat

VARIABLES str, n, fail, patIdx, loop, best, pc

vars == <<str, n, fail, patIdx, loop, best, pc>>

Sentinel == 0

TypeInvariant ==
  /\ str \in [1..n -> CharacterSet]
  /\ n \in Nat
  /\ fail \in [0..(2 * n) -> 0..(2 * n)]
  /\ patIdx \in 0..(2 * n)
  /\ loop \in 0..(2 * n)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "inner", "setbest", "followfail",
             "postcompare", "inc", "done"}

Init ==
  /\ \E s \in [1..n -> CharacterSet] : str = s
  /\ n \in Nat /\ n >= 1
  /\ fail = [i \in 0..(2 * n) |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loop = 1
  /\ best = 0
  /\ pc = "outer"

CharAt(i) == str[((i % n) = 0) % n + 1]

Outer ==
  /\ pc = "outer"
  /\ IF loop < (2 * n) THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<str, n, fail, patIdx, loop, best>>

Lookup ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![loop] = fail[best + loop]]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, patIdx, loop, best>>

Inner ==
  /\ pc = "inner"
  /\ IF CharAt(loop) # CharAt(best + loop) /\ patIdx # Sentinel
       THEN pc' = "setbest"
       ELSE pc' = "postcompare"
  /\ UNCHANGED <<str, n, fail, patIdx, loop, best>>

SetBest ==
  /\ pc = "setbest"
  /\ IF CharAt(loop) < CharAt(best + loop)
       THEN best' = loop % n
       ELSE best' = best
  /\ pc' = "followfail"
  /\ UNCHANGED <<str, n, fail, patIdx, loop>>

FollowFail ==
  /\ pc = "followfail"
  /\ patIdx' = fail[loop]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, fail, loop, best>>

PostCompare ==
  /\ pc = "postcompare"
  /\ IF CharAt(loop) # CharAt(best + loop) /\ patIdx = Sentinel
       THEN best' = IF CharAt(loop) < CharAt(best + loop) THEN loop % n ELSE best
       ELSE best' = best
  /\ fail' = [fail EXCEPT ![loop] = IF CharAt(loop) # CharAt(best + loop)
                                    THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "inc"
  /\ UNCHANGED <<str, n, patIdx, loop>>

Inc ==
  /\ pc = "inc"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, fail, patIdx, best>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Inner \/ SetBest \/ FollowFail
        \/ PostCompare \/ Inc \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup)
        /\ WF_vars(Inner) /\ WF_vars(SetBest) /\ WF_vars(FollowFail)
        /\ WF_vars(PostCompare) /\ WF_vars(Inc)

(* The best rotation offset identifies the lexicographically-minimal         *)
(* rotation of the input string, and it is minimal among equal rotations.      *)
Correctness ==
  /\ (best \in 0..(n - 1) /\ \A s \in 0..(n - 1) :
        LET a == [i \in 0..(n - 1) |-> CharAt(i + best)]
            b == [i \in 0..(n - 1) |-> CharAt(i + s)] IN
          \A i \in 0..(n - 1) : (a[i] = b[i]) => (a[1] <= b[1]))
  /\ (n > 0 => best <= n - 1)

Termination == <>(pc = "done")

====