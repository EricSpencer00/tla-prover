---- MODULE LeastCircularSubstring ----
EXTENDS Integers

CONSTANTS
    CharacterSet

None == -1

VARIABLES
    seq, length, fail, patIdx, i, best, pc

vars == <<seq, length, fail, patIdx, i, best, pc>>

ZSeq == (1..length) -> CharacterSet

TypeOK ==
    /\ seq \in ZSeq
    /\ length = Len(seq)
    /\ fail \in [0..(2 * length)] -> (0..(2 * length)) \cup {None}
    /\ patIdx \in (0..(2 * length)) \cup {None}
    /\ i \in 0..(2 * length)
    /\ best \in 0..(length - 1)
    /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateBest", "followFail", "postCmp", "increment", "done"}

Init ==
    /\ \E s \in ZSeq : seq = s
    /\ length = Len(seq)
    /\ fail = [k \in 0..(2 * length) |-> None]
    /\ patIdx = None
    /\ i = 1
    /\ best = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ i < 2 * length
    /\ pc' = "lookup"
    /\ UNCHANGED <<seq, length, fail, patIdx, i, best>>

Lookup ==
    /\ pc = "lookup"
    /\ fail[i \% length] \in (0..(2 * length)) \cup {None}
    /\ patIdx' = fail[i \% length]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<seq, length, fail, i, best>>

InnerLoop ==
    /\ pc = "innerLoop"
    /\ i \% length \notin {best, (best + (patIdx + 1) % length) % length}
    /\ patIdx # None
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<seq, length, fail, patIdx, i, best>>

UpdateBest ==
    /\ pc = "innerLoop"
    /\ i \% length \notin {best, (best + (patIdx + 1) % length) % length}
    /\ patIdx # None
    /\ seq[i \% length] < seq[(best + (patIdx + 1) % length) % length]
    /\ best' = i % length
    /\ pc' = "followFail"
    /\ UNCHANGED <<seq, length, fail, patIdx, i>>

FollowFail ==
    /\ pc = "followFail"
    /\ patIdx # None
    /\ patIdx' = fail[patIdx]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<seq, length, fail, i, best>>

PostCmp ==
    /\ pc = "innerLoop"
    /\ i \% length \notin {best, (best + (patIdx + 1) % length) % length}
    /\ patIdx = None
    /\ seq[i \% length] < seq[(best + (patIdx + 1) % length) % length]
    /\ best' = i % length
    /\ fail' = [fail EXCEPT ![i \% length] = None]
    /\ pc' = "increment"
    /\ UNCHANGED <<seq, length, patIdx, i>>

Increment ==
    /\ pc = "increment"
    /\ i' = i + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<seq, length, fail, patIdx, best>>

Done ==
    /\ pc = "outerCheck"
    /\ i >= 2 * length
    /\ pc' = "done"
    /\ UNCHANGED <<seq, length, fail, patIdx, i, best>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBest \/ FollowFail
    \/ PostCmp \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)

LessOrEq(s, t) ==
    \E k \in 0..(length - 1) : \A j \in 0..(length - 1) : s[(s + k) % length] <= t[(t + j) % length]

Correctness ==
    /\ (pc = "done") => (LessOrEq(best, 0) /\ (\A j \in 1..(length - 1) : best <= j))

Termination == <>(pc = "done")

====