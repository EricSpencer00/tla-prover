--------------------------- MODULE LeastCircularSubstring ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

(* The character set is a finite subset of Nat.  The spec redefines CharacterSet as   *)
(* a Nat constant for .cfg compatibility (keep EXTENDS Naturals, do NOT declare Nat).*)
ASSUME CharacterSet \subseteq Nat /\ CharacterSet # {}

\* Zero-indexed sequences (SeqOf) are taken from a separate utility module, not  *
\* the standard Sequences module, so the spec never uses the standard one-indexed *
\* sequence operators directly.                                                *

VARIABLES string, length, fail, pat, loop, best, pc

vars == <<string, length, fail, pat, loop, best, pc>>

MaxLen == 2
Sentinel == 99
Terms == [idx : 0 .. MaxLen, val : CharacterSet \cup {Sentinel}]

TypeOK ==
    /\ string \in [0 .. MaxLen -> CharacterSet]
    /\ length \in 1 .. MaxLen
    /\ fail \in [0 .. MaxLen -> Terms]
    /\ pat \in 0 .. Sentinel
    /\ loop \in 1 .. (2 * MaxLen)
    /\ best \in 0 .. (MaxLen - 1)
    /\ pc \in {"outerCheck", "lookupFail", "innerLoop", "updateBest", "followChain",
                "postCompare", "final"}

Init ==
    /\ \E s \in [0 .. MaxLen -> CharacterSet] :
        /\ string = s
        /\ length = Len([i \in 0 .. MaxLen |-> IF i <= Len(s) THEN s[i] ELSE CHOOSE c \in CharacterSet : TRUE])
    /\ fail = [i \in 0 .. MaxLen |-> [idx |-> i, val |-> Sentinel]]
    /\ pat = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loop < (2 * length) THEN pc' = "lookupFail" ELSE pc' = "final"
    /\ UNCHANGED <<string, length, fail, pat, loop, best>>

LookupFail ==
    /\ pc = "lookupFail"
    /\ pat' = fail[loop % length].val
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<string, length, fail, loop, best>>

InnerLoop ==
    /\ pc = "innerLoop"
    /\ IF string[loop % length] # string[(best + loop) % length] /\ pat # Sentinel
       THEN pc' = "compareStep" ELSE pc' = "postCompare"
    /\ UNCHANGED <<string, length, fail, pat, loop, best>>

compareStep == "updateBest"

UpdateBest ==
    /\ pc = "updateBest"
    /\ IF string[loop % length] < string[(best + loop) % length]
       THEN best' = (best + loop) % length
       ELSE best' = best
    /\ pc' = "followChain"
    /\ UNCHANGED <<string, length, fail, pat, loop>>

FollowChain ==
    /\ pc = "followChain"
    /\ pat' = fail[pat].val
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<string, length, fail, loop, best>>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF string[loop % length] # string[(best + loop) % length] /\ pat = Sentinel
       THEN IF string[loop % length] < string[(best + loop) % length]
             THEN best' = (best + loop) % length
             ELSE best' = best
       ELSE best' = best
    /\ fail' = [fail EXCEPT ![loop % length] =
                    IF string[loop % length] = string[(best + loop) % length]
                    THEN [idx |-> loop % length, val |-> IF pat = Sentinel THEN Sentinel ELSE pat + 1]
                    ELSE [idx |-> loop % length, val |-> Sentinel]]
    /\ pc' = "increment"
    /\ UNCHANGED <<string, length, pat, loop>>

Increment ==
    /\ pc = "increment"
    /\ loop' = loop + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<string, length, fail, pat, best>>

Stutter ==
    /\ pc = "final"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ LookupFail \/ InnerLoop \/ UpdateBest \/ FollowChain
    \/ PostCompare \/ Increment \/ Stutter

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(OuterCheck) /\ WF_vars(LookupFail) /\ WF_vars(InnerLoop)
    /\ WF_vars(UpdateBest) /\ WF_vars(FollowChain) /\ WF_vars(PostCompare)
    /\ WF_vars(Increment)

TypeInvariant == TypeOK

\* Correctness: the rotation at `best` is lexicographically no greater than any other
\* rotation, and among equal rotations it has the smallest shift.
Correctness ==
    /\ \A i \in 0 .. (length - 1) :
         LET a == [k \in 0 .. (length - 1) |-> string[(best + k) % length]]
             b == [k \in 0 .. (length - 1) |-> string[(i + k) % length]]
         IN (a # b) => (a \prec b)
    /\ \A i \in 0 .. (length - 1), j \in 0 .. (length - 1) :
         (LET a == [k \in 0 .. (length - 1) |-> string[(i + k) % length]]
              b == [k \in 0 .. (length - 1) |-> string[(j + k) % length]]
          IN (a = b) => i <= j)

Termination == <>(pc = "final")

=============================================================================