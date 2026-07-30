---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

MODULES == "ZeroIndexedSequences"

UndefinedIndex == Nat

VARIABLES str, n, fail, fidx, i, best, pc

vars == <<str, n, fail, fidx, i, best, pc>>

TypeInvariant ==
    /\ str \in STRING(CharacterSet)
    /\ n = Len(str)
    /\ fail \in [0 .. 2 * n -> 0 .. Nat]
    /\ fidx \in 0 .. Nat
    /\ i \in 1 .. 2 * n
    /\ best \in 0 .. (n - 1)
    /\ pc \in {"outer", "lookup", "inner", "updateBest", "followChain",
               "postComp", "reset", "done"}

Init ==
    /\ str \in STRING(CharacterSet)
    /\ n = Len(str)
    /\ fail = [k \in 0 .. 2 * n |-> UndefinedIndex]
    /\ fidx = UndefinedIndex
    /\ i = 1
    /\ best = 0
    /\ pc = "outer"

Outer ==
    /\ pc = "outer"
    /\ i < 2 * n
    /\ pc' = "lookup"
    /\ UNCHANGED <<str, n, fail, fidx, i, best>>

Lookup ==
    /\ pc = "lookup"
    /\ fail[i - 1 - best] # UndefinedIndex
    /\ fidx' = fail[i - 1 - best]
    /\ pc' = "inner"
    /\ UNCHANGED <<str, n, fail, i, best>>

Inner ==
    /\ pc = "inner"
    /\ fidx # UndefinedIndex
    /\ LET c1 == str[(i - 1) % n]
           c2 == str[(i - 1 - fidx) % n]
       IN c1 = c2
    /\ pc' = "inner"
    /\ UNCHANGED <<str, n, fail, fidx, i, best>>

UpdateBest ==
    /\ pc = "inner"
    /\ fidx # UndefinedIndex
    /\ LET c1 == str[(i - 1) % n]
           c2 == str[(i - 1 - fidx) % n]
       IN c1 < c2
    /\ best' = (i - 1) % n
    /\ pc' = "followChain"
    /\ UNCHANGED <<str, n, fail, fidx, i>>

FollowChain ==
    /\ pc = "followChain"
    /\ fidx # UndefinedIndex
    /\ fidx' = fail[fidx]
    /\ pc' = "postComp"
    /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
    /\ pc = "postComp"
    /\ LET c1 == str[(i - 1) % n]
           c2 == str[(i - 1 - fidx) % n]
       IN (fidx = UndefinedIndex /\ c1 # c2 /\ c1 < c2)
    /\ best' = IF fidx = UndefinedIndex /\ LET c1 == str[(i - 1) % n]
                                            c2 == str[(i - 1 - fidx) % n]
                                         IN c1 # c2 /\ c1 < c2
                                          THEN (i - 1) % n ELSE best
    /\ fail' = [fail EXCEPT ![i - 1 - best] = IF fidx = UndefinedIndex
                                               THEN UndefinedIndex
                                               ELSE fidx + 1]
    /\ pc' = "reset"
    /\ UNCHANGED <<str, n, fidx, i>>

Reset ==
    /\ pc = "reset"
    /\ i' = i + 1
    /\ fidx' = UndefinedIndex
    /\ pc' = "outer"
    /\ UNCHANGED <<str, n, fail, best>>

Terminate ==
    /\ pc = "outer"
    /\ i >= 2 * n
    /\ pc' = "done"
    /\ UNCHANGED <<str, n, fail, fidx, i, best>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Outer \/ Lookup \/ Inner \/ UpdateBest \/ FollowChain
    \/ PostComp \/ Reset \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars

Correctness ==
    /\ \A rot \in 0 .. (n - 1) : 
         (SeqSubSeq(str, best, n) # SeqSubSeq(str, rot, n))
         \/ (SeqSubSeq(str, best, n) = SeqSubSeq(str, rot, n) /\ best <= rot)
    /\ best >= 0
    /\ best < n

Termination == pc = "done"

====