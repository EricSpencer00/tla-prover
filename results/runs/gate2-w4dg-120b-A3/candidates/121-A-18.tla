---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences, Naturals

CONSTANTS
    CharacterSet

\* Derived constants: the failure function is indexed up to twice the string length,
\* so the maximum index is twice the maximum length. The sentinel indicates "undef".
Sentinel == -1

VARIABLES
    str,        \* the input string (zero-indexed sequence of chars from CharacterSet)
    len,        \* length of the input string
    fail,       \* failure function array indexed 0..2*len
    matchIdx,   \* pattern-match index (failure function lookup)
    i,          \* outer loop counter, runs 1..<2*len
    bestOff,    \* best rotation offset found so far
    pc          \* program counter: which labeled step of the algorithm is active

vars == <<str, len, fail, matchIdx, i, bestOff, pc>>


TypeInvariant ==
    /\ str \in [0..(len - 1) -> CharacterSet]
    /\ len \in Nat
    /\ fail \in [0..(2 * len) -> (Nat \cup {Sentinel})]
    /\ matchIdx \in (Nat \cup {Sentinel})
    /\ i \in Nat
    /\ bestOff \in Nat
    /\ pc \in {"outerCheck", "lookup", "inner", "updateBest", "followFail",
               "postComp", "increment", "done"}

\* Compare the rotation at offset a with the rotation at offset b, lexicographically.
RotationLeq(a, b) ==
    \E k \in Nat :
        LET n == len IN
            \A offset \in 0..(n - 1) :
                LET ca == str[(a + offset) % n]
                    cb == str[(b + offset) % n]
                IN IF ca # cb THEN ca <= cb ELSE @

Init ==
    /\ \E s \in [0..(CharacterSet) -> CharacterSet] :
        /\ CharacterSet # {}
        /\ s \in [0..(len - 1) -> CharacterSet]
        /\ str' = s
    /\ len' = Len(str)
    /\ fail' = [k \in 0..(2 * len) |-> Sentinel]
    /\ matchIdx' = Sentinel
    /\ i' = 1
    /\ bestOff' = 0
    /\ pc' = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF i < 2 * len THEN pc' = "lookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<str, len, fail, matchIdx, i, bestOff>>

Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = fail[i - 1]
    /\ pc' = "inner"
    /\ UNCHANGED <<str, len, fail, i, bestOff>>

Inner ==
    /\ pc = "inner"
    /\ LET a == i % len
           b == bestOff % len
           ca == str[a]
           cb == str[b]
       IN
        /\ IF ca # cb /\ matchIdx # Sentinel
            THEN pc' = "inner"
            ELSE pc' = "postComp"
        /\ UNCHANGED <<str, len, fail, i, bestOff>>
    /\ UNCHANGED matchIdx

UpdateBest ==
    /\ pc = "updateBest"
    /\ LET a == i % len
           b == bestOff % len
           ca == str[a]
           cb == str[b]
       IN ca < cb /\ bestOff' = a
    /\ UNCHANGED <<str, len, fail, matchIdx, i, pc>>

FollowFail ==
    /\ pc = "followFail"
    /\ matchIdx' = IF matchIdx # Sentinel THEN fail[matchIdx] ELSE Sentinel
    /\ pc' = "inner"
    /\ UNCHANGED <<str, len, fail, i, bestOff>>

PostComp ==
    /\ pc = "postComp"
    /\ LET a == i % len
           b == bestOff % len
           ca == str[a]
           cb == str[b]
       IN
        /\ IF ca # cb /\ matchIdx = Sentinel /\ ca < cb
            THEN bestOff' = a
            ELSE bestOff' = bestOff
        /\ fail' = [fail EXCEPT ![i - 1] =
                        IF ca # cb /\ matchIdx = Sentinel
                            THEN Sentinel
                            ELSE matchIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<str, len, matchIdx, i>>

Increment ==
    /\ pc = "increment"
    /\ i' = i + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<str, len, fail, matchIdx, bestOff>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == OuterCheck \/ Lookup \/ Inner \/ UpdateBest \/ FollowFail \/ PostComp \/ Increment \/ Done

InitNext == Init /\ Next

Spec == Init /\ [][Next]_vars /\ WF_vars(Init /\ Next)

Correctness ==
    \A a \in 0..(len - 1) : RotationLeq(bestOff, a)

Termination == <>(pc = "done")

\* The .cfg replaces Nat with a finite zero-indexed character set; keep EXTENDS Naturals
CharacterSet == Nat
====