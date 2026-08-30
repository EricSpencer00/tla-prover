---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS
    CharacterSet

\* Redefine Nat as a FINITE version for model checking, but keep it from Naturals.
Nat == {1, 2}

VARIABLES
    inputString,  \* the chosen zero-indexed character sequence from the corpus
    n,            \* length of the input string
    failureFn,    \* failure function array, indexed up to twice the string length
    matchIdx,     \* pattern match index (a failure function lookup)
    loopIdx,      \* outer-loop counter (1 .. 2*n)
    bestOffset,   \* start offset of the lexicographically smallest rotation found
    pc            \* program counter: which labeled step of the algorithm is executing

vars == << inputString, n, failureFn, matchIdx, loopIdx, bestOffset, pc >>

Sentinel == 0 - 1
MaxLen == 2
MaxLoop == 2 * MaxLen

\* Zero-indexed subsequence: SubSeq(s, i, j) = s[i .. j] where i <= j.
ZeroIndexedSubSeq(s, i, j) == SubSeq(s, i + 1, j + 1)

\* Circular indexing into the input string.
CharAt(i) == inputString[(i % n)]

TypeInvariant ==
    /\ inputString \in [0 .. MaxLen - 1 -> CharacterSet]
    /\ n = Len(inputString)
    /\ failureFn \in [0 .. MaxLoop - 1 -> (0 .. MaxLoop - 1) \cup {Sentinel}]
    /\ matchIdx \in (0 .. MaxLoop - 1) \cup {Sentinel}
    /\ loopIdx \in 1 .. MaxLoop
    /\ bestOffset \in 0 .. n - 1
    /\ pc \in {"outerCheck", "lookup", "innerComp", "followChain", "postComp",
               "terminated"}

Init ==
    /\ \E s \in [0 .. MaxLen - 1 -> CharacterSet] : inputString = s
    /\ n = Len(inputString)
    /\ failureFn = [i \in 0 .. MaxLoop - 1 |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loopIdx = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopIdx < MaxLoop
       THEN pc' = "lookup"
       ELSE pc' = "terminated"
    /\ UNCHANGED << inputString, n, failureFn, matchIdx, loopIdx, bestOffset >>

Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = failureFn[loopIdx]
    /\ pc' = "innerComp"
    /\ UNCHANGED << inputString, n, failureFn, loopIdx, bestOffset >>

InnerComp ==
    /\ pc = "innerComp"
    /\ IF CharAt(loopIdx) # CharAt(bestOffset + loopIdx)
         THEN IF matchIdx = Sentinel
               THEN pc' = "postComp"
               ELSE pc' = "followChain"
         ELSE pc' = "innerComp"
    /\ UNCHANGED << inputString, n, failureFn, matchIdx, loopIdx, bestOffset >>

FollowChain ==
    /\ pc = "followChain"
    /\ matchIdx' = failureFn[matchIdx]
    /\ pc' = "innerComp"
    /\ UNCHANGED << inputString, n, failureFn, loopIdx, bestOffset >>

PostComp ==
    /\ pc = "postComp"
    /\ LET newOffset ==
           IF CharAt(loopIdx) < CharAt(bestOffset + loopIdx) THEN loopIdx ELSE bestOffset
       IN
        /\ failureFn' = [failureFn EXCEPT ![loopIdx] =
                            IF CharAt(loopIdx) # CharAt(bestOffset + loopIdx)
                              THEN IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1
                              ELSE 0]
        /\ bestOffset' = newOffset
    /\ loopIdx' = loopIdx + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED << inputString, n, matchIdx >>

Stutter ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerComp
    \/ FollowChain
    \/ PostComp
    \/ Stutter

\* The algorithm always eventually reaches its terminated state.
Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(InnerComp)
        /\ WF_vars(FollowChain) /\ WF_vars(PostComp)

\* Upon termination, the rotation at bestOffset is lexicographically <= every other,
\* and among equal rotations it has the smallest shift value.
Correctness ==
    /\ pc = "terminated"
    /\ \A k \in 0 .. n - 1 :
         /\ ZeroIndexedSubSeq(inputString, k, n - 1 #= ZeroIndexedSubSeq(inputString, bestOffset, n - 1) => k >= bestOffset
    /\ \A k \in 0 .. n - 1 :
         ZeroIndexedSubSeq(inputString, bestOffset, n - 1) <= ZeroIndexedSubSeq(inputString, k, n - 1)

Termination == (pc = "terminated") ~> (pc = "terminated")

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(InnerComp)
        /\ WF_vars(FollowChain) /\ WF_vars(PostComp)
====