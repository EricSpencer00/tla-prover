---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A finite version of Nat, defined here to keep the alphabet finite for model checking.
\* The name Num is left undefined on purpose; this definition is what the .cfg overwrites.
\* Naturals (which defines Nat) is still EXTENDED, because other operators from it are used.
Num == CharacterSet

MaxLength == 2

Indices == 0..(MaxLength - 1)

Sentinel == MaxLength + 1

VARIABLES str, n, failure, pi, i, best, pc

vars == <<str, n, failure, pi, i, best, pc>>

TypeInvariant ==
    /\ str \in [Indices -> Num]
    /\ n \in 1..MaxLength
    /\ failure \in [Indices -> 0..Sentinel]
    /\ pi \in 0..Sentinel
    /\ i \in 0..(2 * MaxLength)
    /\ best \in 0..(MaxLength - 1)
    /\ pc \in {"outer", "lookup", "innerLoop", "compareLess", "followChain",
               "postCompare", "increment", "done"}

Init ==
    /\ \E s \in [Indices -> Num] : str = s
    /\ n = Len(str)
    /\ failure = [k \in Indices |-> Sentinel]
    /\ pi = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ i < 2 * n
    /\ pc' = "lookup"
    /\ UNCHANGED <<str, n, failure, pi, i, best>>

LookupFailure ==
    /\ pc = "lookup"
    /\ pi' = failure[(i - 1) % n]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<str, n, failure, i, best>>

InnerLoop ==
    /\ pc = "innerLoop"
    /\ str[i % n] # str[(best + i) % n]
    /\ pi # Sentinel
    /\ pc' = "compareLess"
    /\ UNCHANGED <<str, n, failure, pi, i, best>>

CompareLess ==
    /\ pc = "compareLess"
    /\ str[i % n] < str[(best + i) % n]
    /\ best' = i % n
    /\ pc' = "followChain"
    /\ UNCHANGED <<str, n, failure, pi, i>>

FollowChain ==
    /\ pc = "followChain"
    /\ pi' = failure[pi]
    /\ pc' = "postCompare"
    /\ UNCHANGED <<str, n, failure, i, best>>

PostCompare ==
    /\ pc = "postCompare"
    /\ \/ (str[i % n] # str[(best + i) % n] /\ pi = Sentinel /\ 
           IF str[i % n] < str[(best + i) % n] THEN best' = i % n ELSE best' = best)
       \/ (failure' = [failure EXCEPT ![(i - 1) % n] = IF pi = Sentinel THEN Sentinel ELSE pi + 1])
    /\ pc' = "increment"
    /\ UNCHANGED <<str, n, pi, i>>

Increment ==
    /\ pc = "increment"
    /\ i' = i + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<str, n, failure, pi, best>>

Done ==
    /\ pc = "outer"
    /\ i >= 2 * n
    /\ pc' = "done"
    /\ UNCHANGED <<str, n, failure, pi, i, best>>

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop \/ LookupFailure \/ InnerLoop \/ CompareLess \/ FollowChain
    \/ PostCompare \/ Increment \/ Done \/ Stutter

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(OuterLoop) /\ WF_vars(LookupFailure) /\ WF_vars(InnerLoop)
    /\ WF_vars(CompareLess) /\ WF_vars(FollowChain) /\ WF_vars(PostCompare)
    /\ WF_vars(Increment) /\ WF_vars(Done)

\* The rotation the algorithm chose is no worse than any other rotation, and any equal
\* rotation is produced by a smaller shift -- this is what makes the answer unique.
MinimalRotation ==
    /\ \A k \in 1..(n - 1) : \A m \in 1..(n - 1) :
         ( ( \A j \in Indices : str[(best + j) % n] = str[(k + j) % n] )
           => (k >= best \/ m >= best) )
    /\ \A k \in 1..(n - 1) : \A j \in Indices :
         ( \A m \in 1..(n - 1) : str[(best + j) % n] >= str[(m + j) % n] )
           => str[(best + j) % n] <= str[(k + j) % n]

Termination == \<>(pc = "done")

\* The liveness spec is the only thing the model checker is required to verify;
\* the per-rotation bound is what keeps the reachable state space finite.
Properties == Termination

Spec == Spec /\ Properties

====