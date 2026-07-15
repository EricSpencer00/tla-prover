---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    CharacterSet, \* a finite subset of Nat representing the alphabet
    Nat         \* the set of natural numbers (used as sentinel)

\* ----------------------------------------------------------------------
\* Sentinel value for undefined entries in the failure function and pattern index
\* ----------------------------------------------------------------------
Sentinel == Nat

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    str,        \* input string (a sequence of characters)
    n,          \* length of the input string
    fail,       \* failure function array indexed from 0..2*n-1
    p,          \* pattern‑match index (may be Sentinel)
    i,          \* outer loop counter, runs from 1 to 2*n
    best,       \* current best rotation offset
    pc          \* program counter indicating the current labeled step

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(j) == j % n               \* circular index into the string
CharAt(seq, j) == seq[Idx(j)] \* character at position j modulo n

\* ----------------------------------------------------------------------
\* Type invariant (required by the .cfg)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ n >= 0
    /\ i \in 1..(2 * n)
    /\ best \in 0..(n-1)
    /\ p \in (0..(n-1)) \cup {Sentinel}
    /\ fail \in [0..(2*n-1) -> (0..(n-1)) \cup {Sentinel}]
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "UpdateBest",
               "FollowFail", "PostComp", "Increment", "Done"}

\* ----------------------------------------------------------------------
\* Initial state (required by the .cfg)
\* ----------------------------------------------------------------------
Init ==
    /\ str \in Seq(CharacterSet)          \* nondeterministic input string
    /\ n = Len(str)
    /\ i = 1
    /\ best = 0
    /\ p = Sentinel
    /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions corresponding to the labeled steps of Booth's algorithm
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED <<str, n, fail, p, i, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<str, n, fail, p, i, best>>

Lookup ==
    /\ pc = "Lookup"
    /\ let pos == i - 1 in
       /\ p' = fail[pos]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF CharAt(str, i) # CharAt(str, best + p + 1)
          THEN IF p # Sentinel
                  THEN /\ p' = fail[p]
                       /\ pc' = "InnerLoop"
                       /\ UNCHANGED <<str, n, fail, i, best>>
                  ELSE /\ pc' = "PostComp"
                       /\ UNCHANGED <<str, n, fail, p, i, best>>
          ELSE /\ p' = p + 1
               /\ pc' = "Lookup"
               /\ UNCHANGED <<str, n, fail, i, best>>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ p # Sentinel
    /\ CharAt(str, i) < CharAt(str, best + p + 1)
    /\ best' = i
    /\ UNCHANGED <<str, n, fail, p, i, pc>>

FollowFail ==
    /\ pc = "FollowFail"
    /\ p' = fail[p]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
    /\ pc = "PostComp"
    /\ IF CharAt(str, i) < CharAt(str, best + p + 1)
          THEN /\ best' = i
               /\ fail' = [fail EXCEPT ![i-1] = Sentinel]
          ELSE /\ best' = best
               /\ fail' = [fail EXCEPT ![i-1] = IF p = Sentinel THEN Sentinel ELSE p + 1]
    /\ pc' = "Increment"
    /\ UNCHANGED <<str, n, p, i>>

Increment ==
    /\ pc = "Increment"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, fail, p, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, p, i, best, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, p, i, best, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation (required by the .cfg)
\* ----------------------------------------------------------------------
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ UpdateBest
    \/ FollowFail
    \/ PostComp
    \/ Increment
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification (the temporal formula, required by the .cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, p, i, best, pc>>

\* ----------------------------------------------------------------------
\* Safety property: Correctness of the computed rotation (required by the .cfg)
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A j \in 0..(n-1) :
          \A k \in 0..(n-1) :
            LET rB == << CharAt(str, best + t) : t \in 0..(n-1) >> IN
            LET rJ == << CharAt(str, k + t) : t \in 0..(n-1) >> IN
            ( rB # rJ => rB < rJ ) /\ ( rB = rJ => best <= k )

\* ----------------------------------------------------------------------
\* Liveness property (optional, not required by the .cfg but useful)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Theorem (helps TLC but is not required)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

=============================================================================