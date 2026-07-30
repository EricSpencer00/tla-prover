---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* Booth's lexicographically-least rotation algorithm, modeled exactly as
\* described.  The failure function is indexed over the doubled string length
\* (a single linear scan over the rotation candidates, wrapping via Mod).
\* Zero-indexing comes from the utility module this spec depends on.
CONSTANTS
    CharacterSet,
    Nat

VARIABLES
    w,          \* input string, a zero-indexed sequence of characters
    n,          \* length of w
    fail,       \* failure function array (indexed up to 2*n)
    matchIdx,   \* current failure function lookup index (or sentinel)
    i,          \* outer loop counter (1 <= i < 2*n)
    best,       \* start of lexicographically-minimal rotation found so far
    pc          \* program counter: which labeled step is executing

vars == <<w, n, fail, matchIdx, i, best, pc>>

Sentinel == 99
MaxString == 2
MaxAlphabet == 2

TypeInvariant ==
    /\ w \in Seq(CharacterSet)
    /\ n = Len(w)
    /\ fail \in [0..(2 * MaxString) -> 0..(2 * MaxString) \cup {Sentinel}]
    /\ matchIdx \in 0..(2 * MaxString) \cup {Sentinel}
    /\ i \in 1..(2 * MaxString)
    /\ best \in 0..(MaxString - 1)
    /\ pc \in {"outer", "lookup", "compare", "reset", "post", "increment"}

Init ==
    /\ \E s \in Seq(CharacterSet) : w = s
    /\ n = Len(w)
    /\ fail = [k \in 0..(2 * MaxString) |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "outer"

\* Outer loop check; i runs from 1 up to just below 2*n across the doubled run.
OuterCheck ==
    /\ pc = "outer"
    /\ i < 2 * n
    /\ pc' = "lookup"
    /\ UNCHANGED <<w, n, fail, matchIdx, i, best>>

\* Failure function lookup for the current position relative to the best offset.
Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = fail[(i - 1) % n + best]
    /\ pc' = "compare"
    /\ UNCHANGED <<w, n, fail, i, best>>

\* Inner loop: compare characters at the current and candidate positions,
\* following failure links when they differ.
Compare ==
    /\ pc = "compare"
    /\ LET cur == w[(i % n) + 1] IN
       LET cand == w[((i - 1) % n + best) % n + 1] IN
       LET chLess == cur < cand IN
       /\ IF cur = cand
           THEN pc' = "compare"
           ELSE
               /\ IF matchIdx # Sentinel
                    THEN pc' = "compare"
                    ELSE pc' = "post"
               /\ best' = IF cur = cand /\ chLess THEN i % n ELSE best
               /\ matchIdx' = IF cur = cand THEN matchIdx ELSE Sentinel
    /\ UNCHANGED <<w, n, fail, i>>

\* Follow the failure function chain by moving to the linked index.
Reset ==
    /\ pc = "compare"
    /\ matchIdx # Sentinel
    /\ matchIdx' = fail[matchIdx]
    /\ UNCHANGED <<w, n, fail, i, best, pc>>

\* Post-comparison cleanup: reset or extend the failure function entry.
Post ==
    /\ pc = "post"
    /\ LET cur == w[(i % n) + 1] IN
       LET cand == w[((i - 1) % n + best) % n + 1] IN
       LET chLess == cur < cand IN
       /\ IF cur # cand /\ chLess THEN best' = i % n ELSE best' = best
    /\ fail' = [fail EXCEPT ![((i - 1) % n + best) % (2 * MaxString) + 1] =
                    IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<w, n, matchIdx, i>>

\* Increment the loop counter and return to the outer loop check.
Increment ==
    /\ pc = "increment"
    /\ i' = i + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<w, n, fail, matchIdx, best>>

\* The algorithm has terminated (the outer loop has run past 2*n); it may
\* stutter here forever, which is what the liveness check looks for.
Done ==
    /\ pc = "outer"
    /\ i >= 2 * n
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Compare
    \/ Reset
    \/ Post
    \/ Increment
    \/ Done

\* The lexicographically-minimal rotation is the smallest of all rotations of w.
\* Rotating by k returns the circular shift of w starting at position k.
Rotate(k) ==
    [j \in 1..n |-> w[((k + j - 2) % n) + 1]]

Correctness ==
    /\ \A k \in 0..(n - 1) : Rotate(best) <= Rotate(k)
    /\ \A k \in 0..(n - 1) : Rotate(best) = Rotate(k) => best <= k

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "outer" /\ i >= 2 * n)

====