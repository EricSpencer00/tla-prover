---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* The algorithm runs sequentially (no actors) but tracks its progress through
\* a program-counter so the model checker can explore each labeled step as a
\* branch. The input string is chosen nondeterministically from all zero-indexed
\* sequences over the character set, which is precisely why we must verify the
\* lexicographic minimality for every such string, not just a few examples.
\* The "doubled" string (iterating up to twice the length) is what lets the
\* algorithm treat the input as circular without having to write any modulo
\* indexing arithmetic itself -- each index is reduced modulo the string length
\* only when a character is actually read.

CONSTANTS CharacterSet, Nat

\* The sentinel value used to mark an undefined entry in the failure function.
\* It must sit outside the valid index range (0..2*Length-1) so it never looks
\* like a genuine entry.
Undef == Nat

VARIABLES str, length, fail, pi, i, best, pc

vars == <<str, length, fail, pi, i, best, pc>>

Values == { str[k] : k \in DOMAIN str } \cup { CharacterSet }

TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ length = Len(str)
    /\ fail \in [0..(2 * length - 1) -> (0..(2 * length - 1)) \cup {Undef}]
    /\ pi \in (0..(2 * length - 1)) \cup {Undef}
    /\ i \in 0..(2 * length - 1)
    /\ best \in 0..(length - 1)
    /\ pc \in {"outer", "lookup", "compare", "follow", "postcompare", "done"}

Init ==
    /\ str \in [0..(Nat - 1) -> Values]
    /\ length = Len(str)
    /\ fail = [k \in 0..(2 * length - 1) |-> Undef]
    /\ pi = Undef
    /\ i = 1
    /\ best = 0
    /\ pc = "outer"

\* The outer loop drives the index up to twice the length so that every rotation
\* of the circular string is examined at least once.
OuterCheck ==
    /\ pc = "outer"
    /\ i < (2 * length)
    /\ pc' = "lookup"
    /\ UNCHANGED <<str, length, fail, pi, i, best>>

Lookup ==
    /\ pc = "lookup"
    /\ pi' = fail[(i - 1) % (2 * length)]
    /\ pc' = "compare"
    /\ UNCHANGED <<str, length, fail, i, best>>

CharAt(k) == str[k % length]

\* The inner loop walks back up the failure chain while the characters differ.
Compare ==
    /\ pc = "compare"
    /\ \/ (CharAt(i) # CharAt(best) /\ pi # Undef /\ pc' = "compare")
       \/ (CharAt(i) # CharAt(best) /\ pi = Undef /\ pc' = "postcompare")
       \/ (CharAt(i) = CharAt(best) /\ pc' = "postcompare")
    /\ UNCHANGED <<str, length, fail, pi, i, best>>

UpdateBest ==
    /\ CharAt(i) < CharAt(best)
    /\ best' = i % length
    /\ UNCHANGED <<str, length, fail, pi, i, best>>

Follow ==
    /\ pc = "compare"
    /\ pi # Undef
    /\ pi' = fail[pi]
    /\ pc' = "compare"
    /\ UNCHANGED <<str, length, fail, i, best>>

Postcompare ==
    /\ pc = "postcompare"
    /\ \/ (CharAt(i) # CharAt(best) /\ pi = Undef /\ pc' = "postcompare")
       \/ (CharAt(i) = CharAt(best) /\ pc' = "postcompare")
    /\ \/ (CharAt(i) # CharAt(best) /\ pi = Undef /\ UNCHANGED <<pc, fail>>)
       \/ (CharAt(i) # CharAt(best) /\ pi # Undef /\ fail' = [fail EXCEPT ![i] = pi + 1])
    /\ IF pi # Undef THEN UNCHANGED pi ELSE UNCHANGED pi
    /\ pc' = "inc"

Inc ==
    /\ pc = "postcompare"
    /\ i' = i + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<str, length, fail, pi, best>>

Terminate ==
    /\ pc = "outer"
    /\ i >= (2 * length)
    /\ pc' = "done"
    /\ UNCHANGED <<str, length, fail, pi, i, best>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Follow
    \/ Compare
    \/ UpdateBest
    \/ Postcompare
    \/ Inc
    \/ Terminate
    \/ Stall

Spec == Init /\ [][Next]_vars

\* Minimality: the rotation identified by the best offset is lexicographically
\* at most every other rotation, and among rotations that are equal it has the
\* smallest shift value (a tie is broken by shift rather than arbitrarily).
\* This is what must hold at the very end of the doubled run.
Correctness ==
    /\ \A k \in 0..(length - 1) : StrLessEq(str, best, k)
    /\ \A k \in 0..(length - 1) :
           (StrLessEq(str, k, best) /\ \A m \in 0..(length - 1) : StrLessEq(str, k, m))
               => best <= k

StrLessEq(s, a, b) ==
    \A k \in 0..(length - 1) : CharAt((a + k) % length) <= CharAt((b + k) % length)

Termination == <>(pc = "done")

\* The identifiers below are the exact ones the reference .cfg expects.
INVARIANTS == TypeInvariant, Correctness
PROPERTIES == Termination

====