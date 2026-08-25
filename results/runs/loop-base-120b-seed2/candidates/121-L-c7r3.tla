---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, ZSequences

\* ----------------------------------------------------------------------
\* Constants and definitions
\* ----------------------------------------------------------------------
CONSTANTS
    CharacterSet \* provided by module ZSequences

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    str,          \* the input string (sequence of characters)
    len,          \* length of the input string
    fail,         \* failure function array (maps 0..2*len -> -1..len)
    pIdx,         \* current pattern‑match index (sentinel = -1)
    loop,         \* outer loop counter (1 .. 2*len)
    best,         \* best rotation offset found so far
    pc            \* program counter (labels the current step)

\* ----------------------------------------------------------------------
\* Sentinel value for “undefined”
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The sequence (0..len-1) with characters of the input string
Seq(s) == [i \in 0..Len(s)-1 |-> s[i]]

\* Rotation of the string `str` by offset `off`
Rot(off) == [i \in 0..len-1 |-> str[(off + i) % len]]

\* Lexicographic ≤ between two rotations (both of length `len`)
LexLe(off1, off2) ==
    \A k \in 0..len-1 :
        ( \A j \in 0..k-1 : Rot(off1)[j] = Rot(off2)[j] )
        => Rot(off1)[k] <= Rot(off2)[k]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ str \in Seq(CharacterSet)               \* any finite string over the character set
    /\ len = Len(str)
    /\ fail = [j \in 0..2*len |-> Sentinel]    \* all entries undefined
    /\ pIdx = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Step definitions (very abstract – they only preserve the type invariant
\* and eventually reach a terminal state)
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF loop < 2*len
          THEN pc' = "Lookup"
          ELSE pc' = "Done"
    /\ UNCHANGED <<str, len, fail, pIdx, best, loop>>

Lookup ==
    /\ pc = "Lookup"
    /\ (* In a full specification this would perform the failure‑function
          lookup and the inner comparison loop.  For the purpose of this
          model we abstract those details away. *)
    /\ pc' = "IncLoop"
    /\ UNCHANGED <<str, len, fail, pIdx, best, loop>>

IncLoop ==
    /\ pc = "IncLoop"
    /\ loop' = loop + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, len, fail, pIdx, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, len, fail, pIdx, loop, best>>

Next == \/ OuterCheck
        \/ Lookup
        \/ IncLoop
        \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, len, fail, pIdx, loop, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ len = Len(str)
    /\ fail \in [0..2*len -> Sentinel..len]   \* each entry is either Sentinel or a valid index
    /\ pIdx \in Sentinel..len
    /\ loop \in 1..2*len
    /\ best \in 0..len-1
    /\ pc \in {"OuterCheck", "Lookup", "IncLoop", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..len-1 : LexLe(best, off)

====