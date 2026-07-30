---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, Integers
CONSTANTS CharacterSet

\* This replaces the built-in Nat with a finite subset of it, derived from
\* the model's character set. The .cfg file maps Nat to this, so Nat is a
\* constant from the model's perspective, not the built-in infinite type.
ASSUME Nat \subseteq CharacterSet

N == Cardinality(CharacterSet)
SENTINEL == 0 - 1
MaxLen == 2

VARIABLES str, len, fail, pi, loop, best, pc
vars == <<str, len, fail, pi, loop, best, pc>>

\* A nondeterministic input string over the character set, of length
\* up to MaxLen, drawn from the full corpus of such strings.
Corpus == UNION { [1..n -> C] : n \in 0..MaxLen, C \in SUBSET CharacterSet }

TypeInvariant ==
  /\ str \in Corpus
  /\ len = Len(str)
  /\ fail \in [0..(2 * MaxLen) -> Nat \cup {SENTINEL}]
  /\ pi \in Nat \cup {SENTINEL}
  /\ loop \in 1..(2 * MaxLen)
  /\ best \in 0..MaxLen
  /\ pc \in {"outer", "lookup", "inner", "updateBest", "followChain", "postcompare"}

Init ==
  /\ str \in Corpus
  /\ len = Len(str)
  /\ fail = [i \in 0..(2 * MaxLen) |-> SENTINEL]
  /\ pi = SENTINEL
  /\ loop = 1
  /\ best = 0
  /\ pc = "outer"

\* Wrap around the string using modular indexing into the original
\* zero-indexed sequence; the loop runs up to twice the length.
CurrentChar == str[((loop - 1) % len) + 1]
CandidateChar == str[((best + pi) % len) + 1]

Outer ==
  /\ pc = "outer"
  /\ loop < (2 * MaxLen)
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, len, fail, pi, loop, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pi' = fail[(best + loop) % (2 * MaxLen)]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, len, fail, loop, best>>

Inner ==
  /\ pc = "inner"
  /\ CurrentChar # CandidateChar
  /\ pi # SENTINEL
  /\ pc' = "followChain"
  /\ UNCHANGED <<str, len, fail, pi, loop, best>>

UpdateBest ==
  /\ pc = "inner"
  /\ CurrentChar < CandidateChar
  /\ best' = loop % len
  /\ pc' = "followChain"
  /\ UNCHANGED <<str, len, fail, pi, loop>>

FollowChain ==
  /\ pc = "followChain"
  /\ pi' = fail[pi]
  /\ pc' = "postcompare"
  /\ UNCHANGED <<str, len, fail, loop, best>>

PostCompare ==
  /\ pc = "postcompare"
  /\ LET newBest ==
         IF CurrentChar # CandidateChar /\ pi = SENTINEL /\ CurrentChar < CandidateChar
         THEN loop % len
         ELSE best
     IN
       /\ best' = newBest
       /\ fail' = [fail EXCEPT ![pi] = IF pi = SENTINEL THEN SENTINEL ELSE pi + 1]
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, len, pi>>

Done ==
  /\ pc = "outer"
  /\ loop >= (2 * MaxLen)
  /\ UNCHANGED vars

Stall ==
  /\ pc = "outer"
  /\ loop >= (2 * MaxLen)
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Inner \/ UpdateBest \/ FollowChain \/ PostCompare \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(FollowChain) /\ WF_vars(PostCompare)

\* Correctness: best names the offset of the lexicographically-minimal
\* rotation; the rotation at best is <= every other rotation, and ties
\* are broken by the smallest shift value.
LesserRotation ==
  \A k \in 0..(len - 1) :
    LET r1 == \A i \in 1..len : str[((best + i - 1) % len) + 1]
                     <= str[((k + i - 1) % len) + 1]
        r2 == ~(\A i \in 1..len : str[((k + i - 1) % len) + 1]
                     <= str[((best + i - 1) % len) + 1])
        r3 == best <= k
    IN r1 \/ (r2 /\ r3)

Correctness == pc = "outer" /\ loop >= (2 * MaxLen) => LesserRotation

Termination == <>(pc = "outer" /\ loop >= (2 * MaxLen))

====