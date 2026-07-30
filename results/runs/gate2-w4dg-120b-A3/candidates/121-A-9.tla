---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences, ZSequences, Naturals

CONSTANTS
    CharacterSet

VARIABLES
    inputString,          \* zero-indexed sequence of characters over CharacterSet
    strLength,            \* length of inputString
    failure,              \* failure function array (indexed 0..2*strLength)
    patIndex,             \* pattern-match index (failure function lookup)
    outer,                \* outer-loop counter (1 <= outer < 2*strLength)
    bestOffset,           \* current best rotation offset (offset of lexicographically-minimal rotation)
    pc                    \* program counter (labeled step of the algorithm)

vars == <<inputString, strLength, failure, patIndex, outer, bestOffset, pc>>

\* The set of all zero-indexed sequences over CharacterSet of length up to maxLen.
Corpus(maxLen) == { s \in (0 .. Cardinality(CharacterSet) - 1) ^ (maxLen + 1) :
                        Len(s) <= maxLen }

\* Sentinel value meaning "no failure function entry".
NOFAIL == -1

Init ==
    /\ \E s \in Corpus(1) : inputString' = s
    /\ strLength' = Len(inputString)
    /\ failure' = [i \in 0 .. 2 * (Len(inputString)) |-> NOFAIL]
    /\ patIndex' = NOFAIL
    /\ outer' = 1
    /\ bestOffset' = 0
    /\ pc' = "outer"

\* The outer loop runs while outer < 2*strLength; after that the algorithm is done.
OuterCheck ==
    /\ outer < 2 * strLength
    /\ pc' = "lookup"
    /\ UNCHANGED <<inputString, strLength, failure, patIndex, outer, bestOffset>>

LookupFailure ==
    /\ pc = "lookup"
    /\ \E i \in 0 .. 2 * strLength :
        /\ failure' = [failure EXCEPT ![i] = IF i = 0 THEN NOFAIL ELSE failure[i - 1]]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, strLength, patIndex, outer, bestOffset>>

\* Compare the character at the current outer position with that at the
\* candidate position (bestOffset ahead). The modulo arithmetic handles the circular wrap.
Compare ==
    /\ pc = "compare"
    /\ LET cur == outer % strLength
           cand == (bestOffset + outer) % strLength
       IN
        IF inputString[cur] # inputString[cand]
            /\ patIndex # NOFAIL
            THEN pc' = "compare"
            ELSE pc' = "post"
    /\ UNCHANGED <<inputString, strLength, failure, patIndex, outer, bestOffset>>

UpdateOnLess ==
    /\ pc \in {"compare", "post"}
    /\ LET cur == outer % strLength
           cand == (bestOffset + outer) % strLength
       IN inputString[cur] < inputString[cand]
    /\ bestOffset' = outer
    /\ UNCHANGED <<inputString, strLength, failure, patIndex, outer, pc>>

FollowFailure ==
    /\ pc = "compare"
    /\ patIndex' = IF patIndex = NOFAIL THEN NOFAIL ELSE failure[patIndex]
    /\ UNCHANGED <<inputString, strLength, failure, outer, bestOffset, pc>>

PostComparison ==
    /\ pc = "post"
    /\ LET cur == outer % strLength
           cand == (bestOffset + outer) % strLength
       IN
        /\ IF inputString[cur] # inputString[cand] /\ patIndex = NOFAIL /\ inputString[cur] < inputString[cand]
              THEN bestOffset' = outer
              ELSE bestOffset' = bestOffset
        /\ failure' = [failure EXCEPT ![outer] = IF patIndex = NOFAIL THEN NOFAIL ELSE patIndex + 1]
    /\ UNCHANGED <<inputString, strLength, patIndex, outer, pc>>

Increment ==
    /\ pc \in {"post", "lookup"}
    /\ outer' = outer + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, strLength, failure, patIndex, bestOffset>>

Stall ==
    /\ pc = "outer"
    /\ outer >= 2 * strLength
    /\ UNCHANGED vars

Next == OuterCheck \/ LookupFailure \/ Compare \/ UpdateOnLess \/ FollowFailure \/ PostComparison \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Increment)

\* Type invariant: every variable stays within its intended type/range.
TypeInvariant ==
    /\ inputString \in Corpus(1)
    /\ strLength = Len(inputString)
    /\ failure \in [0 .. 2 * strLength -> NOFAIL .. strLength]
    /\ patIndex \in {NOFAIL} \cup (0 .. strLength)
    /\ outer \in 0 .. (2 * strLength) + 1
    /\ bestOffset \in 0 .. (strLength - 1)
    /\ pc \in {"outer", "lookup", "compare", "post"}

\* The lexicographically-minimal rotation is found at bestOffset: it is
\* not larger than any other rotation, and among equal rotations it has
\* the smallest shift value (the offset itself).
Correctness ==
    /\ bestOffset \in 0 .. (strLength - 1)
    /\ \A i \in 0 .. (strLength - 1) :
          LET x == inputString[(bestOffset + i) % strLength]
              y == inputString[i]
          IN (x # y => x < y)
    /\ \A i \in 0 .. (strLength - 1) :
          /\ inputString[(bestOffset + i) % strLength] = inputString[i]
          /\ \A j \in 0 .. (strLength - 1) :
                inputString[(j + i) % strLength] = inputString[i] => bestOffset <= j

\* Liveness: the algorithm always eventually reaches its terminated state.
Termination == <>(pc = "outer" /\ outer >= 2 * strLength)

====