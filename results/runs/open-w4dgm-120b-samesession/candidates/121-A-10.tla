---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences
\* A literal string literal is a finite sequence, so LiteralToSeq is only
\* needed to move a literal into the ZSequences module's CharacterSet.
ImportFrom ZSequences

CONSTANTS CharacterSet

Sentinel == 0
MaxLoops == 4
StringLengths == 1..MaxLoops
\* The ZSequences module needs a literal that is a full sequence; this is
\* a literal sequence, not a string, so the squiggly braces are the right
\* choice and there is no literal-to-sequence conversion needed.
LiteralString == <<"a", "b", "c">>
LiteralToSeq(L) == L

VARIABLES inputStr, strLen, failure, pmatch, outerIter, bestOffset, pc

vars == <<inputStr, strLen, failure, pmatch, outerIter, bestOffset, pc>>

TypeInvariant ==
  /\ inputStr \in LiteralToSeq(CharacterSet)
  /\ strLen = Len(inputStr)
  /\ failure \in [0..(2 * strLen) -> 0..(2 * strLen)]
  /\ pmatch \in 0..(2 * strLen)
  /\ outerIter \in 1..(2 * strLen)
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outer", "lookup", "inner", "replace", "follow", "post", "done"}

Init ==
  /\ inputStr \in LiteralToSeq(CharacterSet)
  /\ strLen = Len(inputStr)
  /\ failure = [i \in 0..(2 * strLen) |-> Sentinel]
  /\ pmatch = Sentinel
  /\ outerIter = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* Outer loop that iterates twice over the string so the failure function can
\* see the whole doubled (circular) string at once.
Outer ==
  /\ pc = "outer"
  /\ outerIter < (2 * strLen)
  /\ pc' = "lookup"
  /\ UNCHANGED <<inputStr, strLen, failure, pmatch, outerIter, bestOffset>>

\* Failure function lookup for the current position relative to the best
\* offset discovered so far.
Lookup ==
  /\ pc = "lookup"
  /\ pmatch' = failure[(outerIter + bestOffset) % strLen]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputStr, strLen, failure, outerIter, bestOffset>>

\* Inner comparison: characters at the current position vs. the candidate
\* position (mod the string length), walking the failure chain outward.
InnerComp ==
  /\ pc = "inner"
  /\ \/ inputStr[(outerIter % strLen) + 1]
       = inputStr[((outerIter + pmatch) % strLen) + 1]
     \/ pmatch = Sentinel
  /\ pc' = "post"
  /\ UNCHANGED <<inputStr, strLen, failure, pmatch, outerIter, bestOffset>>

\* A lexicographically smaller character at a later position makes the
\* current position the new best rotation offset.
Replace ==
  /\ pc = "inner"
  /\ inputStr[(outerIter % strLen) + 1]
       < inputStr[((outerIter + pmatch) % strLen) + 1]
  /\ bestOffset' = outerIter % strLen
  /\ pc' = "post"
  /\ UNCHANGED <<inputStr, strLen, failure, pmatch, outerIter>>

\* Failure function chain follows to the next node outward (or the
\* sentinel, which ends the inner loop).
FollowChain ==
  /\ pc = "inner"
  /\ pmatch # Sentinel
  /\ pmatch' = failure[pmatch]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputStr, strLen, failure, outerIter, bestOffset>>

\* Post-comparison: if the characters still differ and the failure chain
\* is exhausted, the inner loop is done and the failure function is reset
\* (no match) or extended by one.
PostComp ==
  /\ pc = "post"
  /\ IF \/ (pmatch = Sentinel
            /\ inputStr[(outerIter % strLen) + 1]
                 = inputStr[((outerIter + pmatch) % strLen) + 1]
            \/ (pmatch = Sentinel
                /\ inputStr[(outerIter % strLen) + 1]
                     >= inputStr[((outerIter + pmatch) % strLen) + 1]
                /\ failure' = [failure EXCEPT ![outerIter + bestOffset] = Sentinel]
               )
       THEN UNCHANGED <<inputStr, strLen, pmatch, outerIter, bestOffset>>
       ELSE /\ failure' = [failure EXCEPT ![outerIter + bestOffset] = pmatch + 1]
            /\ UNCHANGED <<inputStr, strLen, pmatch, outerIter, bestOffset>>
  /\ pc' = "inc"
  /\ UNCHANGED <<inputStr, strLen>>

\* Loop iteration counter; when it reaches its bound the algorithm exits.
IncIter ==
  /\ pc = "inc"
  /\ outerIter' = outerIter + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputStr, strLen, failure, pmatch, bestOffset>>

\* The algorithm has reached its bound and simply stays here.
Done ==
  /\ pc = "outer"
  /\ outerIter = (2 * strLen)
  /\ pc' = "done"
  /\ UNCHANGED <<inputStr, strLen, failure, pmatch, outerIter, bestOffset>>

\* After termination the specification idles rather than stopping.
Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Outer \/ Lookup \/ Replace \/ FollowChain
  \/ InnerComp \/ PostComp \/ IncIter \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup)

\* The rotation at the best offset is lexicographically no greater than any
\* other rotation of the input string, and among ties it has the smallest
\* shift (the lexicographically-first occurrence of the minimal rotation).
Correctness ==
  /\ \A shift \in 0..(strLen - 1) :
       SubSeq(LiteralToSeq(inputStr), bestOffset + strLen) <=
         SubSeq(LiteralToSeq(inputStr), shift + strLen)
  /\ \A shift \in 0..(strLen - 1) :
       SubSeq(LiteralToSeq(inputStr), bestOffset + strLen) =
         SubSeq(LiteralToSeq(inputStr), shift + strLen) => bestOffset <= shift

Termination == (pc = "outer") ~> (pc = "done")

====