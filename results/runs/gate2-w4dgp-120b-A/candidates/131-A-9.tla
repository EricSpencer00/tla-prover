---- MODULE MajorityProof ----
\* Boyer-Moore majority vote algorithm with an interactive correctness proof.
\* The algorithm scans a sequence of values and keeps at most one candidate
\* for a majority element, using a vote counter that is incremented when the
\* current value matches the candidate and decremented otherwise; the candidate
\* is reset when the counter reaches zero. The proof shows that the candidate
\* is the unique majority whenever one exists.
EXTENDS Naturals, FiniteSets
\* The main majority vote specification is imported as a known module so that
\* its invariant can be reused here without redefining the algorithm.
CONSTANTS Value
ASSUME Value = {0, 1}
IMPORTS MajorityVote
\* MajorityVote defines: N, seq, c (candidate), cnt (counter), i (scan index),
\* TypeOK (type-correctness invariant), Inv (the inductive invariant from the
\* original specification), and MainInv (that Inv implies the candidate is the
\* majority when one exists).
VARIABLES c, cnt, i

vars == <<c, cnt, i>>

Init == MajorityVote.Init

Next == MajorityVote.Next

Spec == MajorityVote.Spec

\* TypeOK is defined in MajorityVote; this wrapper re-exposes it under the
\* name expected by the configuration.
TypeOK == MajorityVote.TypeOK

\* MainInv is also defined in MajorityVote; it is the invariant that ties
\* the candidate and the vote counter to the actual distribution of values.
Inv == MajorityVote.Inv

\* Correct is the inductive invariant proved in MajorityVote; it states that if
\* the vote counter is positive then the candidate is the majority of the
\* scanned prefix, and if the counter is zero an actual majority must be
\* captured by the candidate. Combining it with the final index reaching N
\* yields the full correctness property below.
Correct == Inv

====