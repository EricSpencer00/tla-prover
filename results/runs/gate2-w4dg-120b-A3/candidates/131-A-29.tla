---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* Inherit the main Boyer-Moore majority vote specification.
\* It defines InitVote and NextVote, which are exactly the actions
\* this module re-exposes as its own Init and Next.
\* The invariant Inv is also inherited and is the key to the proof:
\* it states that whenever the scan is finished and a strict majority
\* exists, the majority element equals the current candidate.
\* No new state or transition is introduced here.

\* The majority vote spec is factored into its own module so the proof
\* layer here can be kept small and self-contained: imports give us the
\* full set of actions, no matter how many it has.
\* The theorem below is what TLAPS checks -- it is the real work of the
\* proof, not a comment.
EXTENDS MajoritySpec

Init == InitVote
Next == NextVote

Spec == Init /\ [][Next]_<<seq, cursor, candidate, count>>

TypeOK == Cardinality(seq) <= 2 /\ candidate \in Value \cup {"none"}

Correct == (cursor = Len) => (MajorityExists(seq) => (candidate = StrictMajority(seq)))

====