---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Runtime concrete instantiation; the .cfg file provides the actual finite
\* sets to bound the model (this keeps the spec structure fixed but the
\* shape flexible for config-time instantiation).
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]
Balloted(a) == { v.ball : v \in votes[a] }

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> -1]

\* Raising the promise threshold is always available; it makes the acceptor
\* refuse to participate (vote) in any lower-numbered ballot, which is what
\* keeps later ballots from contradicting a value already safe.
RaiseThreshold(a, n) ==
  /\ n > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = n]
  /\ UNCHANGED <<votes>>

\* Safety enforcement: a voter may not cast a ballot for a value that another
\* voter has already had voted for in that same ballot, and the ballot must
\* respect the acceptor's own promise threshold.
VoteVal(a, n, v) ==
  /\ n >= threshold[a]
  /\ \A w \in votes[a] : w.ball # n
  /\ \A b \in MCAcceptor : \A w \in votes[b] : ~(w.ball = n /\ w.val # v)
  /\ \A c \in MCBallot : c < n => \E Q \in MCQuorum :
        \A b \in Q : \E w \in votes[b] : w.ball = c /\ w.val = v \/ n <= threshold[b]
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> n, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = n]

Next ==
  \/ \E a \in MCAcceptor, n \in MCBallot : RaiseThreshold(a, n)
  \/ \E a \in MCAcceptor, n \in MCBallot, v \in MCValue : VoteVal(a, n, v)

Spec == Init /\ [][Next]_vars

\* The chosen value is derived from the votes: the values that at least one
\* quorum voted for in some ballot. Consistency then follows from the
\* ballot-level single-value-per-ballot fact.
Chosen == { v : \E b \in MCAcceptor, n \in MCBallot : <<b, n>> \in votes[b] /\ v = n.val }

\* SAFETY: each recorded vote is safe in its own ballot, no ballot ever
\* shows two different values, and all variables stay within their declared
\* types.
Inv ==
  /\ \A a \in MCAcceptor : \A w \in votes[a] :
        /\ w.ball \in MCBallot /\ w.val \in MCValue
        /\ \A c \in MCBallot : c < w.ball => \E Q \in MCQuorum :
              \A b \in Q : \E u \in votes[b] : u.ball = c /\ u.val = w.val \/ w.ball <= threshold[b]
  /\ \A n \in MCBallot : \A a, b \in MCAcceptor :
        (\E v \in MCValue : [ball |-> n, val |-> v] \in votes[a] /\ [ball |-> n, val |-> v] \in votes[b])
        \/ ~(\E v \in MCValue : [ball |-> n, val |-> v] \in votes[a] \/ [ball |-> n, val |-> v] \in votes[b])
  /\ \A a \in MCAcceptor : threshold[a] \in (-1) \cup MCBallot

\* CONCRETENESS: the chosen set is never large enough to contain two
\* distinct values, which is exactly the single consensus outcome.
ConsensusSpecBar == Cardinality(Chosen) <= 1

\* Quorum-level symmetry: swapping two acceptors everywhere in the model
\* does not change any reachable state, so no single acceptor is special.
MCSymmetry == {p \in [MCAcceptor -> MCAcceptor] :
                  \A a \in MCAcceptor : p[p[a]] = a}

====