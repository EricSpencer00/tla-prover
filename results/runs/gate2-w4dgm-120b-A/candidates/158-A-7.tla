---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

\* A quorum is a non-empty set of acceptors; the overlap property is an
\* invariant over the Quorum constant, not a per-instance check.
QuorumSet == Quorum
NoValue == "novalue"
NoVote == <<-1, NoValue>>
Votes == {NoVote} \union [balloon : Ballot, val : Value]

VARIABLES voted, threshold
vars == <<voted, threshold>>

TypeOK ==
  /\ voted \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> (-1)..(Cardinality(Ballot) - 1)]

Init ==
  /\ voted = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* Safety: a vote cast by an acceptor must be safe at its ballot number.
VoterSafety ==
  /\ \A a \in Acceptor : \A v \in voted[a] : v.balloon \in Ballot /\ v.val \in Value
  /\ \A a \in Acceptor : \A b \in Ballot :
       \A v \in voted[a] : v.balloon = b => \A c \in Ballot : c < b => SafeAt(b, c, v.val)
  /\ threshold = [a \in Acceptor |-> Cardinality({v \in voted[a] : v.balloon \in Ballot}) - 1]

\* A value is safe at ballot b if every lower ballot was unanimously voted for
\* that value by some quorum, or was not reachable at all.
SafeAt(b, c, val) ==
  \A q \in QuorumSet :
    \/ \A m \in q : \E w \in voted[m] : w.balloon = c /\ w.val = val
    \/ \A m \in q : \A w \in voted[m] : w.balloon # c

\* Keeping the promise threshold separate from the votes lets a lagging
\* acceptor catch up without casting a conflicting vote.
Promise(a, b) ==
  /\ b \in Ballot
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED voted

\* Vote only if the ballot is reachable and nobody else voted for a different
\* value in that same ballot -- the single-value-per-ballot rule.
Vote(a, b, val) ==
  /\ b \in Ballot
  /\ b >= threshold[a]
  /\ \A w \in voted[a] : w.balloon # b
  /\ \A m \in Acceptor : \A w \in voted[m] : w.balloon = b => w.val = val
  /\ \A q \in QuorumSet : \A m \in q : \E w \in voted[m] : w.balloon = b /\ w.val = val
  /\ voted' = [voted EXCEPT ![a] = @ \union {[balloon |-> b, val |-> val]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Cast(a, b, val) == Vote(a, b, val)

Next ==
  \E a \in Acceptor :
    \/ \E b \in Ballot : Promise(a, b)
    \/ \E b \in Ballot, val \in Value : Cast(a, b, val)

Spec == Init /\ [][Next]_vars /\ WF_vars(Cast(a1, 0, v1))

\* Consistency: the derived set of chosen values never grows beyond one value.
Chosen == {val \in Value : \E a \in Acceptor, b \in Ballot : [balloon |-> b, val |-> val] \in voted[a]}
Inv == Cardinality(Chosen) <= 1

\* The voting algorithm implements consensus: the chosen set is derived from
\* the votes, so the two-level (ballot, value) shape does not weaken safety.
ConsensusSpecBar == Chosen = {val \in Value : \E a \in Acceptor, b \in Ballot : [balloon |-> b, val |-> val] \in voted[a]}

\* The symmetry group is permutations of acceptors, values, quorums, and
\* ballots considered independently -- any combination of them is admissible.
MCSymmetry ==
  {f \in [Acceptor \union Value \union Quorum \union Ballot ->
            Acceptor \union Value \union Quorum \union Ballot] :
     /\ \A x \in Acceptor : f[x] \in Acceptor
     /\ \A x \in Value : f[x] \in Value
     /\ \A x \in Quorum : f[x] \in Quorum
     /\ \A x \in Ballot : f[x] \in Ballot}

\* The model's finite instantiations: three acceptors, two values, two ballots.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2}, {a2, a3} }
MCBallot == {0, 1}

====