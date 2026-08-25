---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

\* --------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* --------------------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* --------------------------------------------------------------
\* Operators that map the abstract constants to the concrete ones
\* (these are overridden by the configuration file)
\* --------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* --------------------------------------------------------------
\* State variables
\* --------------------------------------------------------------
VARIABLES Voted, Threshold

\* Voted[a] is the set of votes cast by acceptor a.
\* A vote is a record [ballot : Ballot, value : Value].
\* Threshold[a] is the minimum ballot number a will ever vote in
\* (initially -1, meaning no promise has been made).
\* --------------------------------------------------------------
Init ==
    /\ Voted = [a \in MCAcceptor |-> {}]
    /\ Threshold = [a \in MCAcceptor |-> -1]

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------

\* A vote for ballot b and value v is safe at (b,v) if for every
\* lower ballot c < b there exists a quorum Q such that every
\* acceptor in Q either already voted for v in c or can never
\* vote in c (i.e., its threshold is already > c).
\* --------------------------------------------------------------
SafeAt(b, v) ==
    /\ b \in MCBallot
    /\ v \in MCValue
    /\ \A c \in MCBallot :
        (c < b) =>
          \E Q \in MCQuorum :
            /\ Q \subseteq MCAcceptor
            /\ \A a \in Q :
                 ( \E vote \in Voted[a] :
                       /\ vote.ballot = c
                       /\ vote.value = v )
                 \/ (Threshold[a] > c)

\* At most one distinct value may be voted for in any given ballot.
\* --------------------------------------------------------------
OneValuePerBallot ==
    \A a1, a2 \in MCAcceptor :
      \A v1, v2 \in MCValue :
        \A b \in MCBallot :
          (<<b, v1>> \in Voted[a1] /\ <<b, v2>> \in Voted[a2]) => v1 = v2

\* Every stored vote is safe at its ballot.
\* --------------------------------------------------------------
AllVotesSafe ==
    \A a \in MCAcceptor :
      \A vote \in Voted[a] :
        SafeAt(vote.ballot, vote.value)

\* Types of the state variables.
\* --------------------------------------------------------------
TypeInvariant ==
    /\ Voted \in [MCAcceptor -> SUBSET [ballot : MCBallot, value : MCValue]]
    /\ Threshold \in [MCAcceptor -> Int]

Inv == /\ TypeInvariant
       /\ AllVotesSafe
       /\ OneValuePerBallot

\* --------------------------------------------------------------
\* Action: an acceptor raises its promise threshold (without voting)
\* --------------------------------------------------------------
Promise ==
    \E a \in MCAcceptor :
      \E t \in Int :
        /\ t > Threshold[a]
        /\ Voted' = Voted
        /\ Threshold' = [Threshold EXCEPT ![a] = t]

\* --------------------------------------------------------------
\* Action: an acceptor votes for value v in ballot b
\* --------------------------------------------------------------
Vote ==
    \E a \in MCAcceptor :
      \E b \in MCBallot :
        \E v \in MCValue :
          /\ b >= Threshold[a]               \* cannot vote below promise
          /\ \A vote \in Voted[a] : vote.ballot # b   \* not already voted in b
          /\ SafeAt(b, v)                    \* safety condition
          /\ \A a2 \in MCAcceptor :
                \A vote2 \in Voted[a2] :
                  (vote2.ballot = b) => vote2.value = v   \* at most one value per ballot
          /\ Voted' = [Voted EXCEPT ![a] = Voted[a] \cup {<<b, v>>}]
          /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next == \/ Promise \/ Vote

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_<<Voted, Threshold>>

\* --------------------------------------------------------------
\* Consensus safety property: at most one value can be chosen.
\* A value is chosen when some quorum has all its members voting
\* for that value in the same ballot.
\* --------------------------------------------------------------
Chosen(v) ==
    \E b \in MCBallot :
      \E Q \in MCQuorum :
        /\ Q \subseteq MCAcceptor
        /\ \A a \in Q :
             \E vote \in Voted[a] :
               /\ vote.ballot = b
               /\ vote.value = v

ConsensusSpecBar ==
    \A v1, v2 \in MCValue :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* --------------------------------------------------------------
\* Symmetry definition: all permutations of the acceptor set.
\* --------------------------------------------------------------
MCSymmetry ==
    { f \in [MCAcceptor -> MCAcceptor] :
        /\ \A a1, a2 \in MCAcceptor : f[a1] = f[a2] => a1 = a2
        /\ \A a \in MCAcceptor : f[a] \in MCAcceptor }

====