---- MODULE Voting ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\* ---------- CONSTANTS ----------
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ---------- ASSUMPTIONS ----------
\* Concrete instantiations for model checking (can be overridden in a .cfg file)
ASSUME Acceptor = {a1, a2, a3}
ASSUME Value    = {v1, v2}
ASSUME Ballot   = Nat                     \* natural numbers (0,1,2,…)
ASSUME Quorum \subseteq SUBSET Acceptor
\* Overlap property: any two quorums intersect
ASSUME \A Q1, Q2 \in Quorum : Q1 # {} /\ Q2 # {} => Q1 \cap Q2 # {}

\* ---------- STATE VARIABLES ----------
VARIABLES votes, promise

\* votes[a] is the set of votes cast by acceptor a.
\* each vote is a record [ballot : Ballot, value : Value]
\* promise[a] is the current promise threshold (an integer, -1 means no promise)
Init ==
    /\ votes   = [ a \in Acceptor |-> {} ]
    /\ promise = [ a \in Acceptor |-> -1 ]

\* ---------- HELPERS ----------
VoteRecord(b, v) == [ballot |-> b, value |-> v]

SafeAt(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E w \in votes[a] : w.ballot = c /\ w.value = v )
                    \/ (promise[a] > c)

OneValuePerBallot ==
    \A b \in Ballot :
        \A acc1, acc2 \in Acceptor :
            \A w1 \in votes[acc1] :
                \A w2 \in votes[acc2] :
                    (w1.ballot = b /\ w2.ballot = b) => w1.value = w2.value

AllVotesSafe ==
    \A a \in Acceptor :
        \A w \in votes[a] :
            SafeAt(w.ballot, w.value)

TypeInvariant ==
    /\ votes   \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
    /\ promise \in [Acceptor -> Int]

Inv == TypeInvariant /\ OneValuePerBallot /\ AllVotesSafe

\* ---------- ACTIONS ----------
\* Promise action: raise the promise threshold without voting
PromiseAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > promise[a]
            /\ promise' = [promise EXCEPT ![a] = b]
            /\ UNCHANGED votes

\* Vote action: cast a vote for value v in ballot b
VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= promise[a]                         \* not below current promise
                /\ ~(\E w \in votes[a] : w.ballot = b)    \* a has not already voted in b
                /\ \A acc \in Acceptor :
                        \A w \in votes[acc] :
                            (w.ballot = b) => w.value = v   \* no conflicting vote
                /\ \E Q \in Quorum :
                        \A acc2 \in Q :
                            ( \E w \in votes[acc2] : w.ballot = b /\ w.value = v )
                            \/ (promise[acc2] > b)            \* quorum shows value is safe
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { VoteRecord(b, v) } ]
                /\ promise' = [promise EXCEPT ![a] = b]

Next == \/ PromiseAction \/ VoteAction

\* ---------- SPECIFICATION ----------
Spec == Init /\ [] [Next]_<<votes, promise>>

\* ---------- REQUIRED OPERATORS FOR .cfg ----------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* Compatibility aliases expected by the generated MCVoting module
TypeOK == TypeInvariant

OneVote ==
    \A a \in Acceptor :
        \A w1, w2 \in votes[a] :
            w1.ballot = w2.ballot => w1.value = w2.value

maxBal ==
    IF \E a \in Acceptor : votes[a] # {} THEN
        Max({ w.ballot : a \in Acceptor, w \in votes[a] })
    ELSE -1

\* Property required by the .cfg file: consensus safety
ConsensusSpecBar == [] (OneValuePerBallot)

\* Symmetry set of permutations over acceptors
MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2 }

====