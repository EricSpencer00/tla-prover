---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*-----------------------------------------------------------------
  Concrete interpretations for the constants (used by the model)
-----------------------------------------------------------------*)
ASSUME Acceptor = {a1, a2, a3}
ASSUME Value    = {v1, v2}
ASSUME Ballot   = Nat \* natural numbers (0,1,2,...)

(*-----------------------------------------------------------------
  Operators required by the .cfg substitutions
-----------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES Votes, Prom   \* Prom is the promise threshold

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
TypeInvariant ==
  /\ Votes \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
  /\ Prom  \in [Acceptor -> Int]      \* we allow -1 as initial value

(*-----------------------------------------------------------------
  Safety of a vote
-----------------------------------------------------------------*)
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          ( \E w \in Votes[a] : w.ballot = c /\ w.value = v )
          \/ (Prom[a] > c)          \* cannot vote in ballot c any more

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Prom  = [a \in Acceptor |-> -1]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Promise ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > Prom[a]
    /\ Prom' = [Prom EXCEPT ![a] = b]
    /\ UNCHANGED Votes

Vote ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= Prom[a]                                          \* respect promise
    /\ ~(\E w \in Votes[a] : w.ballot = b)                  \* not already voted in b
    /\ \A a2 \in Acceptor :
         \A w2 \in Votes[a2] :
           (w2.ballot = b) => (w2.value = v)                \* at most one value per ballot
    /\ Safe(v, b)                                            \* value is safe
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup
                              { [ballot |-> b, value |-> v] } ]
    /\ Prom'  = [Prom EXCEPT ![a] = b]
    /\ UNCHANGED <<>>

Next == \/ Promise \/ Vote

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Votes, Prom>>

(*-----------------------------------------------------------------
  Invariant
-----------------------------------------------------------------*)
Inv ==
  /\ TypeInvariant
  /\ \A a \in Acceptor, w \in Votes[a] :
        Safe(w.value, w.ballot)
  /\ \A b \in Ballot :
        (\E v \in Value : \E a \in Acceptor : [ballot |-> b, value |-> v] \in Votes[a])
        => (\A a1, a2 \in Acceptor :
               (\E w1 \in Votes[a1] : w1.ballot = b) /\ (\E w2 \in Votes[a2] : w2.ballot = b)
               => (\A w1 \in Votes[a1] : \A w2 \in Votes[a2] :
                       (w1.ballot = b /\ w2.ballot = b) => w1.value = w2.value))
  /\ \A Q1 \in Quorum, Q2 \in Quorum : Q1 \cap Q2 # {}

(*-----------------------------------------------------------------
  Consistency property (at most one chosen value)
-----------------------------------------------------------------*)
Chosen(v) ==
  \E Q \in Quorum, b \in Ballot :
     \A a \in Q :
        \E w \in Votes[a] : w.ballot = b /\ w.value = v

ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(*-----------------------------------------------------------------
  Symmetry for model checking
-----------------------------------------------------------------*)
MCSymmetry ==
  { f \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2   \* injective
        /\ \A a \in Acceptor : \E a0 \in Acceptor : f[a0] = a  \* surjective
  }

=============================================================================