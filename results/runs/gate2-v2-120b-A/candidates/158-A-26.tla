---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Acceptor,   \* Set of acceptor identifiers
    Value,      \* Set of possible values
    Quorum,     \* Set of quorum subsets of Acceptor
    Ballot      \* Set of ballot numbers (naturals)

(*--------------------------------------------------------------------
  Derived concepts
--------------------------------------------------------------------*)
Vars
    votes,          \* [a \in Acceptor -> SUBSET [ballot : Ballot, val : Value]]
    threshold       \* [a \in Acceptor -> Ballot]  (current promise)

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Vote == [ballot : Ballot, val : Value]

VoteSet(a) == votes[a]

(* a quorum is any element of the constant set Quorum *)
Quorums == Quorum

(* Overlap property required by the description; we assert it as an ASSUME *)
ASSUME Overlap ==
    \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Safety predicate: a value v is safe at ballot b
--------------------------------------------------------------------*)
SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorums :
                \A a \in Q :
                    (\E v2 \in Value :
                        <<c, v2>> \in votes[a] /\ v2 = v)
                    \/ (b <= threshold[a])

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
IncreaseThreshold(a, newB) ==
    /\ a \in Acceptor
    /\ newB \in Ballot
    /\ newB > threshold[a]
    /\ UNCHANGED votes
    /\ threshold' = [threshold EXCEPT ![a] = newB]

VoteFor(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]                     \* cannot vote below current promise
    /\ ~(\E v2 \in Value : <<b, v2>> \in votes[a])   \* not already voted in this ballot
    /\ \A a2 \in Acceptor :
          (<<b, v>> \in votes[a2]) => a2 = a      \* at most one value per ballot
    /\ SafeAt(v, b)                          \* value must be safe
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, newB \in Ballot : IncreaseThreshold(a, newB)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<votes, threshold>>

(*--------------------------------------------------------------------
  Invariant required by the .cfg
--------------------------------------------------------------------*)
Inv ==
    /\ \A a \in Acceptor : votes[a] \subseteq [ballot : Ballot, val : Value]
    /\ \A a \in Acceptor :
          \A <<b, v>> \in votes[a] :
               b >= threshold[a]                     \* type‐correctness / monotonicity
    /\ \A b \in Ballot :
          ( \E v \in Value : \E Q \in Quorums :
                \A a \in Q : <<b, v>> \in votes[a] ) =>
          ( \A v2 \in Value, Q2 \in Quorums :
                (\A a \in Q2 : <<b, v2>> \in votes[a]) => v2 = v )  \* at most one value per ballot

(*--------------------------------------------------------------------
  Safety property exposed to the model checker
--------------------------------------------------------------------*)
ConsensusSpecBar ==
    \A Q1, Q2 \in Quorums, b1, b2 \in Ballot, v1, v2 \in Value :
        ( \A a \in Q1 : <<b1, v1>> \in votes[a] ) /\ 
        ( \A a \in Q2 : <<b2, v2>> \in votes[a] ) => v1 = v2

=============================================================================