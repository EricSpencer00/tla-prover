---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Default interpretations (may be overridden by the .cfg)
Acceptor == {a1, a2, a3}
Value    == {v1, v2}
Quorum   == {{a1, a2}, {a2, a3}, {a1, a3}}   \* every two quorums intersect
Ballot   == Nat

\* Operators used for model‑checking substitutions
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

\*-----------------------------------------------------------------
\* Safety predicate: a value v is safe at ballot b
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vt \in votes[a] : vt.ballot = c /\ vt.value = v )
          \/ (threshold[a] > c)

\*-----------------------------------------------------------------
\* Initial state
Init ==
  /\ votes    = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\*-----------------------------------------------------------------
\* Promise action – raise the threshold of an acceptor
Promise ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\*-----------------------------------------------------------------
\* Vote action – cast a vote for value v in ballot b
Vote ==
  \E a \in Acceptor, v \in Value, b \in Ballot :
    /\ b >= threshold[a]                                   \* not below promise
    /\ \A vt \in votes[a] : vt.ballot # b                  \* not voted in b before
    /\ (\A a2 \in Acceptor :
          \A vt2 \in votes[a2] :
            (vt2.ballot = b) => vt2.value = v)            \* no different value in b
    /\ Safe(v, b)                                          \* value is safe
    /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup
                     { [ballot |-> b, value |-> v] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

\*-----------------------------------------------------------------
Next == \/ Promise \/ Vote

\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\*-----------------------------------------------------------------
\* Type correctness invariant
TypeInv ==
  /\ votes \in [Acceptor -> SUBSET {[ballot: Ballot, value: Value]}]
  /\ threshold \in [Acceptor -> Int]
  /\ \A a \in Acceptor : threshold[a] >= -1

\*-----------------------------------------------------------------
\* Every vote is safe at its ballot
VoteSafety ==
  \A a \in Acceptor :
    \A vt \in votes[a] :
      Safe(vt.value, vt.ballot)

\*-----------------------------------------------------------------
\* At most one value per ballot (across all acceptors)
SingleValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor, vt1 \in votes[a1] :
            vt1.ballot = b /\ vt1.value = v1) /\
        (\E a2 \in Acceptor, vt2 \in votes[a2] :
            vt2.ballot = b /\ vt2.value = v2) )
      => v1 = v2

\*-----------------------------------------------------------------
Inv == /\ TypeInv /\ VoteSafety /\ SingleValuePerBallot

\*-----------------------------------------------------------------
\* Consistency property expressed as a temporal formula
ConsensusSpecBar == []Inv

\*-----------------------------------------------------------------
\* Symmetry set (a single non‑trivial permutation of acceptors)
MCSymmetry ==
  { [a \in Acceptor |-> 
        IF a = a1 THEN a2
        ELSE IF a = a2 THEN a1
        ELSE a ] }

=============================================================================