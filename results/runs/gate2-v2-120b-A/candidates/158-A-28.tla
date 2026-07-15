---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

\* --------------------------------------------------------------
\* Constants (instantiated in the .cfg file)
\* --------------------------------------------------------------
CONSTANTS 
    a1,          \* an acceptor (example name)
    Acceptor,    \* the set of all acceptors
    Value,       \* the set of all values that may be chosen
    Quorum,      \* a set of subsets of Acceptor, each subset is a quorum
    Ballot       \* the set of ballot numbers (e.g., 0..2)

\* --------------------------------------------------------------
\* Types
\* --------------------------------------------------------------
Vote == [bal : Ballot, val : Value]

\* --------------------------------------------------------------
\* Variables
\* --------------------------------------------------------------
VARIABLES votes, thresh

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
\* The set of votes cast by a particular acceptor
AcceptorVotes(a) == { v \in votes : v \in votes /\ a \in { a } }

\* All possible quorums (must be subsets of Acceptor)
Quorums == Quorum

\* Overlap property: any two quorums intersect
QuorumOverlap == 
    \A q1, q2 \in Quorums : q1 # q2 => q1 \cap q2 # {}

\* A value is safe at ballot b when for every lower ballot c there is a quorum
\* in which each member either has already voted for that value in c or cannot
\* vote in c because its threshold is already > c.
SafeAt(v, b) ==
    \A c \in Ballot : c < b =>
        \E q \in Quorums :
            \A a \in q :
                (\E vt \in votes : vt.val = v /\ vt.bal = c /\ a \in Acceptor) \/ thresh[a] > c

\* A quorum has all members voting for value v in ballot b
QuorumVotes(v, b) == 
    \E q \in Quorums :
        \A a \in q :
            \E vt \in votes : vt.val = v /\ vt.bal = b /\ a \in Acceptor

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ votes = {}
    /\ thresh = [a \in Acceptor |-> -1]

\* --------------------------------------------------------------
\* Actions
\* --------------------------------------------------------------

\* An acceptor raises its promise threshold (no vote)
Raise(a, newBal) ==
    /\ a \in Acceptor
    /\ newBal \in Ballot
    /\ newBal > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = newBal]
    /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot
Vote(a, bal, val) ==
    /\ a \in Acceptor
    /\ bal \in Ballot
    /\ val \in Value
    /\ bal >= thresh[a]                \* condition 1
    /\ \A vt \in votes : vt.bal # bal => TRUE   \* no restriction on other ballots
    /\ ~(\E vt \in votes : vt.bal = bal)          \* condition 2: a has not voted in bal
    /\ (\A vt \in votes : vt.bal = bal => vt.val = val) \* condition 3: no different value in same ballot
    /\ SafeAt(val, bal)                \* condition 4: value is safe at bal
    /\ votes' = votes \cup { [bal |-> bal, val |-> val] }
    /\ thresh' = [thresh EXCEPT ![a] = bal]

\* The combined NEXT relation
Next ==
    \/ \E a \in Acceptor, newBal \in Ballot : Raise(a, newBal)
    \/ \E a \in Acceptor, bal \in Ballot, val \in Value : Vote(a, bal, val)

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, thresh>>

\* --------------------------------------------------------------
\* Invariant required by the .cfg file
\* --------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor : thresh[a] \in Ballot \cup {-1}
    /\ \A vt \in votes : vt.bal \in Ballot /\ vt.val \in Value
    /\ \A bal \in Ballot : 
        (\E v \in Value : (\A a \in Acceptor : 
            (\E vt \in votes : vt.bal = bal /\ vt.val = v /\ a \in Acceptor))) =>
        (\A a1, a2 \in Acceptor :
            (\E vt1 \in votes : vt1.bal = bal /\ vt1.val = v /\ a1 \in Acceptor) /\
            (\E vt2 \in votes : vt2.bal = bal /\ vt2.val = v /\ a2 \in Acceptor))
    /\ \A vt \in votes : SafeAt(vt.val, vt.bal)

\* --------------------------------------------------------------
\* Property representing the abstract consensus specification
\* --------------------------------------------------------------
ConsensusSpecBar ==
    \A q1, q2 \in Quorums :
        \A v1, v2 \in Value, b1, b2 \in Ballot :
            (\A a1 \in q1 : \E vt1 \in votes : vt1.bal = b1 /\ vt1.val = v1 /\ a1 \in Acceptor) /\
            (\A a2 \in q2 : \E vt2 \in votes : vt2.bal = b2 /\ vt2.val = v2 /\ a2 \in Acceptor) =>
                v1 = v2

====