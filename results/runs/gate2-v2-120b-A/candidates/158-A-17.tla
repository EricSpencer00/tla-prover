---- MODULE Voting ----
EXTENDS Naturals, TLC

(* ---------- Constants ---------- *)
CONSTANTS
    Acceptor,   \* Set of acceptor identifiers
    Value,      \* Set of possible proposal values
    Quorum,     \* Set of quorums, each quorum is a subset of Acceptor
    Ballot      \* Set of ballot numbers (natural numbers)

(* ---------- Types ---------- *)
Vote == [ bal : Ballot, val : Value ]

(* ---------- State variables ---------- *)
VARIABLES
    votes,      \* [a \in Acceptor -> SUBSET Vote]  : votes cast by each acceptor
    thresh      \* [a \in Acceptor -> Ballot]       : promise threshold per acceptor

(* ---------- Helper definitions ---------- *)

AcceptorVotes == [a \in Acceptor |-> votes[a]]
Thresh == [a \in Acceptor |-> thresh[a]]

(* A quorum that contains only acceptors that have either voted (bal,val) or are
   guaranteed never to vote in that ballot (i.e., their threshold already exceeds bal). *)
QuorumFor(bal, val) ==
    { q \in Quorum :
        \A a \in q :
            (<<bal, val>> \in votes[a]) \/ (thresh[a] > bal) }

(* A value is safe at ballot bal if for every lower ballot c there exists a quorum
   that guarantees the value at c. *)
SafeAt(val, bal) ==
    \A c \in Ballot :
        (c < bal) => \E q \in Quorum :
            \A a \in q :
                (<<c, val>> \in votes[a]) \/ (thresh[a] > c)

(* A quorum of acceptors have all voted for (bal,val). *)
ChosenQuorum(bal, val) ==
    \E q \in Quorum : \A a \in q : <<bal, val>> \in votes[a]

(* ---------- Initial state ---------- *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* ---------- Actions ---------- *)

(* An acceptor may raise its promise threshold without voting *)
Promise(a, newBal) ==
    /\ a \in Acceptor
    /\ newBal \in Ballot
    /\ newBal > thresh[a]
    /\ votes' = votes
    /\ thresh' = [thresh EXCEPT ![a] = newBal]

(* An acceptor votes for a value in a ballot, satisfying safety and quorum conditions *)
VoteAction(a, bal, val) ==
    /\ a \in Acceptor
    /\ bal \in Ballot
    /\ val \in Value
    /\ bal >= thresh[a]                     \* not below current promise
    /\ \A v \in votes[a] : v.bal # bal      \* hasn't voted in this ballot before
    /\ \A a2 \in Acceptor :
          ~(\E v \in votes[a2] :
               v.bal = bal /\ v.val # val) \* no other acceptor voted different value in same ballot
    /\ SafeAt(val, bal)                     \* the value is safe at this ballot
    /\ \E q \in Quorum :                    \* there exists a quorum demonstrating safety
          \A a2 \in q :
              (<<bal, val>> \in votes[a2]) \/ (thresh[a2] > bal)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<bal, val>>}]
    /\ thresh' = [thresh EXCEPT ![a] = bal]

(* The overall next-state relation *)
Next ==
    \/ \E a \in Acceptor, newBal \in Ballot : Promise(a, newBal)
    \/ \E a \in Acceptor, bal \in Ballot, val \in Value : VoteAction(a, bal, val)

(* ---------- Specification ---------- *)

Spec == Init /\ [][Next]_<<votes, thresh>>

(* ---------- Invariant ---------- *)

Inv ==
    /\ \A a \in Acceptor : votes[a] \subseteq Vote
    /\ \A a \in Acceptor : thresh[a] \in Ballot
    /\ \A a \in Acceptor : \A v \in votes[a] :
          (v.bal >= thresh[a]) /\ SafeAt(v.val, v.bal)
    /\ \A bal \in Ballot :
          \A a1, a2 \in Acceptor :
            (\E v1 \in votes[a1] : v1.bal = bal) /\ (\E v2 \in votes[a2] : v2.bal = bal) =>
                (\E v1 \in votes[a1] : v1.bal = bal) .val = (\E v2 \in votes[a2] : v2.bal = bal).val

(* ---------- Safety property (consensus) ---------- *)

ConsensusSpecBar ==
    \A bal1, bal2 \in Ballot, val1, val2 \in Value :
        (ChosenQuorum(bal1, val1) /\ ChosenQuorum(bal2, val2)) => val1 = val2

====