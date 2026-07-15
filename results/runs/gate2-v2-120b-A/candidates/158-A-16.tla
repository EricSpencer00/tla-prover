---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                       *)
(***************************************************************************)
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

VARIABLES votes, prom

\* votes[ a ] is the set of pairs <<b, v>> that acceptor a has cast
\* prom[ a ] is the current promise threshold of acceptor a
vars == <<votes, prom>>

(***************************************************************************)
(*  Type OK (not the main invariant but useful for readability)          *)
(***************************************************************************)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET {<<Ballot, Value>>}]
    /\ prom \in [Acceptor -> Ballot]

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)

\* SafeAt(b,v) : value v is safe at ballot b
SafeAt(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    (<<c, v>> \in votes[a]) \/ (prom[a] > c)

\* A quorum votes for value v in ballot b
QuorumVotes(b, v) ==
    \E q \in Quorum :
        \A a \in q : <<b, v>> \in votes[a]

\* A value is chosen if some quorum voted for it in some ballot
Chosen == { v \in Value : \E b \in Ballot : QuorumVotes(b, v) }

(***************************************************************************)
(*  Actions                                                              *)
(***************************************************************************)

\* An acceptor raises its promise threshold (no vote)
RaisePromise ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > prom[a]
        /\ prom' = [prom EXCEPT ![a] = b]
        /\ UNCHANGED votes

\* An acceptor casts a vote for value v in ballot b
Vote ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= prom[a]                     \* not below current promise
        /\ <<b, v>> \notin votes[a]         \* hasn't voted in this ballot yet
        /\ \A a2 \in Acceptor :
               (\E v2 \in Value : <<b, v2>> \in votes[a2]) => v2 = v
        /\ SafeAt(b, v)                     \* safety condition
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
        /\ prom'  = [prom  EXCEPT ![a] = b]

Next == Vote \/ RaisePromise

(***************************************************************************)
(*  Specification (temporal formula)                                     *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Invariant required by the cfg file                                    *)
(***************************************************************************)
Inv == 
    /\ TypeOK
    /\ \A a \in Acceptor, <<b, v>> \in votes[a] : SafeAt(b, v)
    /\ \A b \in Ballot :
          (\E v \in Value : \E q \in Quorum : \A a \in q : <<b, v>> \in votes[a]) =>
          (\A v2 \in Value :
               (\E q \in Quorum : \A a \in q : <<b, v2>> \in votes[a]) => v2 = v))

(***************************************************************************)
(*  Property that the invariant implies, named in the cfg file           *)
(***************************************************************************)
ConsensusSpecBar == Inv

=============================================================================