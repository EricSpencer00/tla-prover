---- MODULE 16_consensus_forall ----
\* benchmark: pyv-consensus-forall

EXTENDS TLAPS, Naturals, TLC, FiniteSetTheorems


CONSTANT Node,Value,Quorum

VARIABLE vote_request_msg
VARIABLE voted
VARIABLE vote_msg
VARIABLE votes
VARIABLE leader
VARIABLE voting_quorum
VARIABLE decided

vars == <<vote_request_msg,voted,vote_msg,votes,leader,voting_quorum,decided>>

SendRequestVote(i,j) == 
    /\ vote_request_msg' = vote_request_msg \cup {<<i,j>>}
    /\ UNCHANGED <<voted, vote_msg, votes, leader, voting_quorum,decided>>

SendVote(src,dst)==
    /\ ~voted[src]
    /\ <<dst,src>> \in vote_request_msg
    /\ vote_msg' = vote_msg \cup {<<src,dst>>}
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ UNCHANGED <<vote_request_msg, votes, leader, voting_quorum,decided>>

RecvVote(i,sender)==
    /\ <<sender,i>> \in vote_msg
    /\ votes' = votes \cup {<<i,sender>>}
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, leader, voting_quorum,decided>>

ChooseVotingQuorum(i) ==
    \E Q \in Quorum :
    /\ \A v \in Q : <<i,v>> \in votes
    /\ voting_quorum' = Q
    /\ UNCHANGED <<vote_request_msg, vote_msg, votes, voted, leader,decided>>

BecomeLeader(i) == 
    /\ voting_quorum # {}
    /\ \A v \in voting_quorum : <<i,v>> \in votes
    /\ leader' = [leader EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, voting_quorum,decided>>

Decide(i,v) ==
    /\ leader[i]
    /\ \A vx \in Value : <<i,vx>> \notin decided
    /\ decided' = decided \cup {<<i,v>>}
    /\ UNCHANGED <<vote_request_msg, vote_msg, voted, votes, leader, voting_quorum>>

Init == 
    /\ vote_request_msg = {}
    /\ voted = [s \in Node |-> FALSE]
    /\ vote_msg = {}
    /\ votes = {}
    /\ leader = [s \in Node |-> FALSE]
    /\ voting_quorum \in Quorum
    /\ decided = {}

SendRequestVoteAction == \E i,j \in Node : SendRequestVote(i,j)
SendVoteAction == \E i,j \in Node : SendVote(i,j)
RecvVoteAction == \E i,j \in Node : RecvVote(i,j)
ChooseVotingQuorumAction == \E i \in Node : ChooseVotingQuorum(i)
BecomeLeaderAction == \E i \in Node : BecomeLeader(i)
DecideAction == \E i \in Node, v \in Value : Decide(i, v)

Next == 
    \/ SendRequestVoteAction
    \/ SendVoteAction
    \/ RecvVoteAction
    \/ ChooseVotingQuorumAction
    \/ BecomeLeaderAction
    \/ DecideAction

TypeOK == 
    /\ vote_request_msg \in SUBSET (Node \X Node)
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in SUBSET (Node \X Node)
    /\ votes \in SUBSET (Node \X Node)
    /\ leader \in [Node -> BOOLEAN]
    /\ voting_quorum \in Quorum
    /\ decided \in SUBSET (Node \X Value)

\* TypeOKRandom ==
\*     /\ vote_request_msg \in RandomSubset(15, SUBSET (Node \X Node))
\*     /\ voted \in RandomSubset(5, [Node -> BOOLEAN])
\*     /\ vote_msg \in RandomSubset(15, SUBSET (Node \X Node))
\*     /\ votes \in RandomSubset(15, SUBSET (Node \X Node))
\*     /\ leader \in RandomSubset(5, [Node -> BOOLEAN])
\*     /\ voting_quorum \in RandomSubset(5, Quorum)
\*     /\ decided \in RandomSubset(15, SUBSET (Node \X Value))

Safety == 
    \A n1,n2 \in Node : \A v1,v2 \in Value : 
        (<<n1,v1>> \in decided /\ <<n2,v2>> \in decided) => (v1=v2)

NoLeader == ~\E i \in Node : leader[i]

Symmetry == Permutations(Node) \cup Permutations(Value)

NextUnchanged == UNCHANGED vars

\* Inductive strengthening conjuncts
Inv358_1_0_def == \A VARI \in Node : \A VARJ \in Node : (<<VARJ,VARI>> \in vote_msg) \/ (~(<<VARI,VARJ>> \in votes))
Inv119_1_1_def == \A VARI \in Node : \A VARJ \in Node : (<<VARI,VARJ>> \in vote_request_msg) \/ (~(<<VARJ,VARI>> \in vote_msg))
Inv759_1_2_def == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(<<VARI,VARJ>> \in vote_msg))
Inv680_1_3_def == \A VARI \in Node : \A VALI \in Value : (leader[VARI]) \/ (~(<<VARI,VALI>> \in decided))
Inv7155_2_4_def == \A VARJ \in Node : \A VARK \in Node : (VARJ=VARK) \/ (~(leader[VARJ]) \/ (~(leader[VARK])))
Inv7039_2_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARJ=VARK) \/ (~(<<VARI,VARJ>> \in vote_msg) \/ (~(<<VARI,VARK>> \in vote_msg)))
Inv2245_2_1_def == \A VARI \in Node : \A VARJ \in Node : (<<VARI,VARJ>> \in votes) \/ (~(leader[VARI])) \/ (~(VARJ \in voting_quorum))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv358_1_0_def
  /\ Inv119_1_1_def
  /\ Inv759_1_2_def
  /\ Inv680_1_3_def
  /\ Inv7155_2_4_def
  /\ Inv7039_2_0_def
  /\ Inv2245_2_1_def

  
AXIOM QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
AXIOM EmptyNotInQuorums == {} \notin Quorum \* because quorums are majority sets
AXIOM QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
AXIOM Fin == IsFiniteSet(Node)



THEOREM Inductiveness == IndAuto /\ Next => IndAuto'
BY SMT, SetExtensionality
====