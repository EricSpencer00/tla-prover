---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordAlive, coordFaulty, coordDecision, votes,
          pAlive, pFaulty, pVote, pDecision, pVoteSent, pForward

(* ------------------------------------------------------------------------- *)
(* Type invariant                                                             *)
(* ------------------------------------------------------------------------- *)
TypeInvNB ==
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN
  /\ coordDecision \in {commit, abort, waiting}
  /\ votes \in [participants -> {yes, no, undecided}]
  /\ pAlive \in [participants -> BOOLEAN]
  /\ pFaulty \in [participants -> BOOLEAN]
  /\ pVote \in [participants -> {yes, no, undecided}]
  /\ pDecision \in [participants -> {commit, abort, undecided}]
  /\ pVoteSent \in [participants -> BOOLEAN]
  /\ pForward \in [participants -> [participants -> {notsent, commit, abort}]]

(* ------------------------------------------------------------------------- *)
(* Initial state                                                             *)
(* ------------------------------------------------------------------------- *)
Init ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordDecision = waiting
  /\ votes = [p \in participants |-> undecided]
  /\ pAlive = [p \in participants |-> TRUE]
  /\ pFaulty = [p \in participants |-> FALSE]
  /\ pVote = [p \in participants |-> undecided]
  /\ pDecision = [p \in participants |-> undecided]
  /\ pVoteSent = [p \in participants |-> FALSE]
  /\ pForward = [p \in participants |-> [q \in participants |-> notsent]]

(* ------------------------------------------------------------------------- *)
(* Participant sends its vote to the coordinator                              *)
(* ------------------------------------------------------------------------- *)
VoteSend(p) ==
  /\ p \in participants
  /\ pAlive[p] = TRUE
  /\ pVoteSent[p] = FALSE
  /\ pVote[p] \in {yes, no}
  /\ pVoteSent' = [pVoteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pAlive, pFaulty, pDecision, pForward>>

(* ------------------------------------------------------------------------- *)
(* Coordinator receives a vote                                                *)
(* ------------------------------------------------------------------------- *)
CoordReceiveVote(p) ==
  /\ p \in participants
  /\ pAlive[p] = TRUE
  /\ pVote[p] \in {yes, no}
  /\ votes' = [votes EXCEPT ![p] = pVote[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pVote, pDecision, pVoteSent, pForward>>

(* ------------------------------------------------------------------------- *)
(* Coordinator decides when all votes are known                               *)
(* ------------------------------------------------------------------------- *)
MakeDecision ==
  /\ coordAlive = TRUE
  /\ coordDecision = waiting
  /\ \A p \in participants: votes[p] # undecided
  /\ IF \A p \in participants: votes[p] = yes
        THEN coordDecision' = commit
        ELSE coordDecision' = abort
  /\ UNCHANGED <<coordAlive, coordFaulty, votes,
                pAlive, pFaulty, pVote, pDecision, pVoteSent, pForward>>

(* ------------------------------------------------------------------------- *)
(* Participant obtains pre‑decision directly from coordinator                 *)
(* ------------------------------------------------------------------------- *)
PreDecideFromCoord(p) ==
  /\ p \in participants
  /\ pAlive[p] = TRUE
  /\ pForward[p][p] = notsent
  /\ coordDecision \in {commit, abort}
  /\ pForward' = [pForward EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pAlive, pFaulty, pVote, pDecision, pVoteSent>>

(* ------------------------------------------------------------------------- *)
(* Participant forwards its pre‑decision to another participant               *)
(* ------------------------------------------------------------------------- *)
Forward(p, q) ==
  /\ p \in participants /\ q \in participants /\ p # q
  /\ pAlive[p] = TRUE /\ pAlive[q] = TRUE
  /\ pForward[p][p] \in {commit, abort}
  /\ pForward[p][q] = notsent
  /\ pForward' = [pForward EXCEPT ![p][q] = pForward[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pAlive, pFaulty, pVote, pDecision, pVoteSent>>

(* ------------------------------------------------------------------------- *)
(* Participant receives a forwarded pre‑decision                              *)
(* ------------------------------------------------------------------------- *)
PreDecideFromForward(q, p) ==
  /\ q \in participants /\ p \in participants /\ q # p
  /\ pAlive[p] = TRUE
  /\ pForward[p][p] = notsent
  /\ pForward[q][p] \in {commit, abort}
  /\ pForward' = [pForward EXCEPT ![p][p] = pForward[q][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pAlive, pFaulty, pVote, pDecision, pVoteSent>>

(* ------------------------------------------------------------------------- *)
(* Participant decides after forwarding to everybody                         *)
(* ------------------------------------------------------------------------- *)
Decide(p) ==
  /\ p \in participants
  /\ pAlive[p] = TRUE
  /\ pForward[p][p] \in {commit, abort}
  /\ \A q \in participants: q # p => pForward[p][q] # notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = pForward[p][p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pAlive, pFaulty, pVote, pVoteSent, pForward>>

(* ------------------------------------------------------------------------- *)
(* Abort on timeout when the coordinator is dead and no decision is present  *)
(* ------------------------------------------------------------------------- *)
AbortOnTimeout(p) ==
  /\ p \in participants
  /\ pAlive[p] = TRUE
  /\ pDecision[p] = undecided
  /\ coordAlive = FALSE
  /\ \A a \in participants: pAlive[a] => pForward[a][a] = notsent
  /\ \A d \in participants: (pAlive[d] = FALSE) =>
        \A a \in participants: pAlive[a] = TRUE => pForward[d][a] = notsent
  /\ pDecision' = [pDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pAlive, pFaulty, pVote, pVoteSent, pForward>>

(* ------------------------------------------------------------------------- *)
(* Crash actions                                                             *)
(* ------------------------------------------------------------------------- *)
CoordDie ==
  /\ coordAlive = TRUE
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, votes,
                pAlive, pFaulty, pVote, pDecision, pVoteSent, pForward>>

ParticipantDie(p) ==
  /\ p \in participants
  /\ pAlive[p] = TRUE
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                pVote, pDecision, pVoteSent, pForward>>

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------- *)
Next ==
  \/ \E p \in participants: VoteSend(p)
  \/ \E p \in participants: CoordReceiveVote(p)
  \/ MakeDecision
  \/ \E p \in participants: PreDecideFromCoord(p)
  \/ \E p, q \in participants: (p # q) /\ Forward(p, q)
  \/ \E q, p \in participants: (q # p) /\ PreDecideFromForward(q, p)
  \/ \E p \in participants: Decide(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: ParticipantDie(p)
  \/ CoordDie

Vars == <<coordAlive, coordFaulty, coordDecision, votes,
          pAlive, pFaulty, pVote, pDecision, pVoteSent, pForward>>

SpecNB == Init /\ [][Next]_Vars

====