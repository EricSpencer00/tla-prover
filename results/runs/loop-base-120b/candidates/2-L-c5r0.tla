---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ---------------------------------------------------------------------- *)
(*  Sets derived from the constants                                         *)
VoteValues      == {yes, no}
DecisionValues  == {commit, abort}
ForwardStatus   == {notsent, commit, abort}
PreDecisionVals == {undecided} \cup DecisionValues
ParticipantDec  == {undecided, commit, abort}

(* ---------------------------------------------------------------------- *)
VARIABLES
  coordAlive, coordFaulty, coordDecision,
  pAlive, pFaulty, pVoteSent, pVote, pPreDec, pForward, pDecided

vars == <<coordAlive, coordFaulty, coordDecision,
          pAlive, pFaulty, pVoteSent, pVote, pPreDec, pForward, pDecided>>

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                          *)
Init ==
  /\ coordAlive   = TRUE
  /\ coordFaulty  = FALSE
  /\ coordDecision = undecided
  /\ pAlive   = [p \in participants |-> TRUE]
  /\ pFaulty  = [p \in participants |-> FALSE]
  /\ pVoteSent= [p \in participants |-> FALSE]
  /\ pVote    = [p \in participants |-> undecided]
  /\ pPreDec  = [p \in participants |-> undecided]
  /\ pForward = [p \in participants |-> [q \in participants |-> notsent]]
  /\ pDecided = [p \in participants |-> undecided]

(* ---------------------------------------------------------------------- *)
(*  Coordinator actions                                                    *)

CoordCrash ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ coordAlive'  = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<coordDecision, pAlive, pFaulty, pVoteSent,
                pVote, pPreDec, pForward, pDecided>>

CoordDecide ==
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE
  /\ \A p \in participants : pVoteSent[p] = TRUE
  /\ decision = IF \A p \in participants : pVote[p] = yes
               THEN commit ELSE abort
  /\ coordDecision' = decision
  /\ UNCHANGED <<coordAlive, coordFaulty, pAlive, pFaulty,
                pVoteSent, pVote, pPreDec, pForward, pDecided>>

(* ---------------------------------------------------------------------- *)
(*  Participant actions                                                    *)

SendVote(p) ==
  /\ pAlive[p] = TRUE
  /\ pFaulty[p] = FALSE
  /\ pVoteSent[p] = FALSE
  /\ vote \in VoteValues
  /\ pVoteSent' = [pVoteSent EXCEPT ![p] = TRUE]
  /\ pVote'    = [pVote EXCEPT    ![p] = vote]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pPreDec, pForward, pDecided>>

PreDecFromCoord(p) ==
  /\ pAlive[p] = TRUE
  /\ pFaulty[p] = FALSE
  /\ pPreDec[p] = undecided
  /\ coordAlive = TRUE
  /\ coordDecision \in DecisionValues
  /\ pPreDec' = [pPreDec EXCEPT ![p] = coordDecision]
  /\ pForward' = [pForward EXCEPT ![p][p] = coordDecision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pVoteSent, pVote, pDecided>>

PreDecFromForward(p) ==
  /\ pAlive[p] = TRUE
  /\ pFaulty[p] = FALSE
  /\ pPreDec[p] = undecided
  /\ \E q \in participants :
        q # p /\ pForward[q][p] \in DecisionValues
  /\ decision = CHOOSE d \in DecisionValues :
        \E q \in participants : q # p /\ pForward[q][p] = d
  /\ pPreDec' = [pPreDec EXCEPT ![p] = decision]
  /\ pForward' = [pForward EXCEPT ![p][p] = decision]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pVoteSent, pVote, pDecided>>

Forward(p,q) ==
  /\ pAlive[p] = TRUE
  /\ pFaulty[p] = FALSE
  /\ pPreDec[p] \in DecisionValues
  /\ pForward[p][q] = notsent
  /\ pForward' = [pForward EXCEPT ![p][q] = pPreDec[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pVoteSent, pVote,
                pPreDec, pDecided>>

Decide(p) ==
  /\ pAlive[p] = TRUE
  /\ pFaulty[p] = FALSE
  /\ pPreDec[p] \in DecisionValues
  /\ \A q \in participants : pForward[p][q] # notsent
  /\ pDecided' = [pDecided EXCEPT ![p] = pPreDec[p]]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pVoteSent, pVote,
                pPreDec, pForward>>

AbortOnTimeout(p) ==
  /\ pAlive[p] = TRUE
  /\ pFaulty[p] = FALSE
  /\ pDecided[p] = undecided
  /\ coordAlive = FALSE
  /\ \A r \in participants : pPreDec[r] = undecided
  /\ pDecided' = [pDecided EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pAlive, pFaulty, pVoteSent, pVote,
                pPreDec, pForward>>

ParticipantCrash(p) ==
  /\ pAlive[p] = TRUE
  /\ pAlive'   = [pAlive EXCEPT ![p] = FALSE]
  /\ pFaulty'  = [pFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                pVoteSent, pVote, pPreDec, pForward, pDecided>>

(* ---------------------------------------------------------------------- *)
(*  Next-state relation                                                    *)

Next ==
  \/ CoordCrash
  \/ CoordDecide
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : PreDecFromCoord(p)
  \/ \E p \in participants : PreDecFromForward(p)
  \/ \E p \in participants : \E q \in participants : Forward(p,q)
  \/ \E p \in participants : Decide(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : ParticipantCrash(p)

(* ---------------------------------------------------------------------- *)
(*  Fairness assumptions (weak fairness, excluding death)                 *)

Fairness ==
  /\ WF_vars(CoordDecide)
  /\ \A p \in participants : WF_vars(SendVote(p))
  /\ \A p \in participants : WF_vars(PreDecFromCoord(p))
  /\ \A p \in participants : WF_vars(PreDecFromForward(p))
  /\ \A p \in participants : \A q \in participants : WF_vars(Forward(p,q))
  /\ \A p \in participants : WF_vars(Decide(p))
  /\ \A p \in participants : WF_vars(AbortOnTimeout(p))

(* ---------------------------------------------------------------------- *)
(*  Specification                                                          *)

SpecNB == Init /\ [][Next]_vars /\ Fairness

(* ---------------------------------------------------------------------- *)
(*  Type invariant                                                         *)

TypeInvNB ==
  /\ coordAlive   \in BOOLEAN
  /\ coordFaulty  \in BOOLEAN
  /\ coordDecision \in PreDecisionVals
  /\ pAlive   \in [participants -> BOOLEAN]
  /\ pFaulty  \in [participants -> BOOLEAN]
  /\ pVoteSent\in [participants -> BOOLEAN]
  /\ pVote    \in [participants -> VoteValues \cup {undecided}]
  /\ pPreDec  \in [participants -> PreDecisionVals]
  /\ pForward \in [participants -> [participants -> ForwardStatus]]
  /\ pDecided \in [participants -> ParticipantDec]

====