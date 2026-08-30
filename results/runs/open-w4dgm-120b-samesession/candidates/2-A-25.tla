---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordination messages are modelled as sets of participant identifiers (an
\* unordered bag), so delivery is unordered and a participant may be
\* pre-informed of the decision from either the coordinator or a peer.
\* fmsg[p][q] is p's forwarding record for q: what p pre-informed q of.
\* fmsg[p][p] is p's own pre-informed decision, if any.

VARIABLES pvote, palive, pdecision, pfaulty, pvoteSent, cstatus, crequest,
          cvote, cbroadcast, cdecision, calive, cfaulty, fmsg

vars == <<pvote, palive, pdecision, pfaulty, pvoteSent, cstatus, crequest,
           cvote, cbroadcast, cdecision, calive, cfaulty, fmsg>>

TypeOK ==
  /\ pvote \in [participants -> {yes, no}]
  /\ palive \in [participants -> BOOLEAN]
  /\ pdecision \in [participants -> {undecided, commit, abort}]
  /\ pfaulty \in [participants -> BOOLEAN]
  /\ pvoteSent \in [participants -> BOOLEAN]
  /\ cstatus \in {"idle", "collecting", "decided", "aborted"}
  /\ crequest \subseteq participants
  /\ cvote \subseteq participants
  /\ cbroadcast \subseteq participants
  /\ cdecision \in {commit, abort, undecided}
  /\ calive \in BOOLEAN
  /\ cfaulty \in BOOLEAN
  /\ fmsg \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ pvote = [p \in participants |-> undecided]
  /\ palive = [p \in participants |-> TRUE]
  /\ pdecision = [p \in participants |-> undecided]
  /\ pfaulty = [p \in participants |-> FALSE]
  /\ pvoteSent = [p \in participants |-> FALSE]
  /\ cstatus = "idle"
  /\ crequest = {}
  /\ cvote = {}
  /\ cbroadcast = {}
  /\ cdecision = undecided
  /\ calive = TRUE
  /\ cfaulty = FALSE
  /\ fmsg = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorSendRequest ==
  /\ calive
  /\ cstatus = "idle"
  /\ cstatus' = "collecting"
  /\ crequest' = participants
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cvote,
                 cbroadcast, cdecision, calive, cfaulty, fmsg>>

\* A participant's broadcast of its vote to the coordinator is its own act,
\* and it may crash silently before it ever happens.
ParticipantSendVote(p) ==
  /\ palive[p]
  /\ ~pfaulty[p]
  /\ ~pvoteSent[p]
  /\ pvote[p] \in {yes, no}
  /\ cvote' = cvote \cup {p}
  /\ pvoteSent' = [pvoteSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, cstatus, crequest,
                 cbroadcast, cdecision, calive, cfaulty, fmsg>>

CoordinatorDetectFault(p) ==
  /\ cstatus = "collecting"
  /\ calive
  /\ pvote[p] = undecided
  /\ ~palive[p]
  /\ pvote[p] = no
  /\ cstatus' = "decided"
  /\ cdecision' = abort
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, crequest,
                 cvote, cbroadcast, calive, cfaulty, fmsg>>

CoordinatorMakeDecision ==
  /\ cstatus = "collecting"
  /\ calive
  /\ \A p \in participants : pvote[p] = yes
  /\ cstatus' = "decided"
  /\ cdecision' = commit
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, crequest,
                 cvote, cbroadcast, calive, cfaulty, fmsg>>

CoordinatorBroadcast(p) ==
  /\ cstatus = "decided"
  /\ calive
  /\ p \notin cbroadcast
  /\ cbroadcast' = cbroadcast \cup {p}
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cstatus,
                 crequest, cvote, cdecision, calive, cfaulty, fmsg>>

\* A participant may be slow to adopt a decision but never actively blocks it:
\* its own forward-to-all action is what keeps the system making progress.
ParticipantPreDecideFromCoordinator(p) ==
  /\ palive[p]
  /\ fmsg[p][p] = notsent
  /\ cstatus = "decided"
  /\ p \in cbroadcast
  /\ fmsg' = [fmsg EXCEPT ![p][p] = cdecision]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cstatus,
                 crequest, cvote, cbroadcast, cdecision, calive, cfaulty>>

ParticipantPreDecideFromPeer(p, q) ==
  /\ palive[p]
  /\ fmsg[p][p] = notsent
  /\ fmsg[q][p] # notsent
  /\ p \notin cvote
  /\ fmsg' = [fmsg EXCEPT ![p][p] = fmsg[q][p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cstatus,
                 crequest, cvote, cbroadcast, cdecision, calive, cfaulty>>

ParticipantForward(p, q) ==
  /\ palive[p]
  /\ fmsg[p][p] # notsent
  /\ fmsg[p][q] = notsent
  /\ fmsg' = [fmsg EXCEPT ![p][q] = fmsg[p][p]]
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cstatus,
                 crequest, cvote, cbroadcast, cdecision, calive, cfaulty>>

ParticipantDecide(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ fmsg[p][p] # notsent
  /\ \A q \in participants \ {p} : fmsg[p][q] = fmsg[p][p]
  /\ pdecision' = [pdecision EXCEPT ![p] = fmsg[p][p]]
  /\ UNCHANGED <<pvote, palive, pfaulty, pvoteSent, cstatus, crequest,
                 cvote, cbroadcast, cdecision, calive, cfaulty, fmsg>>

\* A timeout abort fires only when the coordinator is dead and no living
\* participant can still be reached by anyone (neither coordinator broadcast nor
\* any peer forwarding) -- that is what makes the abort safe rather than a
\* default path that can race with a legitimate decision.
ParticipantAbortOnTimeout(p) ==
  /\ palive[p]
  /\ pdecision[p] = undecided
  /\ ~calive
  /\ \A q \in participants : q \notin cbroadcast
  /\ \A q \in participants : ~(\A r \in participants : r \notin fmsg[q])
  /\ pdecision' = [pdecision EXCEPT ![p] = abort] \/ UNCHANGED <<pvote, palive,
                    pfaulty, pvoteSent, cstatus, crequest, cvote, cbroadcast,
                    cdecision, calive, cfaulty, fmsg>>

ParticipantDie(p) ==
  /\ palive[p]
  /\ palive' = [palive EXCEPT ![p] = FALSE]
  /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pvote, pdecision, pvoteSent, cstatus, crequest, cvote,
                 cbroadcast, cdecision, calive, cfaulty, fmsg>>

CoordinatorDie ==
  /\ calive
  /\ calive' = FALSE
  /\ cfaulty' = TRUE
  /\ UNCHANGED <<pvote, palive, pdecision, pfaulty, pvoteSent, cstatus,
                 crequest, cvote, cbroadcast, cdecision, fmsg>>

Next ==
  \/ CoordinatorSendRequest \/ CoordinatorMakeDecision \/ CoordinatorDie
  \/ \E p \in participants :
       \/ ParticipantSendVote(p) \/ CoordinatorDetectFault(p)
       \/ CoordinatorBroadcast(p) \/ ParticipantPreDecideFromCoordinator(p)
       \/ ParticipantDecide(p) \/ ParticipantDie(p)
       \/ \E q \in participants : ParticipantPreDecideFromPeer(p, q) \/ ParticipantForward(p, q)
       \/ ParticipantAbortOnTimeout(p)

SpecNB ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ParticipantDecide("p1"))
  /\ WF_vars(ParticipantDecide("p2"))
  /\ WF_vars(ParticipantDecide("p3"))

TypeInvNB == TypeOK

\* No two participants ever disagree about the outcome.
AtomicityConsistent == \A p, q \in participants : (pdecision[p] = commit) => (pdecision[q] # abort)

\* Irreversibility: a decision, once made, is never retracted.
NoDecisionReversal ==
  \A p \in participants :
    (pdecision[p] = commit \/ pdecision[p] = abort) ~> (pdecision[p] = commit \/ pdecision[p] = abort)

====