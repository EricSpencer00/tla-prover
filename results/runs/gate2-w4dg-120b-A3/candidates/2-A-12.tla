---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Extends the simple broadcast protocol ACP_SB; this module redefines the
\* full spec to include the reliable broadcast forwarding table per participant.
\* An entry is the pre-decision a participant has received; forward entries are
\* what distinguishes this from the base protocol.

VARIABLES coord, up, decision, faulty, voteSent, fwd, decider

vars == <<coord, up, decision, faulty, voteSent, fwd, decider>>

TypeInvNB ==
  /\ coord \in [req : participants \cup {undecided}, vote : participants \cup {yes, no, undecided},
                 broadcast : participants \cup {undecided}, decision : {undecided, commit, abort},
                 alive : BOOLEAN, faulty : BOOLEAN]
  /\ up \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
  /\ coord = [req |-> undecided, vote |-> undecided, broadcast |-> undecided,
              decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]
  /\ up = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

\* Coordinator actions: exactly those of the base spec (renamed here).
SendReq ==
  /\ coord.alive /\ coord.req = undecided
  /\ \E c \in participants : coord' = [coord EXCEPT !.req = c]
  /\ UNCHANGED <<up, decision, faulty, voteSent, fwd>>

GetVote ==
  /\ coord.alive /\ coord.req # undecided /\ coord.vote = undecided
  /\ up[coord.req]
  /\ ~voteSent[coord.req]
  /\ \E v \in {yes, no} : coord' = [coord EXCEPT !.vote = v]
  /\ voteSent' = [voteSent EXCEPT ![coord.req] = TRUE]
  /\ UNCHANGED <<up, decision, faulty, fwd>>

DetectFault ==
  /\ coord.alive /\ coord.vote = undecided
  /\ coord.faulty
  /\ coord' = [coord EXCEPT !.faulty = TRUE]
  /\ UNCHANGED <<up, decision, faulty, voteSent, fwd>>

MakeDecision ==
  /\ coord.alive /\ coord.vote # undecided /\ coord.decision = undecided
  /\ coord' = [coord EXCEPT !.decision = IF coord.vote = yes THEN commit ELSE abort]
  /\ UNCHANGED <<up, decision, faulty, voteSent, fwd>>

Broadcast ==
  /\ coord.alive /\ coord.decision # undecided /\ coord.broadcast = undecided
  /\ \E p \in participants : coord' = [coord EXCEPT !.broadcast = p]
  /\ UNCHANGED <<up, decision, faulty, voteSent, fwd>>

CoordinatorDie ==
  /\ coord.alive /\ ~coord.faulty
  /\ coord' = [coord EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<up, decision, faulty, voteSent, fwd>>

\* Participant actions: the base ones plus the reliable-broadcast steps.
SendVoteNB ==
  /\ decider = undecided
  /\ \E c \in participants :
       /\ up[c]
       /\ ~voteSent[c]
       /\ decider' = c
  /\ UNCHANGED <<coord, up, decision, faulty, voteSent, fwd>>

AbortNB ==
  /\ decider # undecided
  /\ voteSent[decider]
  /\ coord.vote = no
  /\ decision' = [decision EXCEPT ![decider] = abort]
  /\ UNCHANGED <<coord, up, faulty, voteSent, fwd>>

PredecideFromCoord ==
  /\ up[coord.broadcast]
  /\ fwd[coord.broadcast][coord.broadcast] = notsent
  /\ fwd' = [fwd EXCEPT ![coord.broadcast][coord.broadcast] = coord.decision]
  /\ UNCHANGED <<coord, up, decision, faulty, voteSent>>

PredecideFromFwd ==
  /\ \E p \in participants :
       /\ up[p]
       /\ fwd[p][p] = notsent
       /\ \E q \in participants :
            /\ q # p
            /\ fwd[q][p] # notsent
            /\ fwd' = [fwd EXCEPT ![p][p] = @[q]]
  /\ UNCHANGED <<coord, up, decision, faulty, voteSent>>

\* A participant must forward its pre-decision to *everyone* else before it may
\* finalize locally -- this is what backs non-blocking termination.
Forward ==
  /\ \E p \in participants :
       /\ up[p]
       /\ fwd[p][p] # notsent
       /\ \E q \in participants :
            /\ q # p
            /\ fwd[p][q] = notsent
            /\ fwd' = [fwd EXCEPT ![p][q] = fwd[p][p]]
  /\ UNCHANGED <<coord, up, decision, faulty, voteSent>>

DecideNB ==
  /\ \E p \in participants :
       /\ up[p]
       /\ \A q \in participants : q # p => fwd[p][q] = fwd[p][p]
       /\ decision[p] = undecided
       /\ decision' = [decision EXCEPT ![p] = fwd[p][p]]
  /\ UNCHANGED <<coord, up, faulty, voteSent, fwd>>

AbortOnTimeoutNB ==
  /\ coord.faulty = FALSE
  /\ coord.alive = FALSE
  /\ \A p \in participants : fwd[p][p] # notsent
  /\ \A p \in participants : decision[p] = undecided
  /\ \A q \in participants : ~up[q] => \A r \in participants : fwd[r][q] = notsent
  /\ decision' = [p \in participants |-> abort]
  /\ UNCHANGED <<coord, up, faulty, voteSent, fwd>>

DieNB ==
  /\ up[decider]
  /\ up' = [up EXCEPT ![decider] = FALSE]
  /\ faulty' = [faulty EXCEPT ![decider] = TRUE]
  /\ UNCHANGED <<coord, decision, voteSent, fwd>>

NextNB ==
  \/ SendReq \/ GetVote \/ DetectFault \/ MakeDecision \/ Broadcast \/ CoordinatorDie
  \/ SendVoteNB \/ AbortNB \/ PredecideFromCoord \/ PredecideFromFwd \/ Forward
  \/ DecideNB \/ AbortOnTimeoutNB \/ DieNB

SpecNB ==
  /\ InitNB
  /\ [][NextNB]_vars
  /\ WF_vars(PredecideFromCoord)
  /\ WF_vars(PredecideFromFwd)
  /\ WF_vars(Forward)
  /\ WF_vars(DecideNB)
  /\ WF_vars(SendVoteNB)

\* Safety: agreement, commit/abort validity, irrevocability.
Agreement ==
  \A p, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE

CommitValidity ==
  (decision[CHOOSE p \in participants : TRUE] = commit) => \A p \in participants : voteSent[p] = TRUE

AbortValidity ==
  (decision[CHOOSE p \in participants : TRUE] = abort) =>
    \/ \E p \in participants : voteSent[p] = FALSE
    \/ \E p \in participants : faulty[p] = TRUE
    \/ coord.faulty

Irrevocability ==
  \A p \in participants : (decision[p] # undecided) ~> (decision[p] # undecided)

\* Liveness: the non-blocking guarantee, plus the base termination condition.
Termination ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty[p] = TRUE \/ coord.faulty)

NonBlockingTermination ==
  \A p \in participants : (up[p] /\ decision[p] = undecided) ~> (decision[p] # undecided)

PROPERTIES == Termination /\ NonBlockingTermination

====