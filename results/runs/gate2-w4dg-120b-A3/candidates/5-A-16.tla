---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  alive, faulty, decision, vote, sentVote, asked, recvVote, sent

vars == <<alive, faulty, decision, vote, sentVote, asked, recvVote, sent>>

TypeInv ==
  /\ alive \in [participants \cup {"coordinator"} -> BOOLEAN]
  /\ faulty \in [participants \cup {"coordinator"} -> BOOLEAN]
  /\ decision \in [participants \cup {"coordinator"} -> {undecided, commit, abort}]
  /\ vote \in [participants -> {yes, no}]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ asked \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ sent \in [participants -> {notsent, commit, abort}]

Init ==
  /\ alive = [p \in participants \cup {"coordinator"} |-> TRUE]
  /\ faulty = [p \in participants \cup {"coordinator"} |-> FALSE]
  /\ decision = [p \in participants \cup {"coordinator"} |-> undecided]
  /\ vote = [p \in participants |-> IF CHOOSE b \in {TRUE, FALSE} : TRUE THEN yes ELSE no]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ asked = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ sent = [p \in participants |-> notsent]

CoordinatorSendsRequest(p) ==
  /\ alive["coordinator"]
  /\ ~asked[p]
  /\ asked' = [asked EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, faulty, decision, vote, sentVote, recvVote, sent>>

CoordinatorReceivesVote(p) ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] = undecided
  /\ asked[p]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<alive, faulty, decision, vote, sentVote, asked, sent>>

CoordinatorDetectsFault(p) ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] = undecided
  /\ asked[p]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ decision' = [decision EXCEPT !["coordinator"] = abort]
  /\ UNCHANGED <<alive, faulty, vote, sentVote, asked, recvVote, sent>>

CoordinatorDecides ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] = undecided
  /\ \A p \in participants : recvVote[p] # waiting
  /\ decision' = [decision EXCEPT !["coordinator"] =
        IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED <<alive, faulty, vote, sentVote, asked, recvVote, sent>>

CoordinatorBroadcast(p) ==
  /\ alive["coordinator"]
  /\ decision["coordinator"] # undecided
  /\ sent[p] = notsent
  /\ sent' = [sent EXCEPT ![p] = decision["coordinator"]]
  /\ UNCHANGED <<alive, faulty, decision, vote, sentVote, asked, recvVote>>

CoordinatorDies ==
  /\ alive["coordinator"]
  /\ alive' = [alive EXCEPT !["coordinator"] = FALSE]
  /\ faulty' = [faulty EXCEPT !["coordinator"] = TRUE]
  /\ UNCHANGED <<decision, vote, sentVote, asked, recvVote, sent>>

ParticipantSendsVote(p) ==
  /\ alive[p]
  /\ asked[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<alive, faulty, decision, vote, asked, recvVote, sent>>

ParticipantAbortsOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, faulty, vote, sentVote, asked, recvVote, sent>>

ParticipantAbortsOnNoRequest(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~asked[p]
  /\ ~alive["coordinator"]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<alive, faulty, vote, sentVote, asked, recvVote, sent>>

ParticipantDecidesFromCoordinator(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sent[p]]
  /\ UNCHANGED <<alive, faulty, vote, sentVote, asked, recvVote, sent>>

ParticipantDies(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<decision, vote, sentVote, asked, recvVote, sent>>

Next ==
  \/ \E p \in participants : CoordinatorSendsRequest(p)
  \/ \E p \in participants : CoordinatorReceivesVote(p)
  \/ \E p \in participants : CoordinatorDetectsFault(p)
  \/ CoordinatorDecides
  \/ \E p \in participants : CoordinatorBroadcast(p)
  \/ CoordinatorDies
  \/ \E p \in participants : ParticipantSendsVote(p)
  \/ \E p \in participants : ParticipantAbortsOnNo(p)
  \/ \E p \in participants : ParticipantAbortsOnNoRequest(p)
  \/ \E p \in participants : ParticipantDecidesFromCoordinator(p)
  \/ \E p \in participants : ParticipantDies(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(ParticipantSendsVote(p) \/ ParticipantAbortsOnNo(p) \/ ParticipantAbortsOnNoRequest(p) \/ ParticipantDecidesFromCoordinator(p))
  /\ \A p \in participants : SF_vars(CoordinatorSendsRequest(p) \/ CoordinatorReceivesVote(p) \/ CoordinatorDetectsFault(p) \/ CoordinatorBroadcast(p))

CommitAgreement ==
  \A p, q \in participants : ~(decision[p] = commit /\ decision[q] = abort)

CommitValid ==
  \A p, q \in participants :
    decision[p] = commit => vote[q] = yes

AbortValid ==
  \A p, q \in participants :
    decision[p] = abort => \/ \E r \in participants : vote[r] = no
                           \/ \E r \in participants : ~alive[r]
                           \/ ~alive["coordinator"]

Irreversible ==
  \A p \in participants :
    /\ (decision[p] = commit => decision[p] = commit)
    /\ (decision[p] = abort => decision[p] = abort)

SomeParticipantDecided == \E p \in participants : decision[p] # undecided

DecisionOrFailure ==
  (SomeParticipantDecided \/ \E p \in participants : ~alive[p])
    \/ ~alive["coordinator"]

====