---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, coordReq, coordVote, coordBC, coordDec, coordAlive, coordFaulty, forwarded

vars == <<vote, alive, decision, faulty, sent, coordReq, coordVote, coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

NoVote == [p \in participants |-> undecided]
NoForward == [p \in participants |-> notsent]

\* Forwarded[p] is the forwarding table for participant p: forwarded decisions
\* sent to every participant it has heard from, plus its own pre-decision.
TypeInvNB ==
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \subseteq participants
    /\ sent \subseteq participants
    /\ coordReq \in {waiting, yes, no}
    /\ coordVote \in {yes, no}
    /\ coordBC \in participants \cup {notsent}
    /\ coordDec \in {commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ forwarded \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ vote = NoVote
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = {}
    /\ sent = {}
    /\ coordReq = waiting
    /\ coordVote = yes
    /\ coordBC = notsent
    /\ coordDec = commit
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ forwarded = [p \in participants |-> NoForward]

\* Coordinator collects votes and decides once all participants have voted.
RequestNB ==
    /\ coordAlive
    /\ coordReq = waiting
    /\ coordReq' = yes
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

GetVoteNB(p) ==
    /\ coordAlive
    /\ coordReq = yes
    /\ alive[p]
    /\ p \notin sent
    /\ vote[p] = undecided
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<vote, alive, decision, faulty, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

DetectFaultNB(p) ==
    /\ coordReq = no
    /\ coordAlive
    /\ alive[p]
    /\ vote[p] = undecided
    /\ vote' = [vote EXCEPT ![p] = no]
    /\ UNCHANGED <<alive, decision, faulty, sent, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

MakeDecisionNB ==
    /\ coordAlive
    /\ coordReq = yes
    /\ \A p \in sent : vote[p] # undecided
    /\ coordVote' = (IF \A p \in participants : vote[p] = yes THEN yes ELSE no)
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq,
                   coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

BroadcastNB ==
    /\ coordAlive
    /\ coordDec = commit
    /\ coordBC = notsent
    /\ \A p \in sent : vote[p] = yes
    /\ coordBC' = (CHOOSE p \in sent : TRUE)
    /\ coordDec' = (IF coordVote = yes THEN commit ELSE abort)
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq,
                   coordVote, coordAlive, coordFaulty, forwarded>>

DieNB ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq,
                   coordVote, coordBC, coordDec, forwarded>>

SendVoteNB(p) == GetVoteNB(p) \/ DetectFaultNB(p)

\* A participant receives the coordinator's broadcast as a pre-decision.
PreDecideCoordNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordBC = p
    /\ forwarded[p][p] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][p] = coordDec]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty>>

\* A participant receives a forwarded pre-decision from another participant.
PreDecideFwdNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forwarded[p][p] = notsent
    /\ \E q \in participants :
         /\ q # p
         /\ forwarded[q][p] # notsent
         /\ forwarded' = [forwarded EXCEPT ![p][p] = forwarded[q][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty>>

\* Forward the pre-decision to another participant that has not yet received it.
ForwardNB(p) ==
    /\ alive[p]
    /\ forwarded[p][p] # notsent
    /\ \E q \in participants :
         /\ q # p
         /\ forwarded[p][q] = notsent
         /\ forwarded' = [forwarded EXCEPT ![p][q] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty>>

\* Once a participant has forwarded everywhere, it finalizes its own decision.
DecideNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ forwarded[p][p] # notsent
    /\ \A q \in participants : q # p => forwarded[p][q] = forwarded[p][p]
    /\ decision' = [decision EXCEPT ![p] = forwarded[p][p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

\* Abort on timeout once no new information can reach an undecided alive
\* participant: the coordinator has died and no alive participant is still
\* awaiting a coordinator broadcast, and no dead participant can still
\* forward a decision to a live participant.
AbortTimeoutNB(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ ~coordAlive
    /\ (\A q \in participants : forwarded[q][p] = notsent)
    /\ (\A q \in participants :
         alive[q] => coordBC # q)
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordReq, coordVote,
                   coordBC, coordDec, coordAlive, coordFaulty, forwarded>>

DiePartNB(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<vote, decision, sent, coordReq, coordVote, coordBC,
                   coordDec, coordAlive, coordFaulty, forwarded>>

CoordinatorNB == RequestNB \/ MakeDecisionNB \/ BroadcastNB \/ DieNB
ParticipantNB(p) == SendVoteNB(p) \/ PreDecideCoordNB(p) \/ PreDecideFwdNB(p)
                    \/ ForwardNB(p) \/ DecideNB(p) \/ AbortTimeoutNB(p) \/ DiePartNB(p)

CrashFirstNB == \/~coordAlive \/ \E p \in participants : ~alive[p]

NextNB ==
    \/ CoordinatorNB
    \/ \E p \in participants : ParticipantNB(p)
    \/ (\E p \in participants : ~alive[p] /\ alive' = [alive EXCEPT ![p] = TRUE])

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(CoordinatorNB)
    /\ (\A p \in participants : WF_vars(ParticipantNB(p)))

\* At most one decision value is adopted system-wide.
AgreementNB == ~(\E p, q \in participants :
    /\ decision[p] = commit
    /\ decision[q] = abort)

ValidCommitNB == (\E p \in participants : decision[p] = commit)
                 => \A q \in participants : vote[q] = yes

ValidAbortNB == (\E p \in participants : decision[p] = abort)
                => \/ \E q \in participants : vote[q] = no
                     \/ faulty # {}
                     \/ coordFaulty

IrreversibleNB == \A p \in participants : (decision[p] = commit \/ decision[p] = abort)
                                         ~> (decision[p] = commit \/ decision[p] = abort)

\* SAFETY: at most one decision value is ever adopted, and it can only be
\* justified by unanimity (commit) or a no vote/crash (abort).
SAFETYINVARIANTNB == AgreementNB /\ ValidCommitNB /\ ValidAbortNB

\* LIVENESS: every participant eventually decides, and the system makes a
\* decision (or crashes) even without the coordinator's broadcast.
TerminationNB == <>(\E p \in participants : decision[p] # undecided \/ coordFaulty)
AC5NB == <>(\A p \in participants : decision[p] # undecided \/ faulty # {})

====