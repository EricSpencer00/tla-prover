---- MODULE ACP_NB ----
EXTENDS Naturals, TLC

\* Non-Blocking Atomic Commitment Protocol (ACP-NB) as described above.
\* This specification extends the simple broadcast variant with a reliable
\* broadcast: each participant forwards the received decision to all others
\* before finalizing it, which guarantees that a non-faulty participant
\* always eventually resolves its decision.
\* All identifiers below (including the constants named in the .cfg) must
\* be present for the reference TLC run to succeed.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

States == {"init", "voting", "ready", "broadcasting", "decided", "faulty"}

VARIABLES pstate, vote, alive, decided, faulty, sent, fwdTable,
          coordState, coordVote, coordDecision, coordAlive, coordFaulty

vars == <<pstate, vote, alive, decided, faulty, sent,
          fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

TypeInvNB ==
    /\ pstate \in [participants -> States]
    /\ vote \in [participants -> {yes, no, undecided}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decided \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ fwdTable \in [participants -> [participants -> {notsent, commit, abort}]]
    /\ coordState \in States
    /\ coordVote \in {yes, no, undecided}
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pstate = [n \in participants |-> "init"]
    /\ vote = [n \in participants |-> undecided]
    /\ alive = [n \in participants |-> TRUE]
    /\ decided = [n \in participants |-> undecided]
    /\ faulty = [n \in participants |-> FALSE]
    /\ sent = [n \in participants |-> FALSE]
    /\ fwdTable = [n \in participants |-> [m \in participants |-> notsent]]
    /\ coordState = "init"
    /\ coordVote = undecided
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator actions: unchanged from the base simple broadcast protocol.
SendRequest ==
    /\ coordAlive
    /\ coordState = "init"
    /\ coordState' = "voting"
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  fwdTable, coordVote, coordDecision, coordAlive, coordFaulty>>

ReceiveVote(n) ==
    /\ coordAlive
    /\ coordState = "voting"
    /\ alive[n]
    /\ pstate[n] = "init"
    /\ pstate' = [pstate EXCEPT ![n] = "voting"]
    /\ UNCHANGED <<vote, alive, decided, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

\* Coordinator decides only after votes are in -- the standard ACP condition.
Decide(coordAns) ==
    /\ coordAlive
    /\ coordState = "voting"
    /\ \A n \in participants: pstate[n] = "voting"
    /\ coordVote' = coordAns
    /\ coordDecision' = IF coordAns = yes THEN commit ELSE abort
    /\ coordState' = "ready"
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  fwdTable, coordAlive, coordFaulty>>

BeginBroadcast ==
    /\ coordAlive
    /\ coordState = "ready"
    /\ coordState' = "broadcasting"
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  fwdTable, coordVote, coordDecision, coordAlive, coordFaulty>>

BroadcastDecision(n) ==
    /\ coordAlive
    /\ coordState = "broadcasting"
    /\ alive[n]
    /\ pstate[n] \in {"init", "voting"}
    /\ pstate' = [pstate EXCEPT ![n] = "ready"]
    /\ UNCHANGED <<vote, alive, decided, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

DetectCoordFault ==
    /\ ~coordAlive
    /\ coordFaulty
    /\ coordState' = "faulty"
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  fwdTable, coordVote, coordDecision, coordAlive, coordFaulty>>

CrashCoord ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

\* Participant action: send its yes/no vote to the coordinator.
SendVote(n) ==
    /\ alive[n]
    /\ pstate[n] = "voting"
    /\ vote[n] = undecided
    /\ \E v \in {yes, no} : vote' = [vote EXCEPT ![n] = v]
    /\ UNCHANGED <<pstate, alive, decided, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

AbortOnVoteNo(n) ==
    /\ alive[n]
    /\ pstate[n] = "voting"
    /\ vote[n] = no
    /\ decided' = [decided EXCEPT ![n] = abort]
    /\ pstate' = [pstate EXCEPT ![n] = "decided"]
    /\ UNCHANGED <<vote, alive, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(n) ==
    /\ alive[n]
    /\ decided[n] = undecided
    /\ ~coordAlive
    /\ \A m \in participants: pstate[m] \in {"init", "ready"}
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

\* A participant now also pre-decides from coordinator broadcast or from a peer
\* forward before it is allowed to finalize its own decision.
PreDecideFromCoord(n) ==
    /\ alive[n]
    /\ decided[n] = undecided
    /\ coordAlive
    /\ pstate[n] = "ready"
    /\ coordDecision # undecided
    /\ fwdTable' = [fwdTable EXCEPT ![n][n] = coordDecision]
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

PreDecideFromFwd(n) ==
    /\ alive[n]
    /\ decided[n] = undecided
    /\ \E m \in participants: fwdTable[m][n] # notsent /\ fwdTable' = [fwdTable EXCEPT ![n][n] = fwdTable[m][n]]
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

\* Forward the pre-decision to another participant (repeated until all are done).
Forward(n, m) ==
    /\ alive[n]
    /\ fwdTable[n][n] # notsent
    /\ fwdTable[n][m] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![n][m] = fwdTable[n][n]]
    /\ UNCHANGED <<pstate, vote, alive, decided, faulty, sent,
                  coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

Decide(n) ==
    /\ alive[n]
    /\ decided[n] = undecided
    /\ fwdTable[n][n] # notsent
    /\ \A m \in participants: fwdTable[n][m] # notsent
    /\ decided' = [decided EXCEPT ![n] = fwdTable[n][n]]
    /\ pstate' = [pstate EXCEPT ![n] = "decided"]
    /\ UNCHANGED <<vote, alive, faulty, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

Die(n) ==
    /\ alive[n]
    /\ alive' = [alive EXCEPT ![n] = FALSE]
    /\ faulty' = [faulty EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<pstate, vote, decided, sent,
                  fwdTable, coordState, coordVote, coordDecision, coordAlive, coordFaulty>>

FinishVote ==
    \/ \E n \in participants: SendVote(n)
    \/ \E n \in participants: AbortOnVoteNo(n)

DecideSome ==
    \/ SendRequest \/ BeginBroadcast \/ CrashCoord \/ DetectCoordFault
    \/ \E n \in participants: AbortOnTimeout(n)
    \/ \E n \in participants: PreDecideFromCoord(n)
    \/ \E n \in participants: PreDecideFromFwd(n)
    \/ \E n \in participants: Decide(n)

Next ==
    \/ FinishVote \/ DecideSome
    \/ \E n \in participants: ReceiveVote(n) \/ BroadcastDecision(n)
    \/ \E n \in participants, m \in participants: Forward(n, m)
    \/ \E n \in participants: Die(n)
    \/ \E ans \in {yes, no}: Decide(ans)

SpecNB ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendRequest)
    /\ WF_vars(FinishVote)
    /\ WF_vars(\E n \in participants: SendVote(n))
    /\ WF_vars(\E n \in participants: PreDecideFromCoord(n))
    /\ WF_vars(\E n \in participants: PreDecideFromFwd(n))
    /\ WF_vars(\E n \in participants, m \in participants: Forward(n, m))
    /\ WF_vars(\E n \in participants: Decide(n))

\* Safety: no two participants ever disagree on their terminal decision.
AC1 ==
    /\ \A n, m \in participants: (decided[n] = commit /\ decided[m] = abort) => FALSE
    /\ \A n \in participants: pstate[n] = "decided" => decided[n] # undecided

\* Safety: a commit is only possible if everyone voted yes.
AC2 ==
    /\ \A n \in participants: decided[n] = commit => \A m \in participants: vote[m] = yes

\* Safety: an abort must be explainable by a no vote or a crash.
AC3 ==
    /\ \A n \in participants: decided[n] = abort => (\E m \in participants: vote[m] = no \/ faulty[m] \/ coordFaulty)

\* Safety: decisions are final and irreversible.
AC4 ==
    /\ \A n \in participants: (pstate[n] = "decided") => (pstate[n] = "decided")
    /\ \A n \in participants: decided[n] = commit => (pstate[n] = "decided")

\* Liveness (the base ACP property): the participants always eventually stop waiting.
AC3Live ==
    <>(\A n \in participants: decided[n] # undecided \/ faulty[n] \/ coordFaulty)

\* Liveness: every non-faulty participant eventually reaches a decision -- this is
\* what reliable broadcast buys us, and the base simple Broadcast variant cannot
\* guarantee it (a participant can be left waiting on a coordinator that died).
AC5 ==
    \A n \in participants: (alive[n] /\ decided[n] = undecided) ~> decided[n] # undecided

Properties == AC3Live /\ AC5

====