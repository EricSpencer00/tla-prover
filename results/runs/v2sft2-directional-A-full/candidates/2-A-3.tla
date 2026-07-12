---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants \* set of participant identifiers, e.g., {1,2,3,4}

\* Values used for votes and decisions
\* vote values
yes, no, undecided \* vote states
\* decision values
commit, abort \* commit or abort decisions

\* statuses for forwarding
waiting, notsent \* waiting for a forward, notsent means not yet forwarded

\* ----------------------------------------------------------------------
\* Type definition (for clarity, not required by TLC)
\* ----------------------------------------------------------------------
VoteVal == {yes, no, undecided}
DecisionVal == {commit, abort}
ForwardStatus == {waiting, notsent}
\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    #\* Coordinator's view
    votes,              \* [p \in participants -> VoteVal]
    dec,                \* DecisionVal or NULL (no decision yet)
    aliveC,             \* BOOLEAN: is coordinator alive
    faultyC,            \* BOOLEAN: is coordinator faulty
    \* Participants' views
    Pvotes,             \* [p \in participants -> VoteVal]
    Pdec,               \* [p \in participants -> DecisionVal \cup {undecided}]
    aliveP,             \* [p \in participants -> BOOLEAN]
    faultyP,            \* [p \in participants -> BOOLEAN]
    Prequest,           \* [p \in participants -> BOOLEAN] \* true if request has been sent
    \* Forwarding table for each participant
    fwd,                \* [p1 \in participants -> [p2 \in participants -> ForwardStatus]]
    \* Auxiliary (for internal logic, not part of invariants)
    pendingRequests \* set of participants that have pending requests (used for timeouts)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsDecisionSet == "dec \in {commit, abort}"
IsPdecSet(p) == "Pdec[p] \in {commit, abort}"
AllForwarded(p) == "(\A q \in participants : fwd[p][q] = waiting) \/ (fwd[p][q] = commit) \/ (fwd[p][q] = abort)"
\* ----------------------------------------------------------------------
\* Initial state (must match ACP-SB initial state with added fwd initialization)
\* ----------------------------------------------------------------------
Init ==
    /\ dec = NULL
    /\ votes = [p \in participants |-> undecided]
    /\ dec = NULL
    /\ aliveC = TRUE
    /\ faultyC = FALSE
    /\ Pvotes = [p \in participants |-> undecided]
    /\ Pdec = [p \in participants |-> undecided]
    /\ aliveP = [p \in participants |-> TRUE]
    /\ faultyP = [p \in participants |-> FALSE]
    /\ Prequest = [p \in participants |-> FALSE]
    /\ fwd = [p1 \in participants |-> [p2 \in participants |-> notsent]]
    /\ pendingRequests = {}

\* ----------------------------------------------------------------------
\* Coordinator actions (inherited from ACP-SB)
\* ----------------------------------------------------------------------
SendReq ==
    /\ aliveC
    /\ \A p \in participants : aliveP[p]
    /\ Prequest' = [p \in participants |-> TRUE]
    /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

RecvVote ==
    /\ aliveC
    /\ \E p \in participants : aliveP[p] /\ votes[p] = undecided
    /\ LET v == Pvotes[p] IN
        /\ votes' = [votes EXCEPT ![p] = v]
        /\ UNCHANGED << dec, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

DetectFault ==
    /\ aliveC
    /\ (\E p \in participants : aliveP[p] /\ faultyP[p])
    /\ faultyC' = TRUE
    /\ UNCHANGED << votes, dec, aliveC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

MakeDecision ==
    /\ aliveC
    /\ (\E p \in participants : Pvotes[p] = no)
        \/ (\E p \in participants : faultyP[p])
    /\ dec' = abort
    /\ UNCHANGED << votes, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

MakeDecision2 ==
    /\ aliveC
    /\ (\A p \in participants : Pvotes[p] = yes)
    /\ dec' = commit
    /\ UNCHANGED << votes, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

Broadcast ==
    /\ aliveC
    /\ dec \in {commit, abort}
    /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

DieC ==
    /\ aliveC
    /\ aliveC' = FALSE
    /\ faultyC' = TRUE
    /\ UNCHANGED << votes, dec, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
SendVote ==
    /\ \E p \in participants : aliveP[p] /\ Pvotes[p] = undecided
    /\ LET p == CHOOSE p \in participants : aliveP[p] /\ Pvotes[p] = undecided IN
        /\ Pvotes' = [Pvotes EXCEPT ![p] = yes]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pdec, aliveP, faultyP, fwd, pendingRequests >>

AbortVote ==
    /\ \E p \in participants : aliveP[p] /\ Pvotes[p] = undecided
    /\ LET p == CHOOSE p \in participants : aliveP[p] /\ Pvotes[p] = undecided IN
        /\ Pvotes' = [Pvotes EXCEPT ![p] = no]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pdec, aliveP, faultyP, fwd, pendingRequests >>

AbortDecision ==
    /\ \E p \in participants : aliveP[p] /\ Pdec[p] = undecided
    /\ LET p == CHOOSE p \in participants : aliveP[p] /\ Pdec[p] = undecided IN
        /\ Pdec' = [Pdec EXCEPT ![p] = abort]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, aliveP, faultyP, fwd, pendingRequests >>

PreDecFromC ==
    /\ aliveC
    /\ dec \in {commit, abort}
    /\ \E p \in participants : aliveP[p] /\ Pdec[p] = undecided
    /\ LET p == CHOOSE p \in participants : aliveP[p] /\ Pdec[p] = undecided IN
        /\ Pdec' = [Pdec EXCEPT ![p] = dec]
        /\ fwd' = [fwd EXCEPT ![p][p] = dec]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, aliveP, faultyP, pendingRequests >>

PreDecFromFwd ==
    /\ \E p1, p2 \in participants :
           aliveP[p1] /\ aliveP[p2] /\ p1 # p2
           /\ fwd[p2][p1] = undecided
           /\ fwd[p1][p2] \in {commit, abort}
    /\ LET p1' == CHOOSE p1 \in participants : aliveP[p1] /\ \E p2 \in participants : aliveP[p2] /\ p1 # p2 /\ fwd[p2][p1] = undecided /\ fwd[p1][p2] \in {commit, abort} IN
        LET p2' == CHOOSE p2 \in participants : aliveP[p2] /\ p2 # p1' /\ fwd[p1'][p2] \in {commit, abort} IN
            /\ Pdec' = [Pdec EXCEPT ![p1'] = fwd[p2'][p1']]
            /\ fwd' = [fwd EXCEPT ![p1'][p1'] = fwd[p2'][p1']]
            /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, aliveP, faultyP, pendingRequests >>

Forward ==
    /\ \E p1, p2 \in participants :
           aliveP[p1] /\ aliveP[p2] /\ p1 # p2
           /\ fwd[p1][p2] = notsent
           /\ fwd[p1][p1] \in {commit, abort}
    /\ LET p1' == CHOOSE p1 \in participants : aliveP[p1] /\ \E p2 \in participants : aliveP[p2] /\ p1 # p2 /\ fwd[p1][p2] = notsent /\ fwd[p1][p1] \in {commit, abort} IN
        LET p2' == CHOOSE p2 \in participants : aliveP[p2] /\ p2 # p1' /\ fwd[p1'][p2] = notsent IN
            /\ fwd' = [fwd EXCEPT ![p1'][p2'] = fwd[p1'][p1']]
            /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, pendingRequests >>

DecideNonBlocking ==
    /\ \E p \in participants :
           aliveP[p]
           /\ Pdec[p] = undecided
           /\ fwd[p][p] \in {commit, abort}
           /\ (\A q \in participants : fwd[p][q] = waiting \/ fwd[p][q] = fwd[p][p])
    /\ LET p' == CHOOSE p \in participants : aliveP[p] /\ Pdec[p] = undecided /\ fwd[p][p] \in {commit, abort} /\ (\A q \in participants : fwd[p][q] = waiting \/ fwd[p][q] = fwd[p][p]) IN
        /\ Pdec' = [Pdec EXCEPT ![p'] = fwd[p'][p']]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, aliveP, faultyP, fwd, pendingRequests >>

AbortOnTimeout ==
    /\ \E p \in participants :
           aliveP[p] /\ Pdec[p] = undecided
           /\ faultyC
           /\ (\A q \in participants : ~aliveP[q] \/ ~Pdec[q] = commit)
           /\ (\A q \in participants : ~aliveP[q] \/ ~Pdec[q] = abort)
    /\ LET p' == CHOOSE p \in participants : aliveP[p] /\ Pdec[p] = undecided /\ faultyC /\ (\A q \in participants : ~aliveP[q] \/ ~Pdec[q] = commit) /\ (\A q \in participants : ~aliveP[q] \/ ~Pdec[q] = abort) IN
        /\ Pdec' = [Pdec EXCEPT ![p'] = abort]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, aliveP, faultyP, fwd, pendingRequests >>

DieP ==
    /\ \E p \in participants : aliveP[p]
    /\ LET p == CHOOSE p \in participants : aliveP[p] IN
        /\ aliveP' = [aliveP EXCEPT ![p] = FALSE]
        /\ faultyP' = [faultyP EXCEPT ![p] = TRUE]
        /\ UNCHANGED << votes, dec, aliveC, faultyC, Pvotes, Pdec, fwd, pendingRequests >>

\* ----------------------------------------------------------------------
\* NEXT relation (union of all actions)
\* ----------------------------------------------------------------------
Next ==
    \/ SendVote
    \/ AbortVote
    \/ AbortDecision
    \/ PreDecFromC
    \/ PreDecFromFwd
    \/ Forward
    \/ DecideNonBlocking
    \/ AbortOnTimeout
    \/ DieP
    \/ SendReq
    \/ RecvVote
    \/ DetectFault
    \/ MakeDecision
    \/ MakeDecision2
    \/ Broadcast
    \/ DieC

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SpecNB == Init /\ [][Next]_<<votes, dec, aliveC, faultyC, Pvotes, Pdec, aliveP, faultyP, fwd, pendingRequests>>

\* ----------------------------------------------------------------------
\* Safety invariant (TypeInvNB) – ensures all variables remain within their domains
\* ----------------------------------------------------------------------
TypeInvNB ==
    /\ votes \in [participants -> VoteVal]
    /\ dec \in {commit, abort} \cup {NULL}
    /\ aliveC \in BOOLEAN
    /\ faultyC \in BOOLEAN
    /\ Pvotes \in [participants -> VoteVal]
    /\ Pdec \in [participants -> DecisionVal \cup {undecided}]
    /\ aliveP \in [participants -> BOOLEAN]
    /\ faultyP \in [participants -> BOOLEAN]
    /\ fwd \in [participants -> [participants -> ForwardStatus]]
    /\ pendingRequests \subseteq participants

=============================================================================