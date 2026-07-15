---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ------------------------------------------------------------------------ *)
(* Sets and derived constants *)
(* ------------------------------------------------------------------------ *)

Pids == participants

(* ------------------------------------------------------------------------ *)
(* Variables *)
(* ------------------------------------------------------------------------ *)

VARIABLES
    alive,          \* participants that have not crashed
    faulty,         \* participants that have crashed (may be recovered for reasoning)
    coordAlive,     \* coordinator status: TRUE = alive, FALSE = crashed
    coordFaulty,    \* coordinator faulty flag (TRUE = faulty)
    votes,          \* [pid -> {yes, no}]
    coordDec,       \* coordinator's decision, one of {commit, abort, waiting}
    broadcasted,    \* set of participant ids to which the coordinator has sent its decision
    preDec,         \* [pid -> {commit, abort, undecided}] -- decision received (pre-decision)
    fwdTbl,         \* [pid -> [pid -> {notsent, commit, abort}]] forwarding status
    final,          \* [pid -> {commit, abort, undecided}] final decision
    VoteSent        \* [pid -> BOOLEAN] whether a vote has been sent to the coordinator

(* ------------------------------------------------------------------------ *)
(* Type definitions *)
(* ------------------------------------------------------------------------ *)

Vote == {yes, no}
Decision == {commit, abort, waiting}
PreDecision == {commit, abort, undecided}
FwdStatus == {notsent, commit, abort}
FinalDecision == {commit, abort, undecided}
Bool == BOOLEAN

(* ------------------------------------------------------------------------ *)
(* Helper definitions *)
(* ------------------------------------------------------------------------ *)

AllAlive == { pid \in Pids : alive[pid] }
AllFaulty == { pid \in Pids : faulty[pid] }

(* ------------------------------------------------------------------------ *)
(* Initial state *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ alive = Pids
    /\ faulty = {}
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ votes = [pid \in Pids |-> IF pid \in Pids THEN yes ELSE yes]   \* placeholder; actual votes set by actions
    /\ coordDec = waiting
    /\ broadcasted = {}
    /\ preDec = [pid \in Pids |-> undecided]
    /\ fwdTbl = [pid \in Pids |-> [q \in Pids |-> notsent]]
    /\ final = [pid \in Pids |-> undecided]
    /\ VoteSent = [pid \in Pids |-> FALSE]

(* ------------------------------------------------------------------------ *)
(* Actions *)
(* ------------------------------------------------------------------------ *)

(* Coordinator actions *)

CoordSendRequest ==
    /\ coordAlive
    /\ coordDec = waiting
    /\ \E vs \in [Pids -> Vote] :
        /\ votes' = vs
        /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                       coordDec, broadcasted, preDec, fwdTbl,
                       final, VoteSent>>

CoordCollectVotes ==
    /\ coordAlive
    /\ coordDec = waiting
    /\ \A pid \in Pids : VoteSent[pid]
    /\ \E d \in {commit, abort} :
        /\ coordDec' = d
        /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                       votes, broadcasted, preDec, fwdTbl,
                       final, VoteSent>>

CoordBroadcast ==
    /\ coordAlive
    /\ coordDec \in {commit, abort}
    /\ \E pid \in Pids :
        /\ broadcasted' = broadcasted \cup {pid}
        /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                       votes, coordDec, preDec, fwdTbl,
                       final, VoteSent>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<alive, faulty, votes, coordDec,
                   broadcasted, preDec, fwdTbl,
                   final, VoteSent>>

(* Participant actions *)

SendVote ==
    /\ alive[pid]
    /\ \E v \in Vote :
        /\ votes' = [votes EXCEPT ![pid] = v]
        /\ VoteSent' = [VoteSent EXCEPT ![pid] = TRUE]
        /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                       coordDec, broadcasted, preDec, fwdTbl,
                       final>>

PreDecFromCoord ==
    /\ alive[pid]
    /\ preDec[pid] = undecided
    /\ pid \in broadcasted
    /\ preDec' = [preDec EXCEPT ![pid] = coordDec]
    /\ fwdTbl' = [fwdTbl EXCEPT ![pid][pid] = coordDec]
    /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                   votes, coordDec, broadcasted,
                   final, VoteSent>>

PreDecFromFwd ==
    /\ alive[pid]
    /\ preDec[pid] = undecided
    /\ \E src \in Pids :
        /\ src # pid
        /\ src \in alive
        /\ fwdTbl[src][pid] \in {commit, abort}
        /\ preDec' = [preDec EXCEPT ![pid] = fwdTbl[src][pid]]
        /\ fwdTbl' = [fwdTbl EXCEPT ![pid][pid] = fwdTbl[src][pid]]
        /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                       votes, coordDec, broadcasted,
                       final, VoteSent>>

Forward ==
    /\ alive[pid]
    /\ preDec[pid] \in {commit, abort}
    /\ \E q \in Pids :
        /\ q # pid
        /\ fwdTbl[pid][q] = notsent
        /\ fwdTbl' = [fwdTbl EXCEPT ![pid][q] = preDec[pid]]
        /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                       votes, coordDec, broadcasted,
                       preDec, final, VoteSent>>

Decide ==
    /\ alive[pid]
    /\ preDec[pid] \in {commit, abort}
    /\ \A q \in Pids : q # pid => fwdTbl[pid][q] = preDec[pid]
    /\ final' = [final EXCEPT ![pid] = preDec[pid]]
    /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                   votes, coordDec, broadcasted,
                   preDec, fwdTbl, VoteSent>>

AbortOnTimeout ==
    /\ alive[pid]
    /\ final[pid] = undecided
    /\ ~coordAlive
    /\ \A q \in Pids : q \notin broadcasted
    /\ \A src \in Pids :
        IF src \in faulty THEN
            \A dst \in Pids : fwdTbl[src][dst] = notsent
        ELSE TRUE
    /\ final' = [final EXCEPT ![pid] = abort]
    /\ UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
                   votes, coordDec, broadcasted,
                   preDec, fwdTbl, VoteSent>>

ParticipantDie ==
    /\ alive[pid]
    /\ alive' = alive \ {pid}
    /\ faulty' = faulty \cup {pid}
    /\ UNCHANGED <<coordAlive, coordFaulty, votes,
                   coordDec, broadcasted,
                   preDec, fwdTbl, final, VoteSent>>

(* Stuttering step to avoid deadlock when no action is enabled *)
Idle ==
    UNCHANGED <<alive, faulty, coordAlive, coordFaulty,
               votes, coordDec, broadcasted,
               preDec, fwdTbl, final, VoteSent>>

(* ------------------------------------------------------------------------ *)
(* Next-state relation *)
(* ------------------------------------------------------------------------ *)

Next ==
    \/ \E pid \in Pids : SendVote(pid)
    \/ \E pid \in Pids : PreDecFromCoord(pid)
    \/ \E pid \in Pids : PreDecFromFwd(pid)
    \/ \E pid \in Pids : Forward(pid)
    \/ \E pid \in Pids : Decide(pid)
    \/ \E pid \in Pids : AbortOnTimeout(pid)
    \/ \E pid \in Pids : ParticipantDie(pid)
    \/ CoordSendRequest
    \/ CoordCollectVotes
    \/ CoordBroadcast
    \/ CoordDie
    \/ Idle

(* ------------------------------------------------------------------------ *)
(* Specification *)
(* ------------------------------------------------------------------------ *)

SpecNB == Init /\ [][Next]_<<alive, faulty, coordAlive, coordFaulty,
                            votes, coordDec, broadcasted,
                            preDec, fwdTbl, final, VoteSent>>

(* ------------------------------------------------------------------------ *)
(* Safety invariants *)
(* ------------------------------------------------------------------------ *)

(* Type correctness *)
TypeInvNB ==
    /\ alive \subseteq Pids
    /\ faulty = Pids \ alive
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ votes \in [Pids -> Vote]
    /\ coordDec \in Decision
    /\ broadcasted \subseteq Pids
    /\ preDec \in [Pids -> PreDecision]
    /\ fwdTbl \in [Pids -> [Pids -> FwdStatus]]
    /\ final \in [Pids -> FinalDecision]
    /\ VoteSent \in [Pids -> BOOLEAN]

(* Agreement: no mixed commit/abort among participants *)
AC1 ==
    \A p, q \in Pids :
        (final[p] = commit) => (final[q] # abort)

(* Commit validity *)
AC2 ==
    \A p \in Pids :
        (final[p] = commit) => \A q \in Pids : votes[q] = yes

(* Abort validity *)
AC3 ==
    \A p \in Pids :
        (final[p] = abort) =>
            \/ \E q \in Pids : votes[q] = no
            \/ \E q \in Pids : faulty[q]
            \/ coordFaulty

(* Irrevocability *)
AC4 ==
    \A p \in Pids :
        (final[p] = commit) => [][final[p] = commit]_final
    /\ (final[p] = abort) => [][final[p] = abort]_final

(* ------------------------------------------------------------------------ *)
(* Liveness properties (not used as invariants but kept for completeness) *)
(* ------------------------------------------------------------------------ *)

Liveness1 == <> (\A p \in Pids : final[p] # undecided \/ coordFaulty \/ \E q \in Pids : faulty[q])
Liveness2 == \A p \in Pids : <> (final[p] # undecided)

(* ------------------------------------------------------------------------ *)
(* Theorems (optional) *)
(* ------------------------------------------------------------------------ *)

THEOREM SpecImpliesTypeInv == SpecNB => []TypeInvNB

====