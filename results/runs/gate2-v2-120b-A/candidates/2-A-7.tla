---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg)
--------------------------------------------------------------------*)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ParticipantSet == participants

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Status == {alive, dead}
Vote    == {yes, no}
Dec     == {commit, abort, undecided}
FwdStat == {notsent, commit, abort}
PId     == participants

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    coordAlive,               \* coordinator alive status
    coordFaulty,              \* coordinator faulty flag
    coordDecision,            \* coordinator's decision (undecided, commit, abort)
    votes,                    \* [p \in participants -> Vote \cup {"none"}]
    preDec,                   \* [p \in participants -> {"none", commit, abort}]
    forwarded,                \* [p \in participants -> [q \in participants -> FwdStat]]
    finalDec,                 \* [p \in participants -> Dec]
    faulty                    \* [p \in participants -> BOOLEAN]

(*--------------------------------------------------------------------
  Type invariant (used also as the SpecNB invariant)
--------------------------------------------------------------------*)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {undecided, commit, abort}
    /\ votes \in [participants -> {"none", yes, no}]
    /\ preDec \in [participants -> {"none", commit, abort}]
    /\ forwarded \in [participants -> [participants -> FwdStat]]
    /\ finalDec \in [participants -> Dec]
    /\ faulty \in [participants -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ votes = [p \in participants |-> "none"]
    /\ preDec = [p \in participants |-> "none"]
    /\ forwarded = [p \in participants |-> [q \in participants |-> notsent]]
    /\ finalDec = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]

(*--------------------------------------------------------------------
  Coordinator actions (simplified version from ACP-SB)
--------------------------------------------------------------------*)

CoordSendDecision ==
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ \E d \in {commit, abort}:
        /\ coordDecision = d
        /\ \A p \in participants:
            /\ preDec[p] = "none"
            /\ forwarded[Coord][p] = d

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, preDec, forwarded, finalDec, faulty>>

(* The coordinator may also receive votes and decide, but these are
   omitted for brevity because the focus is on the reliable broadcast.
   They are represented abstractly by nondeterministically setting
   coordDecision to commit or abort when all votes are in. *)

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: votes[p] # "none"
    /\ coordDecision' \in {commit, abort}
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, preDec, forwarded, finalDec, faulty>>

(*--------------------------------------------------------------------
  Participant actions
--------------------------------------------------------------------*)

(* 1. Send vote (abstracted) *)
SendVote(p) ==
    /\ p \in participants
    /\ ~faulty[p]
    /\ votes[p] = "none"
    /\ \E v \in {yes, no}: votes' = [votes EXCEPT ![p] = v]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   preDec, forwarded, finalDec, faulty>>

(* 2. Pre-decide from coordinator *)
PreDecFromCoord(p) ==
    /\ p \in participants
    /\ coordAlive
    /\ coordDecision \in {commit, abort}
    /\ preDec[p] = "none"
    /\ preDec' = [preDec EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, forwarded, finalDec, faulty>>

(* 3. Pre-decide from forwarding *)
PreDecFromFwd(p) ==
    /\ p \in participants
    /\ preDec[p] = "none"
    /\ \E q \in participants:
        /\ q # p
        /\ forwarded[q][p] \in {commit, abort}
        /\ LET d == IF forwarded[q][p] = commit THEN commit ELSE abort IN
            preDec' = [preDec EXCEPT ![p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, forwarded, finalDec, faulty>>

(* 4. Forward to another participant *)
Forward(p, q) ==
    /\ p \in participants /\ q \in participants /\ p # q
    /\ ~faulty[p] /\ ~faulty[q]
    /\ preDec[p] \in {commit, abort}
    /\ forwarded[p][q] = notsent
    /\ forwarded' = [forwarded EXCEPT ![p][q] = IF preDec[p] = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, preDec, finalDec, faulty>>

(* 5. Decide after forwarding to all *)
Decide(p) ==
    /\ p \in participants
    /\ ~faulty[p]
    /\ preDec[p] \in {commit, abort}
    /\ \A q \in participants: q # p => forwarded[p][q] # notsent
    /\ finalDec[p] = preDec[p]
    /\ finalDec' = [finalDec EXCEPT ![p] = preDec[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, preDec, forwarded, faulty>>

(* 6. Abort on timeout (coordinator dead and no broadcasts) *)
AbortTimeout(p) ==
    /\ p \in participants
    /\ ~faulty[p]
    /\ finalDec[p] = undecided
    /\ ~coordAlive
    /\ \A q \in participants:
        /\ forwarded[q][p] = notsent
    /\ finalDec' = [finalDec EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, preDec, forwarded, faulty>>

(* 7. Crash *)
Crash(p) ==
    /\ p \in participants
    /\ ~faulty[p]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                   votes, preDec, forwarded, finalDec>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in participants: SendVote(p)
    \/ CoordDecide
    \/ CoordSendDecision
    \/ CoordDie
    \/ \E p \in participants: PreDecFromCoord(p)
    \/ \E p \in participants: PreDecFromFwd(p)
    \/ \E p, q \in participants: Forward(p, q)
    \/ \E p \in participants: Decide(p)
    \/ \E p \in participants: AbortTimeout(p)
    \/ \E p \in participants: Crash(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                              votes, preDec, forwarded, finalDec, faulty>>

(*--------------------------------------------------------------------
  Safety invariants (explicitly listed for completeness)
--------------------------------------------------------------------*)
AC1 == \A p, q \in participants:
          /\ finalDec[p] = commit => finalDec[q] = commit
          /\ finalDec[p] = abort  => finalDec[q] = abort

AC2 == \A p \in participants:
          finalDec[p] = commit => \A q \in participants: votes[q] = yes

AC3 == \A p \in participants:
          finalDec[p] = abort =>
            \/ \E q \in participants: votes[q] = no
            \/ \E q \in participants: faulty[q] = TRUE
            \/ coordFaulty = TRUE

AC4 == \A p \in participants:
          (finalDec[p] = commit \/ finalDec[p] = abort) =>
          (finalDec[p]' = finalDec[p])

(*--------------------------------------------------------------------
  Liveness properties (optional, included for completeness)
--------------------------------------------------------------------*)
AC5 == \A p \in participants:
          ~faulty[p] => <> (finalDec[p] # undecided)

=============================================================================