---- MODULE ACP_NB ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (declared in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Participant == participants
AllVals    == {yes, no}
AllDecs    == {commit, abort, undecided}
AllStates  == {waiting, commit, abort, undecided}

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    coordAlive,            \* TRUE if coordinator is alive
    coordFaulty,           \* TRUE if coordinator has crashed (faulty)
    coordDecision,        \* coordinator's decision (commit/abort) or NONE
    votes,                \* [p \in Participant -> AllVals]  (vote of each participant)
    voteSent,             \* [p \in Participant -> BOOLEAN]  (has p sent its vote)
    participantAlive,     \* [p \in Participant -> BOOLEAN]  (alive status)
    participantFaulty,    \* [p \in Participant -> BOOLEAN]  (faulty status)
    participantDecision,  \* [p \in Participant -> AllDecs]  (final decision)
    fwdTable,             \* [p \in Participant -> [q \in Participant -> {notsent, commit, abort}]]
    forwardedToAll        \* [p \in Participant -> BOOLEAN]  (has p forwarded to everybody)

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
IsNonFaulty(p) == participantAlive[p] /\ ~participantFaulty[p]
AllNonFaultyAlive == \A p \in Participant : IsNonFaulty(p)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE
    /\ coordDecision = "NONE"
    /\ votes = [p \in Participant |-> no]            \* default; will be set by Vote actions
    /\ voteSent = [p \in Participant |-> FALSE]
    /\ participantAlive = [p \in Participant |-> TRUE]
    /\ participantFaulty = [p \in Participant |-> FALSE]
    /\ participantDecision = [p \in Participant |-> undecided]
    /\ fwdTable = [p \in Participant |-> [q \in Participant |-> notsent]]
    /\ forwardedToAll = [p \in Participant |-> FALSE]

(* ----------------------------------------------------------------------
   Coordinator actions (inherited from ACP-SB, simplified)
   ---------------------------------------------------------------------- *)

CoordDie ==
    /\ coordAlive = TRUE
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, votes, voteSent, participantAlive,
                    participantFaulty, participantDecision, fwdTable,
                    forwardedToAll>>

CoordMakeDecision ==
    /\ coordAlive = TRUE
    /\ coordDecision = "NONE"
    /\ \A p \in Participant : voteSent[p] = TRUE
    /\ coordDecision' = IF \A p \in Participant : votes[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, votes, voteSent,
                    participantAlive, participantFaulty,
                    participantDecision, fwdTable, forwardedToAll>>

(* ----------------------------------------------------------------------
   Participant actions
   ---------------------------------------------------------------------- *)

Vote(p) ==
    /\ IsNonFaulty(p)
    /\ voteSent[p] = FALSE
    /\ votes' = [votes EXCEPT ![p] = IF votes[p] = no THEN no ELSE yes]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision,
                    participantAlive, participantFaulty,
                    participantDecision, fwdTable, forwardedToAll>>

PreDecideFromCoord(p) ==
    /\ IsNonFaulty(p)
    /\ participantDecision[p] = undecided
    /\ coordAlive = TRUE
    /\ coordDecision \in {commit, abort}
    /\ fwdTable[p][p] = notsent
    /\ fwdTable' = [fwdTable EXCEPT ![p][p] = IF coordDecision = commit THEN commit ELSE abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, participantAlive, participantFaulty,
                    participantDecision, forwardedToAll>>

PreDecideFromForward(p) ==
    /\ IsNonFaulty(p)
    /\ participantDecision[p] = undecided
    /\ \E q \in Participant :
          q # p /\ fwdTable[q][p] \in {commit, abort} /\ fwdTable[p][p] = notsent
    /\ LET d == CHOOSE d \in {commit, abort} : 
                \E q \in Participant : q # p /\ fwdTable[q][p] = d
       IN fwdTable' = [fwdTable EXCEPT ![p][p] = d]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, participantAlive, participantFaulty,
                    participantDecision, forwardedToAll>>

Forward(p) ==
    /\ IsNonFaulty(p)
    /\ fwdTable[p][p] \in {commit, abort}
    /\ \E q \in Participant : q # p /\ fwdTable[p][q] = notsent
    /\ \E q \in Participant :
          q # p /\ fwdTable[p][q] = notsent /\ 
          fwdTable' = [fwdTable EXCEPT ![p][q] = fwdTable[p][p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, participantAlive, participantFaulty,
                    participantDecision, forwardedToAll>>

Decide(p) ==
    /\ IsNonFaulty(p)
    /\ fwdTable[p][p] \in {commit, abort}
    /\ \A q \in Participant : q # p => fwdTable[p][q] = fwdTable[p][p]
    /\ participantDecision[p] = undecided
    /\ participantDecision' = [participantDecision EXCEPT ![p] = fwdTable[p][p]]
    /\ forwardedToAll' = [forwardedToAll EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, participantAlive, participantFaulty,
                    fwdTable>>

AbortOnTimeout(p) ==
    /\ IsNonFaulty(p)
    /\ participantDecision[p] = undecided
    /\ coordAlive = FALSE
    /\ \A q \in Participant : fwdTable[q][p] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ forwardedToAll' = [forwardedToAll EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, participantAlive, participantFaulty,
                    fwdTable>>

Die(p) ==
    /\ participantAlive[p] = TRUE
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, votes,
                    voteSent, participantDecision, fwdTable,
                    forwardedToAll>>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E p \in Participant : Vote(p)
    \/ \E p \in Participant : PreDecideFromCoord(p)
    \/ \E p \in Participant : PreDecideFromForward(p)
    \/ \E p \in Participant : Forward(p)
    \/ \E p \in Participant : Decide(p)
    \/ \E p \in Participant : AbortOnTimeout(p)
    \/ \E p \in Participant : Die(p)
    \/ CoordMakeDecision
    \/ CoordDie

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
SpecNB == Init /\ [][Next]_<<coordAlive, coordFaulty, coordDecision,
                            votes, voteSent,
                            participantAlive, participantFaulty,
                            participantDecision, fwdTable,
                            forwardedToAll>>

(* ----------------------------------------------------------------------
   Type invariant (ensures all variables stay within their domains)
   ---------------------------------------------------------------------- *)
TypeInvNB ==
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {"NONE", commit, abort}
    /\ votes \in [Participant -> AllVals]
    /\ voteSent \in [Participant -> BOOLEAN]
    /\ participantAlive \in [Participant -> BOOLEAN]
    /\ participantFaulty \in [Participant -> BOOLEAN]
    /\ participantDecision \in [Participant -> AllDecs]
    /\ fwdTable \in [Participant -> [Participant -> {notsent, commit, abort}]]
    /\ forwardedToAll \in [Participant -> BOOLEAN]

(* ----------------------------------------------------------------------
   Safety properties (invariants)
   ---------------------------------------------------------------------- *)

(* AC1: No two participants decide differently *)
AC1 ==
    \A p, q \in Participant :
        (participantDecision[p] = commit => participantDecision[q] = commit) /\
        (participantDecision[p] = abort  => participantDecision[q] = abort)

(* AC2: Commit validity *)
AC2 ==
    \A p \in Participant :
        participantDecision[p] = commit => \A q \in Participant : votes[q] = yes

(* AC3: Abort validity *)
AC3 ==
    \A p \in Participant :
        participantDecision[p] = abort =>
            (\E q \in Participant : votes[q] = no) \/
            (\E q \in Participant : participantFaulty[q]) \/
            coordFaulty

(* AC4: Irrevocability *)
AC4 ==
    \A p \in Participant :
        participantDecision[p] \in {commit, abort} =>
            participantDecision[p]' = participantDecision[p]

(* ----------------------------------------------------------------------
   Liveness properties (optional, but defined for completeness)
   ---------------------------------------------------------------------- *)
AC5 == WF_vars(Decide(p)) \* placeholder; actual liveness expressed in .cfg

(* ----------------------------------------------------------------------
   Theorem (optional, connects Spec with invariants)
   ---------------------------------------------------------------------- *)
THEOREM SpecImpliesSafety == SpecNB => [] (AC1 /\ AC2 /\ AC3 /\ AC4)

====