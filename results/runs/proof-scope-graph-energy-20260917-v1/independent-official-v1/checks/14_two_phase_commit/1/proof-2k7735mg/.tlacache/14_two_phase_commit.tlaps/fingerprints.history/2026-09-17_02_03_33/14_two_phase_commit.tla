---- MODULE 14_two_phase_commit ----
\* benchmark: i4-two-phase-commit

EXTENDS TLC

CONSTANT Node

VARIABLE vote_yes
VARIABLE vote_no
VARIABLE alive
VARIABLE go_commit
VARIABLE go_abort
VARIABLE decide_commit
VARIABLE decide_abort

VARIABLE abort_flag

vars == <<vote_yes,vote_no,alive,go_commit,go_abort,decide_commit,decide_abort,abort_flag>>

Vote1(n) ==
    /\ n \in alive
    /\ n \notin vote_no
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_yes' = vote_yes \cup {n}
    /\ UNCHANGED <<vote_no,alive,go_commit,go_abort,decide_commit,decide_abort,abort_flag>>

Vote2(n) ==
    /\ n \in alive
    /\ n \notin vote_yes
    /\ n \notin decide_commit
    /\ n \notin decide_abort
    /\ vote_no' = vote_no \cup {n}
    /\ abort_flag' = TRUE
    /\ decide_abort' = decide_abort \cup {n}
    /\ UNCHANGED <<vote_yes,alive,go_commit,go_abort,decide_commit>>

Fail(n) ==
    /\ n \in alive
    /\ alive' = alive \ {n}
    /\ abort_flag' = TRUE
    /\ UNCHANGED <<vote_yes,vote_no,go_commit,go_abort,decide_commit,decide_abort>>

Go1 ==
    /\ \A n \in Node : n \notin go_commit
    /\ \A n \in Node : n \notin go_abort
    /\ \A n \in Node : n \in vote_yes
    /\ go_commit' = Node
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_abort,decide_commit,decide_abort,abort_flag>>

Go2 ==
    /\ \A n \in Node : n \notin go_commit
    /\ \A n \in Node : n \notin go_abort
    /\ \E n \in Node : (n \in vote_no) \/ (n \notin alive)
    /\ go_abort' = Node
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_commit,decide_commit,decide_abort,abort_flag>>

Commit(n) ==
    /\ n \in alive
    /\ n \in go_commit
    /\ decide_commit' = decide_commit \cup {n}
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_commit,go_abort,decide_abort,abort_flag>>

Abort(n) ==
    /\ n \in alive
    /\ n \in go_abort
    /\ decide_abort' = decide_abort \cup {n}
    /\ UNCHANGED <<vote_yes,vote_no,alive,go_commit,go_abort,decide_commit,abort_flag>>

Next ==
    \/ \E n \in Node : Vote1(n)
    \/ \E n \in Node : Vote2(n)
    \/ \E n \in Node : Fail(n)
    \/ Go1
    \/ Go2
    \/ \E n \in Node : Commit(n)
    \/ \E n \in Node : Abort(n)

Init == 
    /\ vote_yes = {}
    /\ vote_no = {}
    /\ alive = Node
    /\ go_commit = {}
    /\ go_abort = {}
    /\ decide_commit = {}
    /\ decide_abort = {}
    /\ abort_flag = FALSE

NextUnchanged == UNCHANGED vars

TypeOK ==
    /\ vote_yes \in SUBSET Node
    /\ vote_no \in SUBSET Node
    /\ alive \in SUBSET Node
    /\ go_commit \in SUBSET Node
    /\ go_abort \in SUBSET Node
    /\ decide_commit \in SUBSET Node
    /\ decide_abort \in SUBSET Node
    /\ abort_flag \in BOOLEAN 
    
Safety == 
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \notin decide_abort) 
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \in vote_yes)
    /\ \A n,n2 \in Node : (n \in decide_abort) => abort_flag

Symmetry == Permutations(Node)


\* Inductive strengthening conjuncts
Inv703_1_0_def == (go_abort = {}) \/ ((go_commit = {}))
Inv1049_1_1_def == \A VARJ \in Node : ~(VARJ \in vote_no) \/ (~(VARJ \in vote_yes))
Inv648_1_2_def == (decide_abort = {}) \/ ((go_commit = {}))
Inv699_1_3_def == (decide_commit = {}) \/ (~(go_commit = {}))
Inv346_1_4_def == \A VARJ \in Node : (VARJ \in alive) \/ ((abort_flag))
Inv313_1_5_def == \A VARI \in Node : (VARI \in vote_yes) \/ ((go_commit = {}))
Inv588_1_0_def == (abort_flag) \/ ((go_abort = {}))
Inv591_1_1_def == (abort_flag) \/ ((vote_no = {}))
Inv2455_2_2_def == \A VARI \in Node : (VARI \in go_abort) \/ ((decide_abort = {})) \/ (~(vote_no = {}))
Inv192_1_0_def == \A VARI \in Node : (VARI \in go_abort) \/ ((go_abort = {}))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv703_1_0_def
  /\ Inv1049_1_1_def
  /\ Inv648_1_2_def
  /\ Inv699_1_3_def
  /\ Inv346_1_4_def
  /\ Inv313_1_5_def
  /\ Inv588_1_0_def
  /\ Inv591_1_1_def
  /\ Inv2455_2_2_def
  /\ Inv192_1_0_def
  

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'OBVIOUS
====