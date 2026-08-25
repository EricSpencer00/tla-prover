---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (to be supplied by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
Message == [type : {"alive"}, from : Proc, to : Proc]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES clock, suspicion, timeout, last, outbox

vars == << clock, suspicion, timeout, last, outbox >>

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AllProcExcept(p) == Proc \ {p}

(* Default timeout for a pair (p,q) where p != q *)
DefaultTimeout(p,q) == d0

(* Compute the maximal relevant threshold for resetting the clock *)
MaxThreshold(p) ==
  LET tSet == { timeout[p][q] : q \in AllProcExcept(p) } \cup {SendPoint, PredictPoint} IN
  IF tSet = {} THEN 0 ELSE Max(tSet)

ResetClock(p, c) ==
  IF c > MaxThreshold(p) THEN 0 ELSE c

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ last = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
  /\ outbox = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ last \in [Proc -> [Proc -> Nat]]
  /\ outbox \in [Proc -> SUBSET Messages]

(*-----------------------------------------------------------------
  Send action for a process p
-----------------------------------------------------------------*)
Send(p) ==
  LET isSend == (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0) IN
  /\ isSend
  /\ UNCHANGED << suspicion, timeout >>
  /\ outbox' = [outbox EXCEPT ![p] = { [type |-> "alive", from |-> p, to |-> q] : q \in AllProcExcept(p) }]
  /\ clock' = [clock EXCEPT ![p] = ResetClock(p, clock[p] + 1)]
  /\ last' =
       [last EXCEPT ![p][q] =
          IF q # p /\ last[p][q] < timeout[p][q] THEN last[p][q] + 1
          ELSE last[p][q] ] 
  /\ UNCHANGED << outbox[Proc \ {p}], suspicion[Proc \ {p}], timeout[Proc \ {p}], last[Proc \ {p}], clock[Proc \ {p}] >>

(*-----------------------------------------------------------------
  Predict action for a process p
-----------------------------------------------------------------*)
Predict(p) ==
  LET isPred == (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0) IN
  /\ isPred
  /\ UNCHANGED << outbox, timeout >>
  /\ suspicion' =
       [suspicion EXCEPT ![p] = suspicion[p] \cup
          { q \in AllProcExcept(p) : last[p][q] > timeout[p][q] }]
  /\ clock' = [clock EXCEPT ![p] = ResetClock(p, clock[p] + 1)]
  /\ last' =
       [last EXCEPT ![p][q] =
          IF q # p /\ last[p][q] < timeout[p][q] THEN last[p][q] + 1
          ELSE last[p][q] ]
  /\ UNCHANGED << outbox[Proc], suspicion[Proc \ {p}], timeout[Proc \ {p}], last[Proc \ {p}], clock[Proc \ {p}] >>

(*-----------------------------------------------------------------
  Receive action for a process p
  (abstract: nondeterministically receives any subset of alive messages)
-----------------------------------------------------------------*)
Receive(p) ==
  /\ \lnot ( (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0) )
  /\ \lnot ( (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0) )
  (* Choose any set of incoming alive messages addressed to p *)
  /\ \E inc \subseteq { m \in Messages : m.type = "alive" /\ m.to = p } :
        LET
          ResetLast(q) ==
            IF q \in { m.from : m \in inc } THEN 0 ELSE last[p][q]
          RemoveSus(q) ==
            IF q \in { m.from : m \in inc } THEN suspicion[p] \ {q} ELSE suspicion[p]
          IncreaseTimeout(q) ==
            IF q \in { m.from : m \in inc } /\ q \in suspicion[p] THEN timeout[p][q] + 1
            ELSE timeout[p][q]
        IN
        /\ suspicion' = [suspicion EXCEPT ![p] = RemoveSus(p)]
        /\ timeout' = [timeout EXCEPT ![p][q] = IncreaseTimeout(q) \ 
                         FOR q \in AllProcExcept(p) ]
        /\ last' = [last EXCEPT ![p][q] = ResetLast(q) \ 
                     FOR q \in AllProcExcept(p) ]
        /\ clock' = [clock EXCEPT ![p] = ResetClock(p, clock[p] + 1)]
        /\ outbox' = [outbox EXCEPT ![p] = {}]
        /\ UNCHANGED << clock[Proc \ {p}], suspicion[Proc \ {p}], timeout[Proc \ {p}], 
                        last[Proc \ {p}], outbox[Proc \ {p}] >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

(*-----------------------------------------------------------------
  Specification (optional, not required by the .cfg but useful)
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

=============================================================================