---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

(* -------------------------------------------------------------------------- *)
(* Constants (must be supplied by the .cfg)                                   *)
(* -------------------------------------------------------------------------- *)
CONSTANTS
    Proc,            \* Set of process identifiers
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Send interval (positive integer)
    PredictPoint,    \* Predict interval (positive integer)
    Messages         \* Set of possible messages (must include alive messages)

(* Message type: we model only alive messages, identified by the sender      *)
Message == [type : {"alive"}, from : Proc]

\* -------------------------------------------------------------------------- *)
(* State variables                                                          *)
(* -------------------------------------------------------------------------- *)
VARIABLES
    sus,            \* [p \in Proc -> SUBSET Proc] : suspicion sets
    timeout,        \* [p \in Proc -> [q \in Proc -> Nat]] : per-process timeouts
    last,           \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since last heard
    clock,          \* [p \in Proc -> Nat] : local clock values
    out,            \* [p \in Proc -> SUBSET Message] : outgoing message sets
    inBox           \* [p \in Proc -> SUBSET Message] : messages received this step

\* -------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* -------------------------------------------------------------------------- *)
ClearSus(p) == 
    \A q \in Proc : sus[p][q] = FALSE

\* -------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* -------------------------------------------------------------------------- *)
Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]
    /\ inBox = [p \in Proc |-> {}]

\* -------------------------------------------------------------------------- *)
(* Actions                                                                  *)
(* -------------------------------------------------------------------------- *)

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0               \* send and predict never coincide
    /\ out' = [out EXCEPT ![p] = { [type |-> "alive", from |-> p] } ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Proc :
          IF q # p THEN
              last' = [last EXCEPT ![p][q] = last[p][q] + 1]
          ELSE
              last' = last
    /\ UNCHANGED << sus, timeout, inBox >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ sus' = [sus EXCEPT ![p] = { q \in Proc :
            q # p /\ last[p][q] > timeout[p][q] }]
    /\ \A q \in Proc :
          IF q # p THEN
              last' = [last EXCEPT ![p][q] = last[p][q] + 1]
          ELSE
              last' = last
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED << timeout, out, inBox >>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \A m \in inBox[p] :
          /\ m.type = "alive"
          /\ m.from # p
    /\ sus' = [sus EXCEPT ![p][m.from] = {} 
               \* remove sender from suspicion set *)
    /\ timeout' = [timeout EXCEPT ![p][m.from] =
          IF m.from \in sus[p] THEN timeout[p][m.from] + 1
          ELSE timeout[p][m.from]]
    /\ last' = [last EXCEPT ![p][m.from] = 0]
    /\ \A q \in Proc :
          IF q # m.from THEN
              last' = [last' EXCEPT ![p][q] = last[p][q] + 1]
          ELSE
              last' = last'
    /\ clock' = [clock EXCEPT ![p] = 
          IF clock[p] + 1 > Max({SendPoint, PredictPoint} \cup
                                 { timeout[p][q] : q \in Proc }) THEN 0
          ELSE clock[p] + 1]
    /\ out' = [out EXCEPT ![p] = {}]               \* after a receive step, no new outs
    /\ UNCHANGED inBox

\* The environmental step that delivers messages from out to inBox.
Deliver ==
    /\ inBox' = [p \in Proc |-> 
          { m \in UNION { out[q] : q \in Proc } : 
                /\ m.type = "alive"
                /\ m.from # p }]      \* each process receives all alive msgs
    /\ UNCHANGED << sus, timeout, last, clock, out >>

\* Process step for a single process
ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Next ==
    \/ \E p \in Proc : ProcStep(p)
    \/ Deliver

\* -------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* -------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<< sus, timeout, last, clock, out, inBox >>

\* -------------------------------------------------------------------------- *)
(* Type invariant (as required)                                            *)
(* -------------------------------------------------------------------------- *)
TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Message]
    /\ inBox \in [Proc -> SUBSET Message]

\* -------------------------------------------------------------------------- *)
(* The module's exported definitions                                         *)
(* -------------------------------------------------------------------------- *)
THEOREM Spec => []TypeOK

=============================================================================