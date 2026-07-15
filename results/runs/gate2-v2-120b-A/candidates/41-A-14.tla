---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (must be bound in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of possible message identifiers (e.g., {"alive"})

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    clock,         \* [p \in Proc -> Nat]   local clock of each process
    suspect,       \* [p \in Proc -> SUBSET Proc]   suspicion set of each process
    timeout,       \* [p \in Proc -> [q \in Proc -> Nat]]   timeout interval for each pair
    lastHeard,     \* [p \in Proc -> [q \in Proc -> Nat]]   ticks since p last heard from q
    outMsgs        \* [p \in Proc -> SUBSET { [dest |-> q, tag |-> "alive"] : q \in Proc \ {p} }]\

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
OtherProc(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveMsg(p,q) == [dest |-> q, tag |-> "alive"]
AllAliveMsgs(p) == { AliveMsg(p,q) : q \in OtherProc(p) }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outMsgs = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outMsgs' = [outMsgs EXCEPT ![p] = AllAliveMsgs(p)]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
           IF q \in OtherProc(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] 
           FOR q \in Proc]
    /\ UNCHANGED << suspect, timeout >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT 
          ![p] = suspect[p] \cup { q \in OtherProc(p) : 
                lastHeard[p][q] >= timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
           IF q \in OtherProc(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] 
           FOR q \in Proc]
    /\ UNCHANGED << outMsgs, timeout >>

Receive(p) ==
    /\ \E msgs \in outMsgs : 
          \A m \in msgs : 
            /\ m.tag = "alive"
            /\ m.dest \in Proc
            /\ \E sender \in Proc :
                  /\ sender # p
                  /\ m = AliveMsg(sender, p)
    /\ \E sender \in Proc :
          /\ sender # p
          /\ m \in outMsgs[sender]
          /\ m = AliveMsg(sender, p)
    /\ LET
          newLastHeard == [lastHeard EXCEPT ![p][sender] = 0]
          newSuspect   == IF sender \in suspect[p] 
                            THEN [suspect EXCEPT ![p] = suspect[p] \ {sender}]
                            ELSE suspect
          incTimeout   == [timeout EXCEPT ![p][sender] = 
                            IF sender \in suspect[p] 
                               THEN timeout[p][sender] + 1
                               ELSE timeout[p][sender]]
       IN
          /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]   \* consume all incoming msgs
          /\ lastHeard' = newLastHeard
          /\ suspect' = newSuspect
          /\ timeout' = incTimeout
          /\ clock' = [clock EXCEPT ![p] = 
                IF clock[p] + 1 > 
                   Max({SendPoint, PredictPoint} \cup 
                       { timeout[p][q] : q \in OtherProc(p) })
                THEN 0
                ELSE clock[p] + 1]

Idle(p) ==
    /\ \A q \in OtherProc(p) : 
          \E m \in outMsgs[q] : m = AliveMsg(p, q)
    /\ outMsgs' = outMsgs
    /\ clock' = [clock EXCEPT ![p] = 
          IF clock[p] + 1 > 
             Max({SendPoint, PredictPoint} \cup 
                 { timeout[p][q] : q \in OtherProc(p) })
          THEN 0
          ELSE clock[p] + 1]
    /\ UNCHANGED << suspect, timeout, lastHeard >>

ProcAction(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ Idle(p)

Next ==
    \E p \in Proc : ProcAction(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<clock, suspect, timeout, lastHeard, outMsgs>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (the only invariant required by the cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outMsgs \in [Proc -> SUBSET { [dest |-> q, tag |-> "alive"] : q \in Proc }]

\* ----------------------------------------------------------------------
\* THEOREM to let TLC know the spec
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====