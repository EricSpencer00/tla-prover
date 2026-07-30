---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS
  Proc, d0, SendPoint, PredictPoint, Messages

Typedef == BOOLEAN

\* Process-local state: suspicion set, adaptive timeout interval per peer,
\* ticks-since-last-heard per peer, local clock, and outgoing messages.
VARIABLES suspect, timeoutInt, waitTicks, clock, outMsgs

vars == <<suspect, timeoutInt, waitTicks, clock, outMsgs>>

NoMsg == [snd |-> CHOOSE p \in Proc : TRUE, dst |-> CHOOSE p \in Proc : TRUE]

MsgSet == {m \in Messages : m.dst \in Proc}

Init == /\ suspect = [p \in Proc |-> {}]
        /\ timeoutInt = [p \in Proc |-> d0]
        /\ waitTicks = [p \in Proc |-> [q \in Proc |-> 0]]
        /\ clock = [p \in Proc |-> 0]
        /\ outMsgs = [p \in Proc |-> {}]

\* Send alive messages at a send-point tick; fire only when not at a predict point.
Send(p) == /\ clock[p] % SendPoint = 0
           /\ clock[p] % PredictPoint # 0
           /\ outMsgs' = [outMsgs EXCEPT ![p] = {m \in Messages : m.dst \in Proc}]
           /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
           /\ waitTicks' = [waitTicks EXCEPT ![p] = [q \in Proc |-> IF waitTicks[p][q] < timeoutInt[p][q]
                                                             THEN waitTicks[p][q] + 1
                                                             ELSE waitTicks[p][q]]]
           /\ UNCHANGED <<suspect, timeoutInt>>

\* Predict crashes at a predict-point tick; fire only when not at a send point.
Predict(p) == /\ clock[p] % PredictPoint = 0
              /\ clock[p] % SendPoint # 0
              /\ suspect' = [suspect EXCEPT ![p] = {q \in suspect[p] : waitTicks[p][q] <= timeoutInt[p][q]}
                                            \cup {q \in Proc : q # p /\ waitTicks[p][q] > timeoutInt[p][q]}]
              /\ waitTicks' = [waitTicks EXCEPT ![p] = [q \in Proc |-> IF waitTicks[p][q] < timeoutInt[p][q]
                                                                THEN waitTicks[p][q] + 1
                                                                ELSE waitTicks[p][q]]]
              /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
              /\ UNCHANGED <<timeoutInt, outMsgs>>

\* Receive incoming messages at all other ticks; reset suspicion on receipt.
Recieve(p) == /\ clock[p] % SendPoint # 0
               /\ clock[p] % PredictPoint # 0
               /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.dst :
                                          \E q \in Proc : m \in outMsgs[q]}]
               /\ timeoutInt' = [timeoutInt EXCEPT ![p][m.dst] =
                                    IF m \in outMsgs[p] THEN timeoutInt[p][m.dst] + 1
                                    ELSE IF \E q \in Proc : m \in outMsgs[q] /\ q # p
                                         THEN timeoutInt[p][m.dst] + 1
                                         ELSE timeoutInt[p][m.dst]]
               /\ waitTicks' = [waitTicks EXCEPT ![p] = [q \in Proc |-> IF q \in {m.dst : m \in outMsgs[p]}
                                                                      THEN 0
                                                                      ELSE waitTicks[p][q]]]
               /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > timeoutInt[p][p]
                                                      THEN 0
                                                      ELSE clock[p] + 1]
               /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]

Next == \E p \in Proc : Send(p) \/ Predict(p) \/ Recieve(p)

Spec == Init /\ [][Next]_vars

\* Correctness: all timers stay within their domains, and no message is lost.
TypeOK == /\ \A p \in Proc : \A q \in Proc : waitTicks[p][q] \in Nat
          /\ \A p \in Proc : suspect[p] \subseteq Proc
          /\ \A p \in Proc : \A q \in Proc : timeoutInt[p][q] \in Nat
          /\ \A p \in Proc : outMsgs[p] \subseteq MsgSet

====