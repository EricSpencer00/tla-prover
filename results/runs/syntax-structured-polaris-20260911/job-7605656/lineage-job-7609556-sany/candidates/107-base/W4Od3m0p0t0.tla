---- MODULE W4Od3m0p0t0 ----

CONSTANTS Banks, Ledger, LockRegister, LastBank

VARIABLES
  lockSnapshot
  lockValue
  lastBank
  bankState

SPECIFICATION
  Init == /\ lockSnapshot = <<>> 
           /\ lockValue = FREE
           /\ lastBank = <<>> 
           /\ bankState = [b \in Banks |-> IDLE]

NEXT
  Next == IF lockSnapshot = <<>> THEN
           IF lockValue = FREE THEN
             IF bankState = [b \in Banks |-> IDLE] THEN
               CHOOSE b \in Banks : lockValue' = b
             ELSE lockValue' = lockValue
           ELSE lockValue' = lockValue
         ELSE
           IF lockSnapshot = <<>> THEN
             lockSnapshot' = <<>> 
             lockValue' = lockValue
             lastBank' = lastBank
             bankState' = bankState
           ELSE
             CHOOSE b \in Banks : 
               IF b \in lockSnapshot THEN
                 lockSnapshot' = [b' \in lockSnapshot | b' \neq b |-> lockSnapshot[b']]
               ELSE
                 lockSnapshot' = lockSnapshot
               lockValue' = lockValue
               lastBank' = lastBank
               bankState' = bankState
           ENDIF
         ENDIF
       ENDIF

INVARIANTS
  MutEx == /\ lockValue \in {FREE, b \in Banks}
           /\ lockSnapshot \subseteq Banks
           /\ lockSnapshot \subseteq bankState
           /\ UNCHANGED <<lockValue, lockSnapshot, lastBank, bankState>> 

PROPERTIES
  AtMostOneInCriticalSection == /\ lockValue \in Banks
                               /\ lockSnapshot = <<>> 
                               /\ lockValue = lockSnapshot[lockValue]

====