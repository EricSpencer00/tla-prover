---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> (Hash \cup {NoBlockVal})]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

Balance(n, h) ==
  IF h # NoHashVal THEN
    LET p == ledger[n][h] IN
    IF p = NoBlockVal THEN 0
    ELSE IF p = NoHashVal THEN GenesisBalance
    ELSE IF h \in received[n] THEN Balance(n, p)
    ELSE Balance(n, p) + (IF p \in Hash THEN Balance(MAP[PublicKey => p], NoHashVal) ELSE 0)
  ELSE 0

\* Super-exponential state growth: the chain records every action order.
BalanceInvariant == Balance(NoHash, NoHashVal) <= GenesisBalance

ValidateSignature(n, h) ==
  /\ ledger[n][h] \in Hash \cup {NoHashVal}
  /\ \E k \in PrivateKey :
       /\ ledger[n][CalculateHash(h, ledger[n][h])].chainOwner = MAP[PublicKey => k]
       /\ ledger[n][CalculateHash(h, ledger[n][h])].sig = k

CreateGenesisBlock(n) ==
  /\ lastHash = NoHashVal
  /\ ledger[n][NoHashVal] = NoHashVal
  /\ \E k \in PrivateKey :
       /\ ledger[n][NoHashVal] = {chainOwner : MAP[PublicKey => k], sig : k}
  /\ lastHash' = NoHashVal
  /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = NoHashVal THEN ledger[n][NoHashVal] ELSE NoBlockVal]]
  /\ received' = [m \in Node |-> IF m = n THEN {NoHashVal} ELSE {}]

CreateSendBlock(n) ==
  /\ lastHash \in Hash
  /\ Balance(n, lastHash) >= 1
  /\ \E k \in PrivateKey :
       /\ ledger[n][lastHash].chainOwner = MAP[PublicKey => k]
       /\ \E d \in 1..Balance(n, lastHash) :
            /\ ledger[n][CalculateHash(lastHash, d)] = {chainOwner : MAP[PublicKey => k], sig : k}
            /\ \E m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(lastHash, d)}]
  /\ UNCHANGED <<lastHash, ledger>>

CreateOpenBlock(n) ==
  /\ lastHash \in Hash
  /\ \E d \in Hash :
       /\ d \in ledger[n][lastHash].sent
       /\ ledger[n][d].recip = n
       /\ ledger[n][CalculateHash(lastHash, d)] = {chainOwner : ledger[n][lastHash].chainOwner, sig : ledger[n][lastHash].sig}
       /\ ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, d)] = ledger[n][lastHash]]
       /\ \E m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(lastHash, d)}]
  /\ UNCHANGED lastHash

CreateReceiveBlock(n) ==
  /\ lastHash \in Hash
  /\ \E d \in Hash :
       /\ d \in ledger[n][lastHash].sent
       /\ ledger[n][d].recip = n
       /\ ledger[n][CalculateHash(lastHash, d)] = {chainOwner : ledger[n][lastHash].chainOwner, sig : ledger[n][lastHash].sig}
       /\ ledger' = [ledger EXCEPT ![n][CalculateHash(lastHash, d)] = ledger[n][lastHash]]
       /\ \E m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(lastHash, d)}]
  /\ UNCHANGED lastHash

CreateChangeRepresentativeBlock(n) ==
  /\ lastHash \in Hash
  /\ \E k \in PrivateKey :
       /\ ledger[n][lastHash].chainOwner = MAP[PublicKey => k]
       /\ ledger[n][CalculateHash(lastHash, 0)] = {chainOwner : MAP[PublicKey => k], sig : k}
       /\ \E m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(lastHash, 0)}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateSendBlock(n) \/ CreateOpenBlock(n) \/ CreateReceiveBlock(n) \/ CreateChangeRepresentativeBlock(n)

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node : \A h \in Hash : ValidateSignature(n, h)

====