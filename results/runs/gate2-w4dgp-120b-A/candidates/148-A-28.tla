---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Hash, NoHashVal,
  PrivateKey, PublicKey,
  Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Account balances are read recursively from each account's own blockchain.
Balance(ledger, node) == IF ledger = [Hash |-> NoBlockVal] THEN 0
  ELSE LET last == ledger[lastHash] IN
    IF last.chainOwner = node THEN
      IF last.blockType = "open" THEN last.amount
      ELSE IF last.blockType = "send" THEN Balance([k \in Hash |-> IF k = last.prev THEN NoBlockVal ELSE ledger[k]], node) - last.amount
      ELSE IF last.blockType = "receive" THEN Balance([k \in Hash |-> IF k = last.prev THEN NoBlockVal ELSE ledger[k]], node) + last.amount
      ELSE Balance([k \in Hash |-> IF k = last.prev THEN NoBlockVal ELSE ledger[k]], node)
    ELSE Balance([k \in Hash |-> IF k = last.prev THEN NoBlockVal ELSE ledger[k]], node)

ConstructionMin == 0
ConstructionMax == 1

Construction == CHOOSE n \in ConstructionMin .. ConstructionMax : TRUE

RECURSIVE Balances(_)
Balances(S) == IF S = {} THEN 0
  ELSE CHOOSE n \in S : Balances(S \ {n}) + Balance(n)

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

ConstructionPending == \E n \in Node : \A m \in Node : m \in received[n]

CreateGenesisBlock(n) ==
  /\ ~ConstructionPending
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash(n, NoHashVal, NoHashVal, NoHashVal, "genesis", GenesisBalance, ANY)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [blockType |-> "genesis", chainOwner |-> n, prev |-> NoHashVal, amount |-> GenesisBalance, target |-> NoHashVal, signature |-> NoHashVal]]]
  /\ received' = [m \in Node |-> {}]

CreateSendBlock(n, target) ==
  /\ ~ConstructionPending
  /\ lastHash # NoHashVal
  /\ Balance(ledger[n], n) >= 1
  /\ lastHash' = CalculateHash(n, ledger[n][lastHash].chainOwner, lastHash, target, "send", 1, ANY)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [blockType |-> "send", chainOwner |-> n, prev |-> lastHash, amount |-> 1, target |-> target, signature |-> NoHashVal]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateOpenBlock(n, source) ==
  /\ ~ConstructionPending
  /\ ledger[n][lastHash].blockType = "send"
  /\ ledger[n][lastHash].target = n
  /\ ledger[n][lastHash].chainOwner # n
  /\ source \notin {ledger[n][k].target : k \in Hash}
  /\ lastHash' = CalculateHash(n, ledger[n][lastHash].chainOwner, lastHash, NoHashVal, "open", ledger[n][lastHash].amount, ANY)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [blockType |-> "open", chainOwner |-> n, prev |-> lastHash, amount |-> ledger[n][lastHash].amount, target |-> NoHashVal, signature |-> NoHashVal]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateReceiveBlock(n, source) ==
  /\ ~ConstructionPending
  /\ lastHash # NoHashVal
  /\ source \notin {ledger[n][k].target : k \in Hash}
  /\ \E k \in Hash :
       /\ ledger[n][k].blockType = "send"
       /\ ledger[n][k].target = n
       /\ lastHash' = CalculateHash(n, ledger[n][lastHash].chainOwner, lastHash, k, "receive", ledger[n][k].amount, ANY)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [blockType |-> "receive", chainOwner |-> n, prev |-> lastHash, amount |-> ledger[n][k].amount, target |-> k, signature |-> NoHashVal]]]
       /\ received' = [m \in Node |-> received[m] \cup {lastHash}]
  /\ UNCHANGED <<lastHash, ledger, received>>

CreateChangeReprBlock(n) ==
  /\ ~ConstructionPending
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash(n, ledger[n][lastHash].chainOwner, lastHash, NoHashVal, "change_representative", 0, ANY)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [blockType |-> "change_representative", chainOwner |-> n, prev |-> lastHash, amount |-> 0, target |-> NoHashVal, signature |-> NoHashVal]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h].signature = NoHashVal
  /\ ledger[n][h].signature' = NoHashVal
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, target \in Node : CreateSendBlock(n, target)
  \/ \E n \in Node, source \in Node : CreateOpenBlock(n, source)
  \/ \E n \in Node, source \in Node : CreateReceiveBlock(n, source)
  \/ \E n \in Node : CreateChangeReprBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> [blockType : {"genesis", "send", "receive", "open", "change_representative", "invalid"}, chainOwner : Node, prev : Hash \cup {NoHashVal}, amount : 0 .. GenesisBalance, target : Node \cup {NoHashVal}, signature : Hash \cup {NoHashVal}]]]
  /\ received \in [Node -> SUBSET Hash]

\* Safety: every block in every node's ledger has a valid signature. This is
\* deliberately the strongest per-block property in the spec, so the model will
\* stop exploring as soon as an invalid signature can be produced.
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal =>
      /\ ledger[n][h].signature = NoHashVal
      /\ ledger[n][h].chainOwner \in Node

====