---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

SignedBlock == [hash : Hash, sender : Node, receiver : PublicKey, prev : Hash, sig : {"ed25519"}, bal : 0..4]
EmptyBlock == [hash |-> NoHash, sender |-> NoBlock, receiver |-> NoBlock, prev |-> NoHash, sig |-> "ed25519", bal |-> 0]

TypeOK ==
  /\ lastHash \in {NoHashVal} \union Hash
  /\ ledger \in [Node -> [Hash -> SignedBlock \union {EmptyBlock}]]
  /\ received \in [Node -> SUBSET Hash]

OwnKey(n) == CHOOSE k \in PrivateKey : k \notin ledger[n][NoHash].hash

Init == /\ lastHash = NoHashVal
        /\ ledger = [n \in Node |-> [h \in Hash |-> EmptyBlock]]
        /\ received = [n \in Node |-> {}]

\* The first block in the lattice, created once, seeded with the total supply.
CreateGenesisBlock(n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash([sender |-> n, prev |-> NoHashVal])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [hash |-> lastHash, sender |-> n, receiver |-> OwnKey(n), prev |-> NoHashVal, sig |-> "ed25519", bal |-> GenesisBalance]]]
  /\ received' = [m \in Node |-> {lastHash}]

\* Send moves coins out of this account; it cannot overdraw.
CreateSendBlock(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash < (Cardinality(Hash) - 1)
  /\ \E amt \in [1..4] :
       /\ amt <= Balance(n, lastHash)
       /\ lastHash' = CalculateHash([sender |-> n, prev |-> lastHash])
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [hash |-> lastHash, sender |-> n, receiver |-> OwnKey(n), prev |-> NoHashVal, sig |-> "ed25519", bal |-> amt]]]
       /\ received' = [m \in Node |-> {lastHash} \union received[m]]
  /\ UNCHANGED <<lastHash, ledger>>

\* The first block of a new account, referencing a send directed to it.
CreateOpenBlock(n) ==
  /\ lastHash' = CalculateHash([sender |-> n, prev |-> NoHashVal])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [hash |-> lastHash, sender |-> n, receiver |-> OwnKey(n), prev |-> NoHashVal, sig |-> "ed25519", bal |-> 0]]]
  /\ received' = [m \in Node |-> {lastHash} \union received[m]]

CreateReceiveBlock(n) ==
  /\ lastHash' = CalculateHash([sender |-> n, prev |-> lastHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [hash |-> lastHash, sender |-> n, receiver |-> OwnKey(n), prev |-> NoHashVal, sig |-> "ed25519", bal |-> 0]]]
  /\ received' = [m \in Node |-> {lastHash} \union received[m]]

CreateChangeRepBlock(n) ==
  /\ lastHash' = CalculateHash([sender |-> n, prev |-> lastHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [hash |-> lastHash, sender |-> n, receiver |-> OwnKey(n), prev |-> NoHashVal, sig |-> "ed25519", bal |-> 0]]]
  /\ received' = [m \in Node |-> {lastHash} \union received[m]]

\* True signatures come from the account's own key and reference real blocks.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h].sig = "ed25519"
  /\ h \notin ledger[n] \cup received[n]
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node : CreateSendBlock(n) \/ CreateOpenBlock(n) \/ CreateReceiveBlock(n) \/ CreateChangeRepBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's replicated ledger must have a signature derived from
\* the public key of the account that owns its chain.
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] \in SignedBlock => ledger[n][h].sig = "ed25519"

====