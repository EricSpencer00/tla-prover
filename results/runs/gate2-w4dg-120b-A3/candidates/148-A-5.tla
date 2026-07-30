---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, NoHash, NoBlock, CalculateHash

ASSUME NoHashValue == NoHashVal
ASSUME NoBlock == NoBlockVal

VARIABLES lastHash, ledger, received

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> (PrivateKey \cup {NoBlock})]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

SumToRoot(n, h) ==
  IF h = NoHash
  THEN 0
  ELSE
    LET prev == ledger[n][h] IN
    IF prev \in PrivateKey
    THEN IF prev \in PrivateKey THEN GenesisBalance ELSE 0
    ELSE SumToRoot(n, prev)

BalanceInAccount(n) == SumToRoot(n, lastHash)

Sign(key, hash) == CalculateHash(key, hash)

CreateGenesisBlock(key) ==
  /\ lastHash = NoHash
  /\ lastHash' = Sign(key, NoHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = key]]
  /\ received' = [n \in Node |-> {lastHash'}]
  /\ UNCHANGED <<>>

CreateSendBlock(node, key) ==
  /\ lastHash # NoHash
  /\ key \in PrivateKey
  /\ BalanceInAccount(node) > 0
  /\ lastHash' = Sign(key, lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = key]]
  /\ received' = [n \in Node |-> {lastHash'} \cup received[n]]
  /\ UNCHANGED <<>>

CreateOpenBlock(node, key, ref) ==
  /\ lastHash # NoHash
  /\ key \in PrivateKey
  /\ ledger[node][ref] = NoBlock
  /\ lastHash' = Sign(key, lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = key]]
  /\ received' = [n \in Node |-> {lastHash'} \cup received[n]]
  /\ UNCHANGED <<>>

CreateReceiveBlock(node, key, ref) ==
  /\ lastHash # NoHash
  /\ key \in PrivateKey
  /\ ledger[node][ref] # NoBlock
  /\ lastHash' = Sign(key, lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = key]]
  /\ received' = [n \in Node |-> {lastHash'} \cup received[n]]
  /\ UNCHANGED <<>>

CreateChangeRep(node, key) ==
  /\ lastHash # NoHash
  /\ key \in PrivateKey
  /\ lastHash' = Sign(key, lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = key]]
  /\ received' = [n \in Node |-> {lastHash'} \cup received[n]]
  /\ UNCHANGED <<>>

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] \in PrivateKey
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E key \in PrivateKey : CreateGenesisBlock(key)
  \/ \E node \in Node, key \in PrivateKey : CreateSendBlock(node, key)
  \/ \E node \in Node, key \in PrivateKey, ref \in Hash : CreateOpenBlock(node, key, ref)
  \/ \E node \in Node, key \in PrivateKey, ref \in Hash : CreateReceiveBlock(node, key, ref)
  \/ \E node \in Node, key \in PrivateKey : CreateChangeRep(node, key)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

ValidSignature ==
  \A n \in Node : \A h \in Hash : ledger[n][h] \in PrivateKey

TypeInvariant == TypeOK /\ ValidSignature

====