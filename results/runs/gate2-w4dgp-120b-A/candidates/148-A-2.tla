---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash
ASSUME NoHash \notin Hash
ASSUME NoBlock \notin Hash

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

SignedBlock == [account: PublicKey, prev: Hash, typ: {"genesis", "send", "open", "receive", "change"}, amount: Nat, recipient: PublicKey, representative: PublicKey, signer: PrivateKey]

CalculateHashImpl == (privateKey, prevHash, data) \in (PrivateKey \X Hash \X [account: PublicKey, prev: Hash, typ: {"genesis", "send", "open", "receive", "change"}, amount: Nat, recipient: PublicKey, representative: PublicKey]) -> CHOOSE h \in Hash : TRUE

NodeOf(p) == CHOOSE n \in Node : p \in PrivateKey

NextHash(prev) == CHOOSE h \in Hash : h # prev

EmptyLedger == [h \in Hash |-> NoBlockVal]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> EmptyLedger]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = NoHash THEN [account |-> PublicKey, prev |-> NoHash, typ |-> "genesis", amount |-> GenesisBalance, recipient |-> PublicKey, representative |-> PublicKey, signer |-> privateKey] ELSE NoBlockVal] ]
  /\ lastHash' = NoHash
  /\ received' = [n \in Node |-> {}]

CreateSendBlock(n, privateKey, amount, recipient) ==
  /\ \A m \in Node : ledger[m][NoHash] # NoBlockVal
  /\ PrivateKey \in PRIVATEKEY
  /\ amount > 0
  /\ lastHash' = NextHash(lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [account |-> PublicKey, prev |-> NoHash, typ |-> "send", amount |-> amount, recipient |-> PublicKey, representative |-> PublicKey, signer |-> privateKey]]]
  /\ received' = [m \in Node |-> @ \cup {lastHash}]

CreateOpenBlock(n, privateKey) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = NextHash(lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [account |-> PublicKey, prev |-> NoHash, typ |-> "open", amount |-> 0, recipient |-> PublicKey, representative |-> PublicKey, signer |-> privateKey]]]
  /\ received' = [m \in Node |-> @ \cup {lastHash}]

CreateReceiveBlock(n, privateKey, amount, recipient) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = NextHash(lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [account |-> PublicKey, prev |-> NoHash, typ |-> "receive", amount |-> amount, recipient |-> PublicKey, representative |-> PublicKey, signer |-> privateKey]]]
  /\ received' = [m \in Node |-> @ \cup {lastHash}]

CreateChangeBlock(n, privateKey) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = NextHash(lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [account |-> PublicKey, prev |-> NoHash, typ |-> "change", amount |-> 0, recipient |-> PublicKey, representative |-> PublicKey, signer |-> privateKey]]]
  /\ received' = [m \in Node |-> @ \cup {lastHash}]

ValidateReceivedBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] # NoBlockVal
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = ledger[n][h]]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E privateKey \in PrivateKey : CreateGenesisBlock(privateKey)
  \/ \E n \in Node, privateKey \in PrivateKey, amount \in Nat, recipient \in PublicKey : CreateSendBlock(n, privateKey, amount, recipient)
  \/ \E n \in Node, privateKey \in PrivateKey : CreateOpenBlock(n, privateKey)
  \/ \E n \in Node, privateKey \in PrivateKey, amount \in Nat, recipient \in PublicKey : CreateReceiveBlock(n, privateKey, amount, recipient)
  \/ \E n \in Node, privateKey \in PrivateKey : CreateChangeBlock(n, privateKey)
  \/ \E n \in Node, h \in Hash : ValidateReceivedBlock(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
  \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => CalculateHashImpl(ledger[n][h].signer, h, ledger[n][h]) = h

====