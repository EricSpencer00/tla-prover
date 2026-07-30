---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal,
  PrivateKey, PublicKey,
  Node, GenesisBalance,
  NoBlockVal, NoHash

\* CalculateHashImpl is a bounded implementation substituted for CalculateHash by the .cfg;
\* the spec itself only requires it to exist as a total operator returning a Hash.
\* It is modelled as a constant function from block data and the previous hash.
CalculateHash == CalculateHashImpl

VARIABLES
  lastHash, ledger, received

vars == << lastHash, ledger, received >>

\* A block is always on some node's chain, which means there is a unique account
\* on whose chain it sits. The account is the node that owns the private key that
\* produced its signature.
AccountOfBlock(b) == CHOOSE n \in Node :
                         \E k \in PrivateKey : b.pubKey = NodeKey[n]

PrevHashOf(b) == IF b.blockType \in {"send", "receive"} THEN b.prevHash ELSE NoHash

\* The chain state is a linked list of blocks, so walking it recurses on the
\* previous hash. The genesis block has no predecessor.
SumOfChain(n, h) ==
  IF h = NoHashVal THEN 0
  ELSE LET b == ledger[n][h] IN b.amount + SumOfChain(n, PrevHashOf(b))

AccountBalance(n) == SumOfChain(n, lastHash)

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> PrivateKey \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash("genesis", NoHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = k]]
  /\ received' = [n \in Node |-> [h \in Hash |-> IF h = lastHash' THEN {h} ELSE {}]]

CreateSendBlock(k, amt) ==
  /\ lastHash # NoHashVal
  /\ AccountBalance(NodeOf(k)) >= amt
  /\ lastHash' = CalculateHash("send", lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = k]]
  /\ received' = [n \in Node |-> [received[n] EXCEPT ![lastHash'] = {lastHash'}]]

CreateOpenBlock(k, h) ==
  /\ ledger[NodeOf(k)][lastHash] # NoBlockVal
  /\ h \in ledger[NodeOf(k)]
  /\ ledger[NodeOf(k)][h] # NoBlockVal
  /\ lastHash' = CalculateHash("open", lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = k]]
  /\ received' = [n \in Node |-> [received[n] EXCEPT ![lastHash'] = {lastHash'}]]

CreateReceiveBlock(k, h) ==
  /\ ledger[NodeOf(k)][lastHash] # NoBlockVal
  /\ h \in ledger[NodeOf(k)]
  /\ ledger[NodeOf(k)][h] # NoBlockVal
  /\ lastHash' = CalculateHash("receive", lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = k]]
  /\ received' = [n \in Node |-> [received[n] EXCEPT ![lastHash'] = {lastHash'}]]

CreateChangeRepBlock(k) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash("changeRep", lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = k]]
  /\ received' = [n \in Node |-> [received[n] EXCEPT ![lastHash'] = {lastHash'}]]

ProcessBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ \E k \in PrivateKey : ledger[n][h] = k
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED << lastHash, ledger >>

Next ==
  \/ \E n \in Node, h \in Hash : ProcessBlock(n, h)
  \/ \E k \in PrivateKey : CreateGenesisBlock(k) \/ CreateChangeRepBlock(k)
  \/ \E k \in PrivateKey, amt \in 0..GenesisBalance : CreateSendBlock(k, amt)
  \/ \E k \in PrivateKey, h \in Hash : CreateOpenBlock(k, h) \/ CreateReceiveBlock(k, h)

Spec == Init /\ [][Next]_vars

\* Cryptographic correctness: every block recorded by every node carries a
\* signature that matches the public key of the account chain it lives on.
SignatureValid(n, h) ==
  /\ ledger[n][h] # NoBlockVal
  /\ LedgerKey[n] = NodeKey[AccountOfBlock(ledger[n][h])]

LedgerKey == [n \in Node |-> CHOOSE k \in PublicKey : \E pk \in PrivateKey : NodeOf(pk) = n /\ k = PrivateKeyToPublic[pk]]

SafetyInvariant == \A n \in Node, h \in Hash : SignatureValid(n, h)

====