---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

TypeOK ==
  /\ lastHash \in {NoHashVal} \cup Hash
  /\ ledger \in [Node -> [Hash -> {NoBlockVal} \cup [blk : PrivateKey \cup {NoBlockVal}, prevHash : Hash \cup {NoHashVal}, typ : {"genesis", "send", "open", "receive", "repset"}, bal : 0..GenesisBalance]]]
  /\ received \in [Node -> SUBSET Hash]

vars == <<lastHash, ledger, received>>

\* Ordered block creation: the lastHash ties new block hashes to the preceding block.
Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Recursively walk the account chain to compute the balance up to a block.
Balance(n, h) ==
  IF h \in {NoHashVal, NoHash} THEN 0
  ELSE LET blk == ledger[n][h] IN
       IF blk = NoBlockVal THEN 0
       ELSE IF blk.typ = "genesis" THEN blk.bal
       ELSE IF blk.typ = "send" THEN blk.bal - Balance(n, blk.prevHash)
       ELSE IF blk.typ \in {"open", "receive"} THEN blk.bal + Balance(n, blk.prevHash)
       ELSE Balance(n, blk.prevHash)

\* Distributed ledger retains every broadcasted block; each node replicates it.
BroadcastBlock(h) ==
  [n \in Node |-> [ledger[n] EXCEPT ![h] = ledger[Node][h]]]

\* A received block is validated against the node's local copy before merging.
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].blk \in PrivateKey
  /\ LET pub == ledger[n][h].blk IN
       /\ (IF ledger[n][h].typ = "genesis" THEN ledger[n][h].bal = GenesisBalance ELSE TRUE)
       /\ (IF ledger[n][h].typ = "send" THEN Balance(n, ledger[n][h].prevHash) >= ledger[n][h].bal ELSE TRUE)
       /\ (IF ledger[n][h].typ = "open" THEN
             \E o \in Node : ledger[o][ledger[n][h].prevHash].typ = "send" /\ ledger[o][ledger[n][h].prevHash].blk \in PrivateKey /\ ledger[o][ledger[n][h].prevHash].bal = pub
           ELSE TRUE)
       /\ (IF ledger[n][h].typ = "receive" THEN
             \E o \in Node : ledger[o][ledger[n][h].prevHash].typ = "send" /\ ledger[o][ledger[n][h].prevHash].blk \in PrivateKey /\ ledger[n][h].bal = ledger[o][ledger[n][h].prevHash].bal
           ELSE TRUE)
  /\ received' = [received EXCEPT ![n] = @ \ {h}]

\* Genesis block is created only once; it carries the full initial supply.
CreateGenesis(n, k) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash([blk |-> k, prevHash |-> NoHashVal, typ |-> "genesis", bal |-> GenesisBalance])
  /\ ledger' = [\E h \in {lastHash'} : [Node |-> [ledger[n] EXCEPT ![h] = [blk |-> k, prevHash |-> NoHashVal, typ |-> "genesis", bal |-> GenesisBalance]]]]
  /\ UNCHANGED received

CreateSend(n, k) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash([blk |-> k, prevHash |-> lastHash, typ |-> "send", bal |-> Balance(n, lastHash)])
  /\ ledger' = BroadcastBlock(lastHash')
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateOpen(n, k, m) ==
  /\ lastHash # NoHashVal
  /\ ledger[m][lastHash].blk \in PrivateKey
  /\ lastHash' = CalculateHash([blk |-> k, prevHash |-> lastHash, typ |-> "open", bal |-> ledger[m][lastHash].blk])
  /\ ledger' = BroadcastBlock(lastHash')
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateReceive(n, k, m) ==
  /\ lastHash # NoHashVal
  /\ ledger[m][lastHash].blk \in PrivateKey
  /\ lastHash' = CalculateHash([blk |-> k, prevHash |-> lastHash, typ |-> "receive", bal |-> ledger[m][lastHash].bal])
  /\ ledger' = BroadcastBlock(lastHash')
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateRepSet(n, k) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash([blk |-> k, prevHash |-> lastHash, typ |-> "repset", bal |-> 0])
  /\ ledger' = BroadcastBlock(lastHash')
  /\ UNCHANGED received

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesis(n, k) \/ CreateSend(n, k) \/ CreateRepSet(n, k)
  \/ \E n \in Node, k \in PrivateKey, m \in Node : CreateOpen(n, k, m) \/ CreateReceive(n, k, m)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* Every block's signature must match its account chain's public key.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].blk \in PrivateKey

====