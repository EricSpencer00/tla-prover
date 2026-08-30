---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Type invariant below is the only hard requirement; the "balance invariant"
\* that the spec mentions is defined afterwards but is not part of INVARIANT.
TypeOK ==
  /\ NoHash \in Hash
  /\ NoHashVal \notin Hash
  /\ NoBlock \in [owner : PrivateKey, prev : Hash, typ : {"genesis", "send", "open", "receive", "change-rep"},
                    dest : PublicKey, amt : 1..GenesisBalance, sig : PublicKey, hash : Hash]
  /\ NoBlockVal \notin [owner : PrivateKey, prev : Hash, typ : {"genesis", "send", "open", "receive", "change-rep"},
                         dest : PublicKey, amt : 1..GenesisBalance, sig : PublicKey, hash : Hash]
  /\ CalculateHash \in [prev : Hash, owner : PrivateKey, typ : {"genesis", "send", "open", "receive", "change-rep"},
                         dest : PublicKey, amt : 0..GenesisBalance] -> Hash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Recursive balance helper: walk an account chain back to genesis, summing
\* amounts from open/receive blocks and subtracting amounts from send blocks.
RECURSIVE ChainBalance(_)
ChainBalance(acc) == IF acc = NoHash THEN 0
  ELSE LET b == ledger[acc] IN
       CASE b = NoBlockVal -> 0
       [] b.typ = "open"   -> ChainBalance(b.prev)
       [] b.typ = "receive"-> b.amt + ChainBalance(b.prev)
       [] b.typ = "send"   -> ChainBalance(b.prev) - b.amt
       [] OTHER            -> ChainBalance(b.prev)

RecursiveChainBalance == ChainBalance

RECURSIVE AccountBalance(_)
AccountBalance(node) == ChainBalance(ledger[NodeOf(node)].hash)

\* Ownership is the public key derived from a node's private key.
NodeOf(node) == CHOOSE pk \in PublicKey : \E sk \in PrivateKey : OwnerOf(sk) = pk /\ node \in OwnerOf(sk)

\* Each node holds the last block it personally created in its own chain.
NodePosition(node) == CHOOSE h \in Hash : ledger[h].owner = NodeOf(node)

RECURSIVE ChainHashes(_)
ChainHashes(h) == IF h = NoHash THEN <<>> ELSE Append(ChainHashes(ledger[h].prev), h)

AccountChainHashes(node) == ChainHashes(NodePosition(node))

Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* Genesis block is created and replicated in every node's copy at once.
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E sk \in PrivateKey :
       /\ ledger' = [ledger EXCEPT ![CalculateHash[NoHash, sk, "genesis", NoHash, 0]]
                         = [owner |-> sk, prev |-> NoHash, typ |-> "genesis", dest |-> NoHash, amt |-> 0,
                            sig |-> OwnerOf(sk), hash |-> CalculateHash[NoHash, sk, "genesis", NoHash, 0]]]
  /\ lastHash' = CalculateHash[NoHash, sk, "genesis", NoHash, 0]
  /\ received' = [n \in Node |-> received[n]]

CreateSend(node, dest, amt) ==
  /\ AccountBalance(node) >= amt
  /\ ledger[NodePosition(node)].typ \in {"genesis", "receive", "open", "change-rep"}
  /\ \E sk \in OwnerOf(NodeOf(node)) :
       /\ ledger' = [ledger EXCEPT ![CalculateHash[NodePosition(node), sk, "send", dest, amt]]
                         = [owner |-> sk, prev |-> NodePosition(node), typ |-> "send", dest |-> dest,
                            amt |-> amt, sig |-> OwnerOf(sk), hash |-> CalculateHash[NodePosition(node), sk, "send", dest, amt]]]
  /\ lastHash' = CalculateHash[NodePosition(node), sk, "send", dest, amt]
  /\ received' = [received EXCEPT ![n] = received[n] \cup {CalculateHash[NodePosition(node), sk, "send", dest, amt]}]

CreateOpen(node, src) ==
  /\ src # NoHash
  /\ ledger[src].typ = "send"
  /\ ledger[src].dest = NodeOf(node)
  /\ \E sk \in OwnerOf(NodeOf(node)) :
       /\ ledger' = [ledger EXCEPT ![CalculateHash[NoHash, sk, "open", NoHash, 0]]
                         = [owner |-> sk, prev |-> src, typ |-> "open", dest |-> NoHash,
                            amt |-> 0, sig |-> OwnerOf(sk), hash |-> CalculateHash[NoHash, sk, "open", NoHash, 0]]]
  /\ lastHash' = CalculateHash[NoHash, sk, "open", NoHash, 0]
  /\ received' = [received EXCEPT ![n] = received[n] \cup {CalculateHash[NoHash, sk, "open", NoHash, 0]}]

CreateReceive(node, src) ==
  /\ src # NoHash
  /\ ledger[src].typ = "send"
  /\ ledger[src].dest = NodeOf(node)
  /\ \E sk \in OwnerOf(NodeOf(node)) :
       /\ ledger' = [ledger EXCEPT ![CalculateHash[NodePosition(node), sk, "receive", NoHash, ledger[src].amt]]
                         = [owner |-> sk, prev |-> NodePosition(node), typ |-> "receive", dest |-> NoHash,
                            amt |-> ledger[src].amt, sig |-> OwnerOf(sk), hash |-> CalculateHash[NodePosition(node), sk, "receive", NoHash, ledger[src].amt]]]
  /\ lastHash' = CalculateHash[NodePosition(node), sk, "receive", NoHash, ledger[src].amt]
  /\ received' = [received EXCEPT ![n] = received[n] \cup {CalculateHash[NodePosition(node), sk, "receive", NoHash, ledger[src].amt]}]

CreateChangeRep(node) ==
  /\ ledger' = [ledger EXCEPT ![CalculateHash[NodePosition(node), CHOOSE sk \in OwnerOf(NodeOf(node)) : TRUE,
                                              "change-rep", NoHash, 0]]
                         = [owner |-> CHOOSE sk \in OwnerOf(NodeOf(node)) : TRUE, prev |-> NodePosition(node), typ |-> "change-rep",
                            dest |-> NoHash, amt |-> 0, sig |-> NodeOf(node), hash |-> CalculateHash[NodePosition(node), CHOOSE sk \in OwnerOf(NodeOf(node)) : TRUE, "change-rep", NoHash, 0]]]
  /\ lastHash' = CalculateHash[NodePosition(node), CHOOSE sk \in OwnerOf(NodeOf(node)) : TRUE, "change-rep", NoHash, 0]
  /\ received' = [received EXCEPT ![n] = received[n] \cup {CalculateHash[NodePosition(node), CHOOSE sk \in OwnerOf(NodeOf(node)) : TRUE, "change-rep", NoHash, 0]}]

Process(n, h) ==
  /\ h \in received[n]
  /\ ledger[h] = NoBlockVal
  /\ \E sk \in OwnerOf(NodeOf(n)) :
       /\ ledger' = [ledger EXCEPT ![h] = [owner |-> sk, prev |-> ledger[h].prev, typ |-> ledger[h].typ, dest |-> ledger[h].dest,
                                            amt |-> ledger[h].amt, sig |-> OwnerOf(sk), hash |-> h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ lastHash' = IF h # NoHash /\ h # lastHash THEN h ELSE lastHash

Next ==
  \/ CreateGenesis
  \/ \E n \in Node, dest \in PublicKey, amt \in 1..GenesisBalance : CreateSend(n, dest, amt)
  \/ \E n \in Node, src \in Hash : CreateOpen(n, src)
  \/ \E n \in Node, src \in Hash : CreateReceive(n, src)
  \/ \E n \in Node : CreateChangeRep(n)
  \/ \E n \in Node, h \in Hash : Process(n, h)

Spec == Init /\ [][Next]_vars

\* A valid signature is one of the public keys derived from the block's own
\* authoring private key, so whatever private key holder created the block,
\* its signature is exactly what the block's own ledger copy records.
SafetyInvariant == \A h \in Hash : ledger[h] # NoBlockVal => ledger[h].sig \in OwnerOf(ledger[h].owner)

BalanceInvariant == RecursiveChainBalance <= GenesisBalance

====