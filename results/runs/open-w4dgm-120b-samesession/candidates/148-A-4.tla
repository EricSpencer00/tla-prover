---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Hashes are opaque identifiers; CalculateHash is the cryptographic hash
\* function mapping a block's contents and its predecessor's hash to the next.
\* NoHash starts the genesis chain.

VARIABLES lastHash, ledgerByNode, receivedByNode

vars == <<lastHash, ledgerByNode, receivedByNode>>

Block == [who: PublicKey, prev: Hash \cup {NoHash}, amt: Nat, kind: {"genesis", "send", "open", "receive", "change"}, recv: PublicKey \cup {"self"}, sig: PrivateKey \cup {NoBlock}]

ChainOf(a) == CHOOSE h \in Hash : ledgerByNode[CHOOSE n \in Node : TRUE][h] # NoBlockVal /\ ledgerByNode[CHOOSE n \in Node : TRUE][h].who = a

BalanceOf(a) ==
  LET Walk(_ts) ==
        IF _ts = <<>> THEN 0
        ELSE LET h == Head(_ts) IN LET blk == ledgerByNode[CHOOSE n \in Node : TRUE][h] IN
             (IF blk.kind = "send" THEN -blk.amt ELSE IF blk.kind = "receive" THEN blk.amt ELSE 0) + Walk(Tail(_ts))
  IN Walk(ChainHashes(a))

ChainHashes(a) ==
  LET Walk(h) ==
        IF h = NoHash THEN <<>>
        ELSE LET blk == ledgerByNode[CHOOSE n \in Node : TRUE][h] IN <<h>> \o Walk(blk.prev)
  IN IF \E h \in Hash : ledgerByNode[CHOOSE n \in Node : TRUE][h] # NoBlockVal /\ ledgerByNode[CHOOSE n \in Node : TRUE][h].who = a THEN Walk(ChainOf(a)) ELSE <<>>

Init ==
  /\ lastHash = NoHash
  /\ ledgerByNode = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ receivedByNode = [n \in Node |-> {}]

\* Genesis: the initial block is broadcast to all nodes at once and can only
\* ever be produced once, at the start of the chain.
CreateGenesisBlock(k) ==
  /\ lastHash = NoHash
  /\ ledgerByNode' = [n \in Node |-> [ledgerByNode[n] EXCEPT ![NoHash] = [who |-> PrivateKey[k], prev |-> NoHash, amt |-> GenesisBalance, kind |-> "genesis", recv |-> "self", sig |-> k]]]
  /\ lastHash' = NoHash
  /\ receivedByNode' = [n \in Node |-> {NoBlock}]
  /\ UNCHANGED <<>>

CreateSendBlock(n, k, a, r) ==
  /\ a > 0
  /\ BalanceOf(PrivateKey[k]) >= a
  /\ LET h == CalculateHash([who |-> PrivateKey[k], prev |-> lastHash, amt |-> a, kind |-> "send", recv |-> r, sig |-> k])
     IN /\ lastHash' = h
        /\ ledgerByNode' = [ledgerByNode EXCEPT ![n][h] = [who |-> PrivateKey[k], prev |-> lastHash, amt |-> a, kind |-> "send", recv |-> r, sig |-> k]]
        /\ receivedByNode' = [receivedByNode EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED <<>>

CreateOpenBlock(n, k, h) ==
  /\ ledgerByNode[n][h] # NoBlockVal
  /\ ledgerByNode[n][h].kind = "send"
  /\ ledgerByNode[n][h].recv = PrivateKey[k]
  /\ ChainOf(PrivateKey[k]) = NoHash
  /\ LET blockHash == CalculateHash([who |-> PrivateKey[k], prev |-> NoHash, amt |-> ledgerByNode[n][h].amt, kind |-> "open", recv |-> h, sig |-> k])
     IN /\ lastHash' = blockHash
        /\ ledgerByNode' = [ledgerByNode EXCEPT ![n][blockHash] = [who |-> PrivateKey[k], prev |-> NoHash, amt |-> ledgerByNode[n][h].amt, kind |-> "open", recv |-> h, sig |-> k]]
        /\ receivedByNode' = [receivedByNode EXCEPT ![n] = @ \cup {blockHash}]
  /\ UNCHANGED <<>>

CreateReceiveBlock(n, k, h) ==
  /\ ledgerByNode[n][h] # NoBlockVal
  /\ ledgerByNode[n][h].kind = "send"
  /\ ledgerByNode[n][h].recv = PrivateKey[k]
  /\ ChainOf(PrivateKey[k]) # NoHash
  /\ LET blockHash == CalculateHash([who |-> PrivateKey[k], prev |-> ChainOf(PrivateKey[k]), amt |-> ledgerByNode[n][h].amt, kind |-> "receive", recv |-> h, sig |-> k])
     IN /\ lastHash' = blockHash
        /\ ledgerByNode' = [ledgerByNode EXCEPT ![n][blockHash] = [who |-> PrivateKey[k], prev |-> ChainOf(PrivateKey[k]), amt |-> ledgerByNode[n][h].amt, kind |-> "receive", recv |-> h, sig |-> k]]
        /\ receivedByNode' = [receivedByNode EXCEPT ![n] = @ \cup {blockHash}]
  /\ UNCHANGED <<>>

CreateChangeRepresentativeBlock(n, k) ==
  /\ ChainOf(PrivateKey[k]) # NoHash
  /\ LET h == CalculateHash([who |-> PrivateKey[k], prev |-> ChainOf(PrivateKey[k]), amt |-> 0, kind |-> "change", recv |-> "self", sig |-> k])
     IN /\ lastHash' = h
        /\ ledgerByNode' = [ledgerByNode EXCEPT ![n][h] = [who |-> PrivateKey[k], prev |-> ChainOf(PrivateKey[k]), amt |-> 0, kind |-> "change", recv |-> "self", sig |-> k]]
        /\ receivedByNode' = [receivedByNode EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED <<>>

ValidateBlock(n, h) ==
  /\ h \in receivedByNode[n]
  /\ ledgerByNode[n][h] = NoBlockVal
  /\ LET blk == ledgerByNode[CHOOSE m \in Node : TRUE][h] IN
       /\ ledgerByNode' = [ledgerByNode EXCEPT ![n][h] = blk]
        /\ receivedByNode' = [receivedByNode EXCEPT ![n] = @ \ {h}]
        /\ UNCHANGED <<lastHash>>
  /\ UNCHANGED <<>>

DiscardBlock(n, h) ==
  /\ h \in receivedByNode[n]
  /\ ledgerByNode' = [ledgerByNode EXCEPT ![n] = @ \ {h}]
  /\ receivedByNode' = [receivedByNode EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E k \in PrivateKey : CreateGenesisBlock(k)
  \/ \E n \in Node, k \in PrivateKey, a \in 1..GenesisBalance, r \in PublicKey \cup {NoHash} : CreateSendBlock(n, k, a, r)
  \/ \E n \in Node, k \in PrivateKey, h \in Hash : CreateOpenBlock(n, k, h)
  \/ \E n \in Node, k \in PrivateKey, h \in Hash : CreateReceiveBlock(n, k, h)
  \/ \E n \in Node, k \in PrivateKey : CreateChangeRepresentativeBlock(n, k)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)
  \/ \E n \in Node, h \in Hash : DiscardBlock(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledgerByNode \in [Node -> [Hash -> [who: PublicKey, prev: Hash \cup {NoHash}, amt: Nat, kind: {"genesis", "send", "open", "receive", "change"}, recv: PublicKey \cup {"self"}, sig: PrivateKey \cup {NoBlock}]]]
  /\ receivedByNode \in [Node -> SUBSET Hash]

\* Every block present in any node's ledger must carry a matching signature.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    (ledgerByNode[n][h] # NoBlockVal) => ledgerByNode[n][h].sig = PrivateKey[ledgerByNode[n][h].who]

====