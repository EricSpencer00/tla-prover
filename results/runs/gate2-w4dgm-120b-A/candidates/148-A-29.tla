---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME /\ NoHash \notin Hash
       /\ NoBlock \notin [hash: Hash \cup {NoHash}, owner: PublicKey, typ: {"genesis", "send", "open", "receive", "change"}, prev: Hash \cup {NoHash}, ref: Hash \cup {NoHash}, amt: 0..GenesisBalance]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Typify == [hash: Hash \cup {NoHash}, owner: PublicKey, typ: {"genesis", "send", "open", "receive", "change"}, prev: Hash \cup {NoHash}, ref: Hash \cup {NoHash}, amt: 0..GenesisBalance]
NodeLedger(n) == ledger[n]
Chain(n) == {NodeLedger(n)[h] : h \in Hash} \ {NoBlockVal}

RECURSIVE ChainBalance(_)
ChainBalance(n) == IF Chain(n) = {} THEN 0
                   ELSE LET b == CHOOSE x \in Chain(n) : TRUE
                        IN (IF b.typ = "genesis" THEN b.amt
                            ELSE IF b.typ = "send" THEN 0
                            ELSE IF b.typ = "open" THEN 0
                            ELSE IF b.typ = "receive" THEN b.amt
                            ELSE 0) + ChainBalance({x \in Chain(n) : x.hash # b.hash})

RECURSIVE ChainPrevious(_)
ChainPrevious(n) == IF Chain(n) = {} THEN NoHash
                    ELSE LET b == CHOOSE x \in Chain(n) : TRUE
                         IN b.prev

RECURSIVE ChainReferences(_)
ChainReferences(n) == IF Chain(n) = {} THEN {}
                       ELSE LET b == CHOOSE x \in Chain(n) : TRUE
                            IN {b.ref} \cup ChainReferences({x \in Chain(n) : x.hash # b.hash})

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Typify \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Typify]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

ValidateBlock(n, b) ==
  /\ b.typ \in {"genesis", "send", "open", "receive", "change"}
  /\ b.prev = ChainPrevious(n)
  /\ b.owner \in PublicKey
  /\ b.amt <= GenesisBalance
  /\ IF b.typ = "send" THEN b.amt <= ChainBalance(n) ELSE TRUE
  /\ IF b.typ = "open" THEN \E m \in Node : b.ref = ChainPrevious(m) /\ b.owner = {p \in PublicKey : \E k \in PrivateKey : OwnerOf(k) = p} /\ b.ref \notin ChainReferences(n) ELSE TRUE
  /\ IF b.typ = "receive" THEN b.ref \in ChainPrevious(n) ELSE TRUE

CreateGenesis(n, k) ==
  /\ lastHash = NoHash
  /\ \A m \in Node : \A h \in Hash : NodeLedger(m)[h] = NoBlockVal
  /\ LET h == CalculateHash("genesis", k, NoHash, NoHash, GenesisBalance)
     IN /\ lastHash' = h
        /\ ledger' = [m \in Node |-> [NodeLedger(m) EXCEPT ![h] = [hash |-> h, owner |-> OwnerOf(k), typ |-> "genesis", prev |-> NoHash, ref |-> NoHash, amt |-> GenesisBalance]]]
        /\ received' = [m \in Node |-> { [hash |-> h, owner |-> OwnerOf(k), typ |-> "genesis", prev |-> NoHash, ref |-> NoHash, amt |-> GenesisBalance] } \cup received[m]]

CreateSend(n, k, amt) ==
  /\ lastHash # NoHash
  /\ amt \in 1..GenesisBalance
  /\ LET h == CalculateHash("send", k, lastHash, NoHash, amt)
     IN /\ lastHash' = h
        /\ ledger' = [m \in Node |-> [NodeLedger(m) EXCEPT ![h] = [hash |-> h, owner |-> OwnerOf(k), typ |-> "send", prev |-> lastHash, ref |-> NoHash, amt |-> amt]]]
        /\ received' = [m \in Node |-> { [hash |-> h, owner |-> OwnerOf(k), typ |-> "send", prev |-> lastHash, ref |-> NoHash, amt |-> amt] } \cup received[m]]

CreateOpen(n, k, ref ==
  /\ lastHash # NoHash
  /\ LET h == CalculateHash("open", k, NoHash, ref, 0)
     IN /\ lastHash' = h
        /\ ledger' = [m \in Node |-> [NodeLedger(m) EXCEPT ![h] = [hash |-> h, owner |-> OwnerOf(k), typ |-> "open", prev |-> NoHash, ref |-> ref, amt |-> 0]]]
        /\ received' = [m \in Node |-> { [hash |-> h, owner |-> OwnerOf(k), typ |-> "open", prev |-> NoHash, ref |-> ref, amt |-> 0] } \cup received[m]]

CreateReceive(n, k, ref) ==
  /\ lastHash # NoHash
  /\ LET h == CalculateHash("receive", k, ChainPrevious(n), ref, 0)
     IN /\ lastHash' = h
        /\ ledger' = [m \in Node |-> [NodeLedger(m) EXCEPT ![h] = [hash |-> h, owner |-> OwnerOf(k), typ |-> "receive", prev |-> ChainPrevious(n), ref |-> ref, amt |-> 0]]]
        /\ received' = [m \in Node |-> { [hash |-> h, owner |-> OwnerOf(k), typ |-> "receive", prev |-> ChainPrevious(n), ref |-> ref, amt |-> 0] } \cup received[m]]

CreateChange(n, k) ==
  /\ lastHash # NoHash
  /\ LET h == CalculateHash("change", k, ChainPrevious(n), NoHash, 0)
     IN /\ lastHash' = h
        /\ ledger' = [m \in Node |-> [NodeLedger(m) EXCEPT ![h] = [hash |-> h, owner |-> OwnerOf(k), typ |-> "change", prev |-> ChainPrevious(n), ref |-> NoHash, amt |-> 0]]]
        /\ received' = [m \in Node |-> { [hash |-> h, owner |-> OwnerOf(k), typ |-> "change", prev |-> ChainPrevious(n), ref |-> NoHash, amt |-> 0] } \cup received[m]]

ProcessBlock(n, b) ==
  /\ b \in received[n]
  /\ \A h \in Hash : (NodeLedger(n)[h] = NoBlockVal) \/ (NodeLedger(n)[h].hash # b.hash)
  /\ ValidateBlock(n, b)
  /\ ledger' = [NodeLedger EXCEPT ![n][b.hash] = b]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesis(n, k)
  \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance : CreateSend(n, k, amt)
  \/ \E n \in Node, k \in PrivateKey, ref \in Hash : CreateOpen(n, k, ref) \/ CreateReceive(n, k, ref)
  \/ \E n \in Node, k \in PrivateKey : CreateChange(n, k)
  \/ \E n \in Node, b \in Typify : ProcessBlock(n, b)

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node : \A h \in Hash : (NodeLedger(n)[h] # NoBlockVal) => NodeLedger(n)[h].owner \in {OwnerOf(k) : k \in PrivateKey}

====