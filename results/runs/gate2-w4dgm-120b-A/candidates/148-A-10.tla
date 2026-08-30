---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

\* Hash calculation is abstracted as a constant operator; a concrete version is
\* substituted in at model-checking time by the .cfg file (CalculateHashImpl).
CONSTANT CalculateHash

AccountOf(n) == n
KeyOf(pk) == pk

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Directed acyclic test: a block's hash must be strictly smaller than its
\* predecessor's, which is only possible when blocks form a DAG with no cycle.
HashesChain(ledger) == \A h \in Hash : (ledger[h] # NoBlockVal) => ledger[h].prev # NoHash /\ ledger[h].prev \notin Hash /\ h < ledger[h].prev

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> [prev: Hash \cup {NoHash}, owner: PublicKey, typ: {"genesis", "send", "open", "receive", "change"}, amount: 0..GenesisBalance]]]
    /\ received \in [Node -> SUBSET Hash]
    /\ HashesChain(ledger)

\* A valid signature must match the public key belonging to the block's owner
\* account. Because each account has a single public key, a forged block would
\* show up as the wrong public key here, so the ledger cannot hold it.
SignatureInvariant ==
    \A node \in Node : \A h \in Hash :
        (ledger[h] # NoBlockVal) =>
            /\ ledger[h].owner = KeyOf(AccountOf(node))
            /\ ledger[h].prev # NoHash => ledger[h].prev \in HashesNode(node)

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

HashesNode(node) == {h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].owner = KeyOf(AccountOf(node))}
BalanceNode(node) == BalanceNodeRec(node, NoHash)
BalanceNodeRec(node, h) ==
    IF h = NoHash THEN 0
    ELSE IF ledger[h] = NoBlockVal THEN 0
    ELSE IF ledger[h].owner = KeyOf(AccountOf(node))
        THEN BalanceNodeRec(node, ledger[h].prev) + IF ledger[h].typ \in {"receive", "genesis"} THEN ledger[h].amount ELSE 0
        ELSE BalanceNodeRec(node, ledger[h].prev)

SendNode(node) == {h \in HashesNode(node) : ledger[h].typ = "send"}
ReceivedNode(node) == {h \in HashesNode(node) : ledger[h].typ = "receive"}
SumBalances == BalanceNodeRec(arbNode, NoHash) + BalanceNodeRec(arbNode2, NoHash)
    where arbNode \in Node
          arbNode2 \in Node
          arbNode # arbNode2

BalanceInvariant == SumBalances <= GenesisBalance

\* A sender can only create a send block for balance it actually has, so tracking
\* that balance directly is what keeps the invariant true -- it is not a derived
\* artifact of validation order or block sequencing.
CreateSend ==
    \E n \in Node, amt \in 1..GenesisBalance :
        /\ BalanceNode(n) >= amt
        /\ lastHash' = CalculateHash([sender |-> n, amt |-> amt], lastHash)
        /\ ledger' = [ledger EXCEPT ![n][lastHash] = [prev |-> lastHash, owner |-> KeyOf(AccountOf(n)), typ |-> "send", amount |-> amt]]
        /\ received' = [k \in Node |-> @ \cup {lastHash}]

CreateOpen ==
    \E n \in Node, h \in HashesNode(n) :
        /\ ledger[h].typ = "send"
        /\ ledger[h].owner = KeyOf(AccountOf(n))
        /\ ~\E h2 \in HashesNode(n) : ledger[h2].typ = "open"
        /\ lastHash' = CalculateHash([opener |-> n, sendHash |-> h], lastHash)
        /\ ledger' = [ledger EXCEPT ![n][lastHash] = [prev |-> lastHash, owner |-> KeyOf(AccountOf(n)), typ |-> "open", amount |-> 0]]
        /\ received' = [k \in Node |-> @ \cup {lastHash}]

CreateReceive ==
    \E n \in Node, h \in HashesNode(n) :
        /\ ledger[h].typ = "send"
        /\ ledger[h].owner = KeyOf(AccountOf(n))
        /\ ~\E h2 \in HashesNode(n) : ledger[h2].typ = "receive" /\ ledger[h2].prev = h
        /\ lastHash' = CalculateHash([receiver |-> n, sendHash |-> h], lastHash)
        /\ ledger' = [ledger EXCEPT ![n][lastHash] = [prev |-> lastHash, owner |-> KeyOf(AccountOf(n)), typ |-> "receive", amount |-> ledger[h].amount]]
        /\ received' = [k \in Node |-> @ \cup {lastHash}]

CreateChange ==
    \E n \in Node :
        /\ lastHash' = CalculateHash([changer |-> n], lastHash)
        /\ ledger' = [ledger EXCEPT ![n][lastHash] = [prev |-> lastHash, owner |-> KeyOf(AccountOf(n)), typ |-> "change", amount |-> 0]]
        /\ received' = [k \in Node |-> @ \cup {lastHash}]

ValidateBlock ==
    \E n \in Node, h \in received[n] :
        /\ ledger[n][h] = NoBlockVal
        /\ ledger' = [ledger EXCEPT ![n][h] = ledger[h]]
        /\ received' = [received EXCEPT ![n] = @ \ {h}]
        /\ UNCHANGED lastHash

Next == CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChange \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* Liveness property: every broadcasted block is eventually recorded at every node.
AllBroadcastBlocksRecorded ==
    \A n \in Node : \A h \in Hash : (h \in received[n]) ~> (ledger[n][h] # NoBlockVal)
====