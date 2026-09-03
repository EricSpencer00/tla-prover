---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES
    lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Recursive balance extraction: walks the account chain backward from the
\* supplied hash, summing the amounts left in each block along the way.
RECURSIVE Balance(_)
Balance(h) ==
    IF h = NoHash THEN 0
    ELSE IF ledger[NoHash][h] # NoBlockVal THEN ledger[NoHash][h].amount + Balance(ledger[NoHash][h].prevHash)
    ELSE Balance(h)

\* Sum of balances of a set of accounts, derived from the recursive Balance.
RECURSIVE BalanceOf(_)
BalanceOf(A) ==
    IF A = {} THEN 0
    ELSE LET a == CHOOSE x \in A : TRUE
         IN Balance(a) + BalanceOf(A \ {a})

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> [hash: Hash, signer: PublicKey, typ: {"genesis", "send", "open", "receive", "change"}, amount: 0..GenesisBalance, dest: PrivateKey \cup {NoHash}, prevHash: Hash \cup {NoHash}, recvHash: Hash \cup {NoHash}]]]
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
    /\ lastHash = NoHashVal
    /\ lastHash' = CalculateHash(k, NoHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [hash |-> lastHash, signer |-> k, typ |-> "genesis", amount |-> GenesisBalance, dest |-> NoHash, prevHash |-> NoHash, recvHash |-> NoHash]]]
    /\ UNCHANGED received

CreateSendBlock(n, k, amt, d) ==
    /\ lastHash # NoHashVal
    /\ Balance(lastHash) >= amt
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [hash |-> lastHash, signer |-> k, typ |-> "send", amount |-> amt, dest |-> d, prevHash |-> lastHash, recvHash |-> NoHash]]
    /\ received' = [m \in Node |-> received[m] \cup {lastHash'}]

CreateOpenBlock(n, k, d, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] # NoBlockVal
    /\ ledger[n][h].dest = d
    /\ h \notin {ledger[n][x].recvHash : x \in Hash}
    /\ lastHash # NoHashVal
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [hash |-> lastHash, signer |-> k, typ |-> "open", amount |-> 0, dest |-> NoHash, prevHash |-> NoHash, recvHash |-> h]]
    /\ received' = [received EXCEPT ![n] = @ \ {h}]

CreateChangeRepBlock(n, k) ==
    /\ lastHash # NoHashVal
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [hash |-> lastHash, signer |-> k, typ |-> "change", amount |-> 0, dest |-> NoHash, prevHash |-> lastHash, recvHash |-> NoHash]]
    /\ UNCHANGED received

CreateReceiveBlock(n, k, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] # NoBlockVal
    /\ ledger[n][h].typ = "send"
    /\ h \notin {ledger[n][x].recvHash : x \in Hash}
    /\ lastHash # NoHashVal
    /\ lastHash' = CalculateHash(k, lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [hash |-> lastHash, signer |-> k, typ |-> "receive", amount |-> 0, dest |-> NoHash, prevHash |-> lastHash, recvHash |-> h]]
    /\ received' = [received EXCEPT ![n] = @ \ {h}]

\* Resolve a block in transit by validating it against the node's local ledger copy.
ValidateBlock(n, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] # NoBlockVal
    /\ ledger[n][h].signer = PrivateKey[PublicKey]
    /\ ledger[n][ledger[n][h].prevHash] # NoBlockVal
    /\ (IF ledger[n][h].typ = "send" THEN Balance(ledger[n][h].prevHash) >= ledger[n][h].amount ELSE TRUE)
    /\ (IF ledger[n][h].typ = "open" THEN ledger[n][h].recvHash \notin {ledger[n][x].recvHash : x \in Hash} ELSE TRUE)
    /\ (IF ledger[n][h].typ = "receive" THEN ledger[n][h].recvHash \notin {ledger[n][x].recvHash : x \in Hash} ELSE TRUE)
    /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ \E k \in PrivateKey: CreateGenesisBlock(k)
    \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, d \in PrivateKey: CreateSendBlock(n, k, amt, d)
    \/ \E n \in Node, k \in PrivateKey, d \in PrivateKey, h \in Hash: CreateOpenBlock(n, k, d, h)
    \/ \E n \in Node, k \in PrivateKey: CreateChangeRepBlock(n, k)
    \/ \E n \in Node, k \in PrivateKey, h \in Hash: CreateReceiveBlock(n, k, h)
    \/ \E n \in Node, h \in Hash: ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must carry a signature that matches the
\* public key of the account whose chain the block sits in.
SafetyInvariant ==
    \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].signer = PrivateKey[PublicKey]

====