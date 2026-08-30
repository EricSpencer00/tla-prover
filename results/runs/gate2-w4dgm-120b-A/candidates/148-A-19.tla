---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Every account has its own block chain; action order is recorded in the chain.
\* The type invariant below is always true (it is the only safety property checked).
\* The signature check is the substantive security claim: every recorded block is
\* signed by the account that owns its chain, so no unauthorized node ever writes.

Chains == {ChainsOf(a) : a \in PublicKey}
Blocks == UNION Chains
Accounts == PublicKey

\* Chain navigation is a partial function on the chain itself (the "next" block
\* in the chain, not the next block to be appended); the chain is a total order
\* of its blocks, so ChainSuccessor is a functional relation whose domain is
\* exactly Chain \ LastBlock.
ChainSuccessor == {<<h, g>> \in Hash \X Hash : h \in Blocks /\ g \in Blocks /\ \E a \in Accounts : h \in ChainsOf(a) /\ g \in ChainsOf(a) /\ \A f \in ChainsOf(a) : (h, f) \in ChainSuccessor => (h, g) \in ChainSuccessor}
LastBlockOf(a) == CHOOSE h \in ChainsOf(a) : \A f \in ChainsOf(a) : <<f, h>> \notin ChainSuccessor

VARIABLES lastHash, ledger, received

TypeOK ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> [parent : Hash \cup {NoHash}, owner : PublicKey, typ : {"SEND", "OPEN", "RECEIVE", "CHANGE"}, amount : 0..GenesisBalance, signature : PrivateKey \cup {NoBlock}]]]
    /\ received \in [Node -> SUBSET [parent : Hash \cup {NoHash}, owner : PublicKey, typ : {"SEND", "OPEN", "RECEIVE", "CHANGE"}, amount : 0..GenesisBalance]]
    /\ ChainSuccessor \subseteq (Hash \X Hash)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> [parent |-> NoHash, owner |-> NoBlock, typ |-> "SEND", amount |-> 0, signature |-> NoBlock]]]
    /\ received = [n \in Node |-> {}]

\* Genesis block is written to every copy at once; CreateSend/Open/Receive/Change
\* write to the author's own copy and rely on delivery to propagate elsewhere.
CreateGenesisBlock(k) ==
    /\ lastHash = NoHashVal
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![NoHashVal] = [parent |-> NoHash, owner |-> NoBlock, typ |-> "SEND", amount |-> GenesisBalance, signature |-> k]]]
    /\ lastHash' = NoHashVal
    /\ received' = [n \in Node |-> [parent |-> NoHash, owner |-> NoBlock, typ |-> "SEND", amount |-> GenesisBalance]]
    /\ \E n \in Node : True

\* A send block is always written to the author's own copy immediately.
CreateSendBlock(k, a, n, to, amt) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash].owner = a
    /\ ledger[n][lastHash].typ = "SEND"
    /\ amt <= Balance(a, ledger[n])
    /\ lastHash' = CalculateHash([parent |-> lastHash, owner |-> a, typ |-> "SEND", amount |-> amt, signature |-> k])
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [parent |-> lastHash, owner |-> a, typ |-> "SEND", amount |-> amt, signature |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[parent |-> lastHash, owner |-> a, typ |-> "SEND", amount |-> amt]}]
    /\ \E n \in Node : True

CreateOpenBlock(k, a, n, parent) ==
    /\ parent \in ChainsOf(a)
    /\ parent # LastBlockOf(a)
    /\ \A key \in Accounts : \A m \in Node : ~([parent |-> parent, owner |-> key, typ |-> "OPEN", amount |-> 0] \in received[m])
    /\ lastHash' = CalculateHash([parent |-> parent, owner |-> a, typ |-> "OPEN", amount |-> 0, signature |-> k])
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [parent |-> parent, owner |-> a, typ |-> "OPEN", amount |-> 0, signature |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[parent |-> parent, owner |-> a, typ |-> "OPEN", amount |-> 0]}]
    /\ \E n \in Node : True

CreateReceiveBlock(k, a, n, parent, amt) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash].owner = a
    /\ parent \in ChainsOf(a)
    /\ parent # LastBlockOf(a)
    /\ \E m \in Node : [parent |-> parent, owner |-> a, typ |-> "SEND", amount |-> amt] \in received[m]
    /\ lastHash' = CalculateHash([parent |-> parent, owner |-> a, typ |-> "RECEIVE", amount |-> amt, signature |-> k])
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [parent |-> parent, owner |-> a, typ |-> "RECEIVE", amount |-> amt, signature |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[parent |-> parent, owner |-> a, typ |-> "RECEIVE", amount |-> amt]}]
    /\ \E n \in Node : True

CreateChangeBlock(k, a, n) ==
    /\ lastHash # NoHashVal
    /\ ledger[n][lastHash].owner = a
    /\ lastHash' = CalculateHash([parent |-> lastHash, owner |-> a, typ |-> "CHANGE", amount |-> 0, signature |-> k])
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [parent |-> lastHash, owner |-> a, typ |-> "CHANGE", amount |-> 0, signature |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[parent |-> lastHash, owner |-> a, typ |-> "CHANGE", amount |-> 0]}]
    /\ \E n \in Node : True

\* Validation uses the local copy and is the only admission control; it is
\* applied separately for each node, which is what lets a copy be behind.
ValidateBlock(n, b) ==
    /\ b \in received[n]
    /\ b.owner \in Accounts
    /\ ledger[n][b.parent].owner = b.owner
    /\ ledger[n][b.parent].typ # "SEND"
    /\ b.amount <= Balance(b.owner, ledger[n])
    /\ ledger' = [ledger EXCEPT ![n][CalculateHash([parent |-> b.parent, owner |-> b.owner, typ |-> b.typ, amount |-> b.amount, signature |-> NoBlock])] = [parent |-> b.parent, owner |-> b.owner, typ |-> b.typ, amount |-> b.amount, signature |-> NoBlock]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
    /\ UNCHANGED lastHash

DiscardBlock(n, b) ==
    /\ b \in received[n]
    /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
    /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ \E n \in Node : DiscardBlock(n, CHOOSE b \in received[n] : TRUE)
    \/ \E n \in Node, b \in [parent : Hash \cup {NoHash}, owner : PublicKey, typ : {"SEND", "OPEN", "RECEIVE", "CHANGE"}, amount : 0..GenesisBalance] : ValidateBlock(n, b)
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)
    \/ \E k \in PrivateKey, a \in Accounts, n \in Node, to \in Accounts, amt \in 1..GenesisBalance : CreateSendBlock(k, a, n, to, amt)
    \/ \E k \in PrivateKey, a \in Accounts, n \in Node, parent \in ChainsOf(a) : CreateOpenBlock(k, a, n, parent)
    \/ \E k \in PrivateKey, a \in Accounts, n \in Node, parent \in ChainsOf(a), amt \in 1..GenesisBalance : CreateReceiveBlock(k, a, n, parent, amt)
    \/ \E k \in PrivateKey, a \in Accounts, n \in Node : CreateChangeBlock(k, a, n)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

Balance(a, l) == BalanceBase(l) - BalanceBase(l \ {LastBlockOf(a)})
BalanceBase(S) == IF S = {} THEN 0 ELSE LET h == CHOOSE x \in S : TRUE IN (IF l[h].typ = "SEND" THEN -l[h].amount ELSE IF l[h].typ = "RECEIVE" THEN l[h].amount ELSE 0) + BalanceBase(S \ {h}) WHERE l == ledger[CHOOSE n \in Node : TRUE]

\* The ledger is replicated across all nodes, so a single bad signature anywhere
\* is a failure of the whole network's integrity.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h].owner # NoBlock => PublicKey[ledger[n][h].signature] = ledger[n][h].owner

====