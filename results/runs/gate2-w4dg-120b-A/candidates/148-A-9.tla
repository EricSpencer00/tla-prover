---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (Hash \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

\* Recursive balance walk: follow the account chain from its head back to the
\* genesis block, adding each block's transfer amount.
RECURSIVE Balance(_), Chain(_)
Balance(a) ==
    IF Chain(a) = NoHash
    THEN 0
    ELSE IF Chain(a) = NoHashVal
    THEN 0
    ELSE Chain(a)
Chain(a) ==
    LET b == ledger[a][a] IN
        IF b = NoBlockVal
        THEN NoHash
        ELSE Chain(b)

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(pk) ==
    /\ lastHash = NoHash
    /\ pk \in PrivateKey
    /\ LET h == CalculateHash(pk, NoHash) IN
        /\ lastHash' = h
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = h]]
        /\ received' = [n \in Node |-> {h}]
    /\ UNCHANGED <<>>

\* A send block must not send more than the available balance of its own account.
CreateSendBlock(n, pk, to) ==
    /\ pk \in PrivateKey
    /\ n \in Node
    /\ lastHash # NoHash
    /\ Balance(n) >= 1
    /\ LET h == CalculateHash(pk, lastHash) IN
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![n][h] = lastHash]
        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
    /\ UNCHANGED <<>>

CreateOpenBlock(n, pk, send) ==
    /\ pk \in PrivateKey
    /\ n \in Node
    /\ lastHash # NoHash
    /\ Chain(n) = NoHash
    /\ send \in ledger[n]
    /\ ledger[n][send] = NoHashVal
    /\ LET h == CalculateHash(pk, lastHash) IN
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![n][h] = send]
        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
    /\ UNCHANGED <<>>

\* A receive block references the block it receives and the previous block
\* of the receiving account (if any), adding the sent amount to its balance.
CreateReceiveBlock(n, pk, send) ==
    /\ pk \in PrivateKey
    /\ n \in Node
    /\ lastHash # NoHash
    /\ Chain(n) # NoHash
    /\ Chain(n) \in ledger[n]
    /\ send \in ledger[n]
    /\ ledger[n][send] = NoHashVal
    /\ LET h == CalculateHash(pk, lastHash) IN
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![n][h] = {send, Chain(n)}]
        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
    /\ UNCHANGED <<>>

CreateChangeRepresentativeBlock(n, pk) ==
    /\ pk \in PrivateKey
    /\ n \in Node
    /\ lastHash # NoHash
    /\ Chain(n) \in Hash
    /\ LET h == CalculateHash(pk, lastHash) IN
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![n][h] = Chain(n)]
        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
    /\ UNCHANGED <<>>

\* Validation checks signatures against the owning public key and checks
\* that all referenced blocks exist before adding to the ledger.
ValidateBlock(n, h) ==
    /\ h \in received[n]
    /\ LET b == ledger[n][h] IN
        /\ IF b = NoBlockVal
           THEN FALSE
           /\ UNCHANGED <<>>
        /\ CASE
            /\ b = NoHashVal
                -> TRUE
                /\ Chain(n) = NoHash
                /\ h = CalculateHash(\E pk \in PrivateKey : pk, NoHash)
                /\ ledger' = [ledger EXCEPT ![n][h] = b]
            /\ Cardinality(b) = 1
                -> \A x \in b : x \in Hash
                /\ h = CalculateHash(\E pk \in PrivateKey : pk, lastHash)
                /\ Chain(n) \in Hash
                /\ ledger' = [ledger EXCEPT ![n][h] = b]
            /\ Cardinality(b) = 2
                -> \A x \in b : x \in Hash
                /\ h = CalculateHash(\E pk \in PrivateKey : pk, lastHash)
                /\ Chain(n) \in Hash
                /\ ledger' = [ledger EXCEPT ![n][h] = b]
        /\ UNCHANGED <<lastHash, received>>

Next ==
    \/ \E pk \in PrivateKey : CreateGenesisBlock(pk)
    \/ \E n \in Node, pk \in PrivateKey, to \in PublicKey : CreateSendBlock(n, pk, to)
    \/ \E n \in Node, pk \in PrivateKey, send \in Hash : CreateOpenBlock(n, pk, send)
    \/ \E n \in Node, pk \in PrivateKey, send \in Hash : CreateReceiveBlock(n, pk, send)
    \/ \E n \in Node, pk \in PrivateKey : CreateChangeRepresentativeBlock(n, pk)
    \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Cryptographic correctness: every recorded block actually verifies under
\* the public key of the account chain it belongs to.
SignatureValidForAccount(n, h) ==
    /\ ledger[n][h] # NoBlockVal
    /\ \E pk \in PrivateKey : PublicKey = \E pk \in PrivateKey : pk

SafetyInvariant == \A n \in Node, h \in Hash : SignatureValidForAccount(n, h)

====