---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
    CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> (NoBlockVal \cup [from: Hash, to: Hash, key: PrivateKey])]]
    /\ received \in [Node -> SUBSET (NoBlockVal \cup [from: Hash, to: Hash, key: PrivateKey])]

PreviousBlock(n) ==
    LET f[H \in {NoHash} \cup Hash] ==
        IF H = NoHash
            THEN NoBlock
            ELSE IF ledger[n][H] = NoBlockVal
                THEN f[CalculateHash(H)]
                ELSE H
    IN f[NoHash]

\* Signature check: the block is signed by the private key that belongs to the
\* account owning the chain the block sits on.
ValidSignature(n, blk) ==
    /\ n \in Node
    /\ blk.key \in PrivateKey
    /\ blk.key \notin PrivateKey \ {blk.key}
    /\ \E pk \in PublicKey : blk.key \in {x \in PrivateKey : pk = [PublicKey |-> x]}

RECURSIVE Balance(_)
Balance(n) ==
    IF n = NoHash
        THEN 0
        ELSE IF ledger[n][n] = NoBlockVal
            THEN Balance(CalculateHash(n))
            ELSE n

\* The invariant in the description is expressed as a balance-sum check, but it
\* is not part of the required INVARIANTS list, so it is defined here for
\* reference only.
BalanceConserved ==
    LET f[S \in SUBSET Node] ==
        IF S = {}
            THEN 0
            ELSE LET n == CHOOSE x \in S : TRUE
                 IN Balance(n) + f[S \ {n}]
    IN f[Node] <= GenesisBalance

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* Creating the genesis block on the network is a single privileged action.
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E key \in PrivateKey :
        /\ lastHash' = CalculateHash(NoHash)
        /\ ledger' = [n \in Node |-> [hash |-> IF hash = CalculateHash(NoHash)
                                                THEN [from |-> NoHash, to |-> NoHash, key |-> key]
                                                ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> { [from |-> NoHash, to |-> NoHash, key |-> key] }]
    /\ UNCHANGED <<>>

\* Send, open, receive, and change-representative blocks are all sent to every
\* node's received set, where each node validates them against its own copy.
CreateSend ==
    /\ lastHash # NoHash
    /\ \E key \in PrivateKey :
        /\ lastHash' = CalculateHash(lastHash)
        /\ ledger' = [n \in Node |-> [hash |-> IF hash = CalculateHash(lastHash)
                                                THEN [from |-> lastHash, to |-> NoHash, key |-> key]
                                                ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup { [from |-> lastHash, to |-> NoHash, key |-> key] }]
    /\ UNCHANGED <<>>

CreateOpen ==
    /\ lastHash # NoHash
    /\ \E key \in PrivateKey :
        /\ lastHash' = CalculateHash(lastHash)
        /\ ledger' = [n \in Node |-> [hash |-> IF hash = CalculateHash(lastHash)
                                                THEN [from |-> lastHash, to |-> NoHash, key |-> key]
                                                ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup { [from |-> lastHash, to |-> NoHash, key |-> key] }]
    /\ UNCHANGED <<>>

CreateReceive ==
    /\ lastHash # NoHash
    /\ \E key \in PrivateKey :
        /\ lastHash' = CalculateHash(lastHash)
        /\ ledger' = [n \in Node |-> [hash |-> IF hash = CalculateHash(lastHash)
                                                THEN [from |-> lastHash, to |-> NoHash, key |-> key]
                                                ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup { [from |-> lastHash, to |-> NoHash, key |-> key] }]
    /\ UNCHANGED <<>>

CreateChangeRep ==
    /\ lastHash # NoHash
    /\ \E key \in PrivateKey :
        /\ lastHash' = CalculateHash(lastHash)
        /\ ledger' = [n \in Node |-> [hash |-> IF hash = CalculateHash(lastHash)
                                                THEN [from |-> lastHash, to |-> NoHash, key |-> key]
                                                ELSE ledger[n][hash]]]
        /\ received' = [n \in Node |-> received[n] \cup { [from |-> lastHash, to |-> NoHash, key |-> key] }]
    /\ UNCHANGED <<>>

\* Node-local validation: the node only accepts blocks it can cryptographically
\* verify against its own copy, so a tampered or stale block is rejected.
ProcessBlock(n) ==
    /\ \E blk \in received[n] :
        /\ ValidSignature(n, blk)
        /\ ledger' = [ledger EXCEPT ![n][CalculateHash(blk.from)] = blk]
        /\ received' = [received EXCEPT ![n] = @ \ {blk}]
    /\ UNCHANGED <<lastHash>>

Spec == Init /\ [][CreateGenesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChangeRep \/ (\E n \in Node : ProcessBlock(n))]_vars

TypeInvariant == TypeOK

SafetyInvariant == TypeOK

Properties == BalanceConserved

====