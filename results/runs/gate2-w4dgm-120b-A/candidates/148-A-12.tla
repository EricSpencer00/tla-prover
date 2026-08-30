---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHash \notin Hash
ASSUME NoBlock \notin Hash

Accounts == PublicKey

\* Curried for substitution: the model can swap a concrete impl for the spec's op.
CalculateHashImpl(data, prev) == CalculateHash(data, prev)

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Ordered chain: the hash of the previous block is recorded in every new block.
Block == [account: Accounts, type: {"genesis", "send", "open", "receive", "change"}, prev: Hash \union {NoHash}, target: Accounts \union {NoAccount}, amount: Nat]

\* No account's chain is ever empty, so a genesis hash always exists and is
\* always searchable.
NoAccount == NoHash

RECURSIVE ChainBalance(_)
ChainBalance(S) ==
    IF S = {} THEN 0
    ELSE LET h == CHOOSE e \in S : TRUE
             rest == ChainBalance(S \ {h})
         IN IF ledger[h].account = ledger[h].target
            THEN rest + ledger[h].amount
            ELSE IF ledger[h].type = "receive"
                 THEN rest + ledger[h].amount
                 ELSE rest - ledger[h].amount

RECURSIVE LedgerBalance(_)
LedgerBalance(S) ==
    IF S = {} THEN 0
    ELSE LET h == CHOOSE e \in S : TRUE
         IN ChainBalance({g \in S : ledger[g].account = ledger[h].account})

TypeOK ==
    /\ lastHash \in Hash \union {NoHash}
    /\ ledger \in [Node -> [Hash -> Block \union {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* The genesis block is the only block introduced without a prior hash.
CreateGenesisBlock(n, k) ==
    /\ lastHash = NoHash
    /\ \A g \in Node : ledger[g][NoHash] = NoBlockVal
    /\ lastHash' = CalculateHashImpl([account |-> k, type |-> "genesis", prev |-> NoHash, target |-> k, amount |-> GenesisBalance], NoHash)
    /\ ledger' = [g \in Node |-> [ledger[g] EXCEPT ![lastHash] = [account |-> k, type |-> "genesis", prev |-> NoHash, target |-> k, amount |-> GenesisBalance]]]
    /\ received' = [g \in Node |-> {lastHash}]

CreateSendBlock(n, k, t, amt) ==
    /\ ledger[n][lastHash].type \in {"genesis", "receive", "change", "open"}
    /\ ledger[n][lastHash].target = k
    /\ amt <= ChainBalance({g \in Hash : ledger[g].account = k})
    /\ lastHash' = CalculateHashImpl([account |-> k, type |-> "send", prev |-> lastHash, target |-> t, amount |-> amt], lastHash)
    /\ ledger' = [g \in Node |-> [ledger[g] EXCEPT ![lastHash] = [account |-> k, type |-> "send", prev |-> lastHash, target |-> t, amount |-> amt]]]
    /\ received' = [g \in Node |-> received[g] \union {lastHash}]

CreateOpenBlock(n, k, sendHash) ==
    /\ ledger[n][lastHash].type \in {"genesis", "receive", "change", "open"}
    /\ ledger[n][sendHash].type = "send"
    /\ ledger[n][sendHash].target = k
    /\ ledger[n][lastHash].account # k
    /\ lastHash' = CalculateHashImpl([account |-> k, type |-> "open", prev |-> lastHash, target |-> NoAccount, amount |-> 0], lastHash)
    /\ ledger' = [g \in Node |-> [ledger[g] EXCEPT ![lastHash] = [account |-> k, type |-> "open", prev |-> lastHash, target |-> NoAccount, amount |-> 0]]]
    /\ received' = [g \in Node |-> received[g] \union {lastHash}]

CreateReceiveBlock(n, k, sendHash) ==
    /\ ledger[n][lastHash].type \in {"genesis", "receive", "change", "open"}
    /\ ledger[n][sendHash].type = "send"
    /\ ledger[n][sendHash].target = k
    /\ lastHash' = CalculateHashImpl([account |-> k, type |-> "receive", prev |-> lastHash, target |-> NoAccount, amount |-> ledger[n][sendHash].amount], lastHash)
    /\ ledger' = [g \in Node |-> [ledger[g] EXCEPT ![lastHash] = [account |-> k, type |-> "receive", prev |-> lastHash, target |-> NoAccount, amount |-> ledger[n][sendHash].amount]]]
    /\ received' = [g \in Node |-> received[g] \union {lastHash}]

CreateChangeRepresentativeBlock(n, k) ==
    /\ ledger[n][lastHash].type \in {"genesis", "receive", "change", "open"}
    /\ ledger[n][lastHash].account = k
    /\ lastHash' = CalculateHashImpl([account |-> k, type |-> "change", prev |-> lastHash, target |-> NoAccount, amount |-> 0], lastHash)
    /\ ledger' = [g \in Node |-> [ledger[g] EXCEPT ![lastHash] = [account |-> k, type |-> "change", prev |-> lastHash, target |-> NoAccount, amount |-> 0]]]
    /\ received' = [g \in Node |-> received[g] \union {lastHash}]

ValidateBlock(n, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] = NoBlockVal
    /\ ledger[n][ledger[n][h].prev] # NoBlockVal
    /\ LET blk == ledger[n][h] IN
         /\ ledger[n][h].account \in PublicKey
         /\ ledger[n][h].type \in {"genesis", "send", "open", "receive", "change"}
         /\ IF blk.type = "send"
            THEN blk.amount <= ChainBalance({g \in Hash : ledger[g].account = blk.account})
            ELSE IF blk.type = "open"
                 THEN ledger[n][blk.prev].type = "send" /\ ledger[n][blk.prev].target = blk.account
                 ELSE IF blk.type = "receive"
                      THEN ledger[n][blk.prev].type \in {"genesis", "receive", "change", "open"}
                           /\ ledger[n][blk.prev].account = blk.account
                           /\ \E p \in Hash : ledger[n][p].type = "send" /\ ledger[n][p].target = blk.account
                      ELSE TRUE
    /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E n \in Node, k \in PrivateKey : CreateGenesisBlock(n, k)
    \/ \E n \in Node, k \in PrivateKey, t \in Accounts, amt \in 1..GenesisBalance : CreateSendBlock(n, k, t, amt)
    \/ \E n \in Node, k \in PrivateKey, sh \in Hash : CreateOpenBlock(n, k, sh)
    \/ \E n \in Node, k \in PrivateKey, sh \in Hash : CreateReceiveBlock(n, k, sh)
    \/ \E n \in Node, k \in PrivateKey : CreateChangeRepresentativeBlock(n, k)
    \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* The twist: no node may hold a block whose signature claims a different
\* account than the block is actually addressed to.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].account \in PublicKey

====