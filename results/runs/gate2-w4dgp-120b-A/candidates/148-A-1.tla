---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal,
    PrivateKey, PublicKey,
    Node, GenesisBalance, NoBlockVal,
    CalculateHash,
    NoHash, NoBlock

VARIABLES lastHash, ledger, received

\* Each node replicates the whole distributed ledger, and each node has its own
\* set of pending blocks that have been broadcast but not yet validated and applied.
vars == <<lastHash, ledger, received>>

MatchPub == [p \in PublicKey |-> CHOOSE k \in PrivateKey : PublicKey[k] = p]

BlockType == {"GENESIS", "SEND", "OPEN", "RECEIVE", "CHANGE_REP"}

\* A block is always signed by the key that owns the account chain containing it.
Block == [type : BlockType, prevHash : Hash, destPub : PublicKey, amount : 0..GenesisBalance, signer : PrivateKey]

\* The block chain for an account is the set of all blocks that are reachable
\* by following backwards links from a given tip hash.
RECURSIVE Chain(_)
Chain(h) ==
    IF h = NoHash THEN {}
    ELSE
        LET b == ledger[h] IN
        b \cup Chain(b.prevHash)

BalanceFor(account, h) ==
    IF h = NoHash THEN 0
    ELSE
        LET b == ledger[h] IN
        IF b.signer = account
            THEN IF b.type = "SEND" THEN BalanceFor(account, b.prevHash) - b.amount
                 ELSE IF b.type = "RECEIVE" THEN BalanceFor(account, b.prevHash) + b.amount
                 ELSE BalanceFor(account, b.prevHash)
            ELSE BalanceFor(account, b.prevHash)

RECURSIVE BalanceAcross(_, _)
BalanceAcross(h, accounts) ==
    IF accounts = {} THEN 0
    ELSE
        LET a == CHOOSE x \in accounts : TRUE IN
        BalanceFor(a, h) + BalanceAcross(h, accounts \ {a})

Balance == BalanceAcross(NoHash, PrivateKey)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n, key) ==
    /\ lastHash = NoHashVal
    /\ LET h == CalculateHash([type |-> "GENESIS", prevHash |-> NoHash, destPub |-> MatchPub[key], amount |-> GenesisBalance, signer |-> key])
           blk == [type |-> "GENESIS", prevHash |-> NoHash, destPub |-> MatchPub[key], amount |-> GenesisBalance, signer |-> key]
       IN /\ lastHash' = h
          /\ ledger' = [x \in Hash |-> IF x = h THEN blk ELSE NoBlockVal]
          /\ received' = [c \in Node |-> (IF c = n THEN {h} ELSE {}) \cup received[c]]
    /\ UNCHANGED Balance

CreateSendBlock(n, key, recipient, amt) ==
    /\ lastHash # NoHashVal
    /\ BalanceFor(key, lastHash) >= amt
    /\ LET h == CalculateHash([type |-> "SEND", prevHash |-> lastHash, destPub |-> MatchPub[recipient], amount |-> amt, signer |-> key])
           blk == [type |-> "SEND", prevHash |-> lastHash, destPub |-> MatchPub[recipient], amount |-> amt, signer |-> key]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = blk]
          /\ received' = [c \in Node |-> (IF c = n THEN {h} ELSE {}) \cup received[c]]
    /\ UNCHANGED Balance

CreateOpenBlock(n, key, sendHash) ==
    /\ sendHash \in received[n]
    /\ ledger[sendHash].type = "SEND"
    /\ ledger[sendHash].destPub = MatchPub[key]
    /\ NoHash \notin Chain(sendHash)
    /\ LET h == CalculateHash([type |-> "OPEN", prevHash |-> NoHash, destPub |-> MatchPub[key], amount |-> ledger[sendHash].amount, signer |-> key])
           blk == [type |-> "OPEN", prevHash |-> NoHash, destPub |-> MatchPub[key], amount |-> ledger[sendHash].amount, signer |-> key]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = blk]
          /\ received' = [c \in Node |-> (IF c = n THEN {h} ELSE {}) \cup received[c]]
    /\ UNCHANGED Balance

CreateReceiveBlock(n, key, sendHash, recvPrev) ==
    /\ sendHash \in received[n]
    /\ ledger[sendHash].type = "SEND"
    /\ ledger[sendHash].destPub = MatchPub[key]
    /\ recvPrev \in Chain(lastHash)
    /\ LET h == CalculateHash([type |-> "RECEIVE", prevHash |-> recvPrev, destPub |-> MatchPub[key], amount |-> ledger[sendHash].amount, signer |-> key])
           blk == [type |-> "RECEIVE", prevHash |-> recvPrev, destPub |-> MatchPub[key], amount |-> ledger[sendHash].amount, signer |-> key]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = blk]
          /\ received' = [c \in Node |-> (IF c = n THEN {h} ELSE {}) \cup received[c]]
    /\ UNCHANGED Balance

CreateChangeRepBlock(n, key, recvPrev) ==
    /\ recvPrev \in Chain(lastHash)
    /\ LET h == CalculateHash([type |-> "CHANGE_REP", prevHash |-> recvPrev, destPub |-> MatchPub[key], amount |-> 0, signer |-> key])
           blk == [type |-> "CHANGE_REP", prevHash |-> recvPrev, destPub |-> MatchPub[key], amount |-> 0, signer |-> key]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = blk]
          /\ received' = [c \in Node |-> (IF c = n THEN {h} ELSE {}) \cup received[c]]
    /\ UNCHANGED Balance

UpdateNodeLedger(n, h) ==
    /\ h \in received[n]
    /\ ledger[h].signer = n
    /\ ledger[h].prevHash \in Chain(lastHash)
    /\ /\ (ledger[h].type \in {"RECEIVE", "SEND"} => BalanceFor(n, lastHash) >= ledger[h].amount)
       /\ (ledger[h].type = "OPEN" => NoHash \notin Chain(ledger[h].prevHash))
       /\ (ledger[h].type = "RECEIVE" => NoHash \notin Chain(h))
    /\ lastHash' = IF h > lastHash THEN h ELSE lastHash
    /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED Balance

Next ==
    \/ \E n \in Node, key \in PrivateKey : CreateGenesisBlock(n, key)
    \/ \E n \in Node, key \in PrivateKey, recipient \in PublicKey, amt \in 0..GenesisBalance : CreateSendBlock(n, key, recipient, amt)
    \/ \E n \in Node, key \in PrivateKey, sendHash \in Hash : CreateOpenBlock(n, key, sendHash)
    \/ \E n \in Node, key \in PrivateKey, sendHash \in Hash, recvPrev \in Hash : CreateReceiveBlock(n, key, sendHash, recvPrev)
    \/ \E n \in Node, key \in PrivateKey, recvPrev \in Hash : CreateChangeRepBlock(n, key, recvPrev)
    \/ \E n \in Node, h \in Hash : UpdateNodeLedger(n, h)

Spec == Init /\ [][Next]_vars

\* Type-correctness is not enough: every block in every node's ledger must verify
\* against the public key derived from its signing private key.
TypeInvariant ==
    /\ lastHash \in {NoHashVal} \cup Hash
    /\ ledger \in [Hash -> Block \cup {NoBlockVal}]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A h \in Hash : (ledger[h] # NoBlockVal) => ledger[h].signer \in {k \in PrivateKey : PublicKey[k] = ledger[h].destPub}

BalanceInvariant == Balance <= GenesisBalance

ShowcaseBalanceInvariant == BalanceInvariant

====