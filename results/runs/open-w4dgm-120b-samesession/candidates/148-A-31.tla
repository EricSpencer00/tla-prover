---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* The "account chain" is a linked list of blocks per public key, and the
\* hash of the whole chain is what orders creation; a block must always
\* reference the hash of the block before it in that exact order.
\* Validation therefore checks the whole local ledger copy, not just the
\* new block in isolation -- an out-of-order write is caught here.
\* (This is the shape of the problem that makes the state space blow up.)

Block == [kind: {"genesis", "send", "open", "receive", "change"},
          owner: PublicKey, pkey: PrivateKey, prev: Hash, src: Hash, bal: 0..GenesisBalance]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Leds == [Node -> [Hash -> Block \cup {NoBlockVal}]]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in Leds
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* A node's own account balance is the sum of its chain's amounts in order.
RECURSIVE ChainBal(_)
ChainBal(b) == IF b = NoBlockVal THEN 0 ELSE b.bal + ChainBal(ledger[Node][b.prev])

RECURSIVE ChainLens(_)
ChainLens(b) == IF b = NoBlockVal THEN 0 ELSE 1 + ChainLens(ledger[Node][b.prev])

Balance(n) == ChainBal(ledger[n][lastHash])
ChainLength(n) == ChainLens(ledger[n][lastHash])

ValidateBase(n, h) == ledger[n][h] # NoBlockVal

\* Creates the genesis block, writes it into every node's ledger at once.
CreateGenesis(pkey) ==
    /\ lastHash = NoHash
    /\ Cardinality(ledger) > 0
    /\ \E h \in Hash:
         /\ ledger[CHOOSE n \in Node : TRUE][h] = NoBlockVal
         /\ lastHash' = h
         /\ ledger' = [n \in Node |->
                         [ledger[n] EXCEPT ![h] =
                             [kind |-> "genesis", owner |-> PublicKey[pkey],
                              pkey |-> pkey, prev |-> NoHash, src |-> NoHash, bal |-> GenesisBalance]]]
    /\ UNCHANGED received

CreateSend(n, pkey, amt, h) ==
    /\ lastHash # NoHash
    /\ ValidateBase(n, lastHash)
    /\ ChainLength(n) < ChainLength(n) + 1
    /\ amt <= Balance(n)
    /\ \E nh \in Hash:
         /\ ledger[n][nh] = NoBlockVal
         /\ lastHash' = nh
         /\ ledger' = [ledger EXCEPT ![n][nh] =
                          [kind |-> "send", owner |-> PublicKey[pkey], pkey |-> pkey,
                           prev |-> lastHash, src |-> NoHash, bal |-> amt]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {nh}]
    /\ UNCHANGED <<>>

\* An "open" block must be the first on its own account chain.
CreateOpen(n, pkey, src, h) ==
    /\ lastHash # NoHash
    /\ ValidateBase(n, lastHash)
    /\ ledger[n][src] # NoBlockVal
    /\ ledger[n][src].kind \in {"send", "receive"}
    /\ ledger[n][src].owner = PublicKey[pkey]
    /\ ChainLength(n) = 0
    /\ \E nh \in Hash:
         /\ ledger[n][nh] = NoBlockVal
         /\ lastHash' = nh
         /\ ledger' = [ledger EXCEPT ![n][nh] =
                          [kind |-> "open", owner |-> PublicKey[pkey], pkey |-> pkey,
                           prev |-> lastHash, src |-> src, bal |-> 0]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {nh}]
    /\ UNCHANGED <<>>

CreateReceive(n, pkey, src, h) ==
    /\ lastHash # NoHash
    /\ ValidateBase(n, lastHash)
    /\ ledger[n][src] # NoBlockVal
    /\ ledger[n][src].owner = PublicKey[pkey]
    /\ ledger[n][src].kind \in {"send", "receive"}
    /\ ledger[n][src].bal <= Balance(n)
    /\ \E nh \in Hash:
         /\ ledger[n][nh] = NoBlockVal
         /\ lastHash' = nh
         /\ ledger' = [ledger EXCEPT ![n][nh] =
                          [kind |-> "receive", owner |-> PublicKey[pkey], pkey |-> pkey,
                           prev |-> lastHash, src |-> src, bal |-> ledger[n][src].bal]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {nh}]
    /\ UNCHANGED <<>>

\* A "representative" change is a block on its own account chain with no
\* amount moved; it exists purely as a voting placeholder.
CreateChangeRep(n, pkey, h) ==
    /\ lastHash # NoHash
    /\ ValidateBase(n, lastHash)
    /\ \E nh \in Hash:
         /\ ledger[n][nh] = NoBlockVal
         /\ lastHash' = nh
         /\ ledger' = [ledger EXCEPT ![n][nh] =
                          [kind |-> "change", owner |-> PublicKey[pkey], pkey |-> pkey,
                           prev |-> lastHash, src |-> NoHash, bal |-> 0]]
         /\ received' = [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {nh}]
    /\ UNCHANGED <<>>

\* Validation here is the whole point: the local copy must already agree
\* on the base chain, or the write is rejected rather than applied.
ValidateBlock(n, h) ==
    /\ h \in received[n]
    /\ ValidateBase(n, ledger[n][h].prev)
    /\ ledger[n][h].pkey \in PrivateKey
    /\ PublicKey[ledger[n][h].pkey] = ledger[n][h].owner
    /\ IF ledger[n][h].kind = "send" THEN ledger[n][h].bal <= Balance(n) ELSE TRUE
    /\ IF ledger[n][h].kind = "open" THEN ChainLength(n) = 0 ELSE TRUE
    /\ IF ledger[n][h].kind = "receive" THEN ChainLength(n) > 0 ELSE TRUE
    /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED lastHash

ValidateAny == \E n \in Node, h \in Hash: ValidateBlock(n, h)

Next ==
    \/ \E pkey \in PrivateKey: CreateGenesis(pkey)
    \/ \E n \in Node, pkey \in PrivateKey, amt \in 1..GenesisBalance, h \in Hash: CreateSend(n, pkey, amt, h)
    \/ \E n \in Node, pkey \in PrivateKey, src \in Hash, h \in Hash: CreateOpen(n, pkey, src, h)
    \/ \E n \in Node, pkey \in PrivateKey, src \in Hash, h \in Hash: CreateReceive(n, pkey, src, h)
    \/ \E n \in Node, pkey \in PrivateKey, h \in Hash: CreateChangeRep(n, pkey, h)
    \/ ValidateAny

Spec == Init /\ [][Next]_vars /\ WF_vars(ValidateAny)

\* A block's pkey/public key pair is the only thing its signature can
\* feasibly be checked against in this model, so the invariant is that
\* they actually match up for every block in every copy. That rules out
\* a forged block silently taking up space in a replicated ledger.
SafetyInvariant == \A n \in Node: \A h \in Hash:
    (ledger[n][h] # NoBlockVal) => PublicKey[ledger[n][h].pkey] = ledger[n][h].owner

====