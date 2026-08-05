---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair, Node,
          GenesisBalance, Ownership

ASSUME
    \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

VARIABLES lastHash, distributedLedger, received

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
    /\ received \subseteq [node : Node, block : SignedBlock \cup {NoBlock}]

\* Each block is cryptographically signed by one private key and validated
\* against the public key of the account it originated from.
CryptographicInvariant ==
    \A node \in Node :
        \A hash \in Hash :
            LET b == distributedLedger[node][hash] IN
            b # NoBlock =>
                LET pk == PublicKeyOf(distributedLedger[node], hash) IN
                ValidateSignature(b.signature, pk, hash)

Safety == TypeOK /\ CryptographicInvariant

\* Start: no block has been created or accepted yet.
Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = {}

\* New blocks are produced by each node locally as signatures rather than
\* as already-validated ledger entries.
CreateBlock(node) ==
    \/ \E privateKey \in PrivateKey :
         /\ ~GenesisBlockExists
         /\ let g == [type |-> "genesis", account |-> KeyPair[privateKey],
                      balance |-> GenesisBalance] in
            CalculateHash(g, lastHash, lastHash')
            /\ distributedLedger' =
                 [n \in Node |-> [distributedLedger[n] EXCEPT ![lastHash'] = [block |-> g,
                    signature |-> SignHash(lastHash', privateKey)]]]
            /\ UNCHANGED received
    \/ \E block \in Block :
         \E privateKey \in PrivateKey :
            /\ block.type \in {"open", "send", "receive", "change"}
            /\ block.type = "open" =>
                 /\ ledger[block.source] # NoBlock
                 /\ ledger[block.source].block.type = "send"
            /\ block.type = "send" =>
                 /\ ledger[block.previous] # NoBlock
                 /\ block.balance <= BalanceAt(ledger, block.previous)
            /\ block.type = "receive" =>
                 /\ ledger[block.previous] # NoBlock
                 /\ ledger[block.source] # NoBlock
                 /\ ledger[block.source].block.type = "send"
                 /\ ~IsSendReceived(ledger, block.source)
            /\ block.type = "change" => ledger[block.previous] # NoBlock
            /\ CalculateHash(block, lastHash, lastHash')
            /\ received' = received \cup
                 {[node |-> node, block |-> [block |-> block,
                     signature |-> SignHash(lastHash', privateKey)]]}
            /\ UNCHANGED distributedLedger
    \/ \E entry \in received :
         /\ entry.node = node
         /\ let ledger == distributedLedger[node] in
              LET b == entry.block IN
              /\ ValidateSignature(b.signature, PublicKeyOf(ledger, b.block.previous), lastHash')
              /\ ledger' = [ledger EXCEPT ![lastHash'] = b]
         /\ received' = received \ {entry}
         /\ UNCHANGED <<lastHash, distributedLedger>>

Next == \E node \in Node : CreateBlock(node)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>
====