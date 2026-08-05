---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal

\* The hash calculation is modeled as a constant operator; the .cfg substitutes a
\* concrete implementation (either a thin injective wrapper or the full operator)
\* known to the model-checker.
CONSTANT CalculateHash

NoHash == NoHashVal
NoBlock == NoBlockVal

ASSUME NoHash # NoBlock

\* Account: a public key derived from a private key in this test model. No two
\* private keys map to the same public key, so ownership is unambiguous.
Account == [private : PrivateKey, public : PublicKey]

\* Every account chain's blocks are ordered by belonging to one of these three
\* types, which also govern their validity checks.
BlockType == {"genesis", "send", "receive", "change"}

\* A signed block carries the account it belongs to, the hash of the previous
\* block in that account's chain, the amount it moves, the block type, an
\* optional referenced hash (for send/receive/change), and the signature.
Block == [account : Account, prevHash : Hash \cup {NoHash}, amount : Nat,
          blockType : BlockType, reference : Hash \cup {NoHash},
          signature : PublicKey]

\* H is the hash of the block it is hovering over; a received block may only
\* become valid if the block it references is already in the local ledger.
Received == [key : PrivateKey, block : Block, hover : Hash]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The account chain is walked recursively; at most GenesisBalance steps, which
\* bounds the depth enough for a finite model.
RECURSIVE ChainBalance(_)
ChainBalance(S) ==
    LET f(h) ==
        IF h = NoHash THEN 0
        ELSE LET b == S[h] IN
             IF b.account.blockType = "receive" THEN b.amount + f(b.reference)
             ELSE IF b.account.blockType = "send" THEN f(b.reference)
             ELSE IF b.account.blockType = "genesis" THEN b.amount
             ELSE f(b.reference)
    IN f

\* Because a node's ledger is a partial function on block hashes, a block may be
\* in transit while already recorded; that is which makes the received set
\* non-disjoint from its ledger.
Balance(n) == ChainBalance(ledger[n])

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET Received]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* A valid Ed25519 signature over a block's contents is the owner's public key.
ValidSignature(b) == b.signature = b.account.public

CreateGenesisBlock(k) ==
    /\ lastHash = NoHash
    /\ \E h \in Hash :
        /\ lastHash' = h
        /\ \E n \in Node :
            LET block == [account |-> [private |-> k, public |-> k],
                          prevHash |-> NoHash, amount |-> GenesisBalance,
                          blockType |-> "genesis", reference |-> NoHash,
                          signature |-> k] IN
                /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = block]]
                /\ received' = [m \in Node |-> { [key |-> k, block |-> block, hover |-> h] }]

CreateSendBlock(n, k, amt, to, ph) ==
    /\ ledger[n][ph] # NoBlock
    /\ ledger[n][ph].account.private = k
    /\ amt <= Balance(n)
    /\ \E h \in Hash :
        /\ h # lastHash
        /\ LET block == [account |-> [private |-> k, public |-> k],
                          prevHash |-> ph, amount |-> amt, blockType |-> "send",
                          reference |-> to, signature |-> k] IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = block]]
            /\ received' = [m \in Node |-> received[m] \cup {[key |-> k, block |-> block, hover |-> h]}]

CreateOpenBlock(n, k, ph) ==
    /\ ledger[n][ph] # NoBlock
    /\ ledger[n][ph].blockType = "send"
    /\ ledger[n][ph].reference = k
    /\ \E h \in Hash :
        /\ h # lastHash
        /\ ~(\E g \in Hash : ledger[n][g] # NoBlock /\ ledger[n][g].reference = ph)
        /\ LET block == [account |-> [private |-> k, public |-> k],
                          prevHash |-> NoHash, amount |-> 0, blockType |-> "change",
                          reference |-> ph, signature |-> k] IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = block]]
            /\ received' = [m \in Node |-> received[m] \cup {[key |-> k, block |-> block, hover |-> h]}]

CreateReceiveBlock(n, k, amt, ph, ref) ==
    /\ ledger[n][ref] # NoBlock
    /\ ledger[n][ref].account.private = k
    /\ ledger[n][ref].blockType = "send"
    /\ ledger[n][ref].reference = k
    /\ \E h \in Hash :
        /\ h # lastHash
        /\ ~(\E g \in Hash : ledger[n][g] # NoBlock /\ ledger[n][g].reference = ref)
        /\ LET block == [account |-> [private |-> k, public |-> k],
                          prevHash |-> ph, amount |-> amt, blockType |-> "receive",
                          reference |-> ref, signature |-> k] IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = block]]
            /\ received' = [m \in Node |-> received[m] \cup {[key |-> k, block |-> block, hover |-> h]}]

CreateChangeBlock(n, k, ph) ==
    /\ ledger[n][ph] # NoBlock
    /\ ledger[n][ph].account.private = k
    /\ \E h \in Hash :
        /\ h # lastHash
        /\ LET block == [account |-> [private |-> k, public |-> k],
                          prevHash |-> ph, amount |-> 0, blockType |-> "change",
                          reference |-> NoHash, signature |-> k] IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = block]]
            /\ received' = [m \in Node |-> received[m] \cup {[key |-> k, block |-> block, hover |-> h]}]

\* Validation checks signatures, block existence, and block-type-specific
\* rules (such as balanced draws in a send block); it is what turns a received
\* block into a block actually recorded in the ledger.
ValidateBlock(n, x) ==
    /\ x.key = x.block.account.private
    /\ x.hover = ledger[n][x.block.prevHash].account.private
    /\ ledger[n][x.block.prevHash] # NoBlock
    /\ ValidSignature(x.block)
    /\ \/ /\ x.block.blockType = "send" /\ x.block.amount <= Balance(n)
          /\ x.block.reference \notin PublicKey
       \/ /\ x.block.blockType = "receive"
          /\ ledger[n][x.block.reference].account.private = x.block.account.private
          /\ ledger[n][x.block.reference].blockType = "send"
          /\ ledger[n][x.block.reference].reference = x.block.account.public
       \/ /\ x.block.blockType \in {"genesis", "change"}
    /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![x.hover] = x.block]]
    /\ received' = [m \in Node |-> received[m] \ {x}]

Next ==
    \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, to \in PublicKey, ph \in Hash : CreateSendBlock(n, k, amt, to, ph)
    \/ \E n \in Node, k \in PrivateKey, ph \in Hash : CreateOpenBlock(n, k, ph)
    \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, ph \in Hash, ref \in Hash : CreateReceiveBlock(n, k, amt, ph, ref)
    \/ \E n \in Node, k \in PrivateKey, ph \in Hash : CreateChangeBlock(n, k, ph)
    \/ \E n \in Node, x \in received[n] : ValidateBlock(n, x)
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)

Spec == Init /\ [][Next]_vars

\* Every block recorded anywhere in the replicated ledger must carry a signature
\* that matches the public key of the account that owns the chain it sits on.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlock => ledger[n][h].signature = ledger[n][h].account.public

====