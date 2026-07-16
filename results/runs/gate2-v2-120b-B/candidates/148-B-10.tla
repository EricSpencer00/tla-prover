---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    PrivateKey,
    PublicKey,
    KeyPair,
    Node,
    GenesisBalance,
    Ownership

VARIABLES
    lastHash,
    distributedLedger,
    received

\* Constants required for TC generation
NoBlock == CHOOSE b : b \notin SignedBlock
NoHash  == CHOOSE h : h \notin Hash

\* Signature record used throughout the spec
Signature == [data : Hash, signedWith : PrivateKey]

\* Helper to sign a hash
SignHash(hash, pk) ==
    [data |-> hash, signedWith |-> pk]

\* Validation of a signature against a public key and hash
ValidateSignature(sig, pk, h) ==
    LET pub == KeyPair[sig.signedWith] IN
    /\ pub = pk
    /\ sig.data = h

\* Block types
GenesisBlock == [type |-> "genesis", account |-> PUBLIC, balance |-> GenesisBalance]
SendBlock     == [type |-> "send", previous |-> Hash, balance |-> Nat,
                  destination |-> PublicKey]
OpenBlock     == [type |-> "open", account |-> PublicKey,
                  source |-> Hash, rep |-> PublicKey]
ReceiveBlock  == [type |-> "receive", previous |-> Hash,
                  source |-> Hash]
ChangeRepBlock == [type |-> "change", previous |-> Hash,
                   rep |-> PublicKey]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

\* Ledger maps a hash to a signed block or a sentinel NoBlock
Ledger == [Hash -> SignedBlock \cup {NoBlock}]

\* Distribution of ledgers across nodes
DistLedger == [Node -> Ledger]

\* Predicate stating that a genesis block has been created
GenesisBlockExists == lastHash /= NoHash

\* ----------------------------------------------------------------------
\* Recursive helpers
\* ----------------------------------------------------------------------
RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, h) ==
    LET sb == ledger[h] IN
    IF sb = NoBlock THEN PUBLIC
    ELSE
        LET blk == sb.block IN
        IF blk.type \in {"genesis", "open"}
        THEN blk.account
        ELSE PublicKeyOf(ledger, blk.previous)

RECURSIVE BalanceAt(_, _)
BalanceAt(ledger, h) ==
    LET sb == ledger[h] IN
    IF sb = NoBlock THEN 0
    ELSE
        LET blk == sb.block IN
        CASE blk.type = "genesis" -> blk.balance
        [] blk.type = "open"    -> BalanceAt(ledger, blk.source)
        [] blk.type = "send"    -> blk.balance
        [] blk.type = "receive" -> BalanceAt(ledger, blk.previous) + (BalanceAt(ledger, blk.source) - BalanceAt(ledger, blk.source))
        [] blk.type = "change"  -> BalanceAt(ledger, blk.previous)

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesisBlock(privateKey) ==
    LET pub == KeyPair[privateKey] IN
    /\ ~GenesisBlockExists
    /\ lastHash' = CalculateHash(GenesisBlock, lastHash, lastHash')
    /\ distributedLedger' = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ distributedLedger' = [n \in Node |->
          [h \in Hash |-> 
            IF h = lastHash' THEN
                [block |-> GenesisBlock, signature |-> SignHash(lastHash', privateKey)]
            ELSE NoBlock]]
    /\ UNCHANGED received

CreateOpenBlock(node) ==
    LET pk == Ownership[node] IN
    LET pub == KeyPair[pk] IN
    LET ledger == distributedLedger[node] IN
    \E src \in Hash :
        ledger[src] /= NoBlock /\ ledger[src].block.type = "send" /\
        \E rep \in PublicKey :
            LET blk == [type |-> "open", account |-> pub,
                        source |-> src, rep |-> rep] IN
            LET h   == CalculateHash(blk, lastHash, lastHash') IN
            /\ received' = [received EXCEPT ![node] = @ \cup {
                [block |-> blk, signature |-> SignHash(h, pk)]}]
            /\ UNCHANGED <<lastHash, distributedLedger>>

CreateSendBlock(node) ==
    LET pk == Ownership[node] IN
    LET pub == KeyPair[pk] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        ledger[prev] /= NoBlock /\ PublicKeyOf(ledger, prev) = pub /\
        \E dst \in PublicKey :
            \E bal \in 0..GenesisBalance :
                LET blk == [type |-> "send", previous |-> prev,
                            balance |-> bal, destination |-> dst] IN
                LET h   == CalculateHash(blk, lastHash, lastHash') IN
                /\ received' = [received EXCEPT ![node] = @ \cup {
                    [block |-> blk, signature |-> SignHash(h, pk)]}]
                /\ UNCHANGED <<lastHash, distributedLedger>>

CreateReceiveBlock(node) ==
    LET pk == Ownership[node] IN
    LET pub == KeyPair[pk] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        ledger[prev] /= NoBlock /\ PublicKeyOf(ledger, prev) = pub /\
        \E src \in Hash :
            ledger[src] /= NoBlock /\ ledger[src].block.type = "send" /\
            ledger[src].block.destination = pub /\
            LET blk == [type |-> "receive", previous |-> prev,
                        source |-> src] IN
            LET h   == CalculateHash(blk, lastHash, lastHash') IN
            /\ received' = [received EXCEPT ![node] = @ \cup {
                [block |-> blk, signature |-> SignHash(h, pk)]}]
            /\ UNCHANGED <<lastHash, distributedLedger>>

CreateChangeRepBlock(node) ==
    LET pk == Ownership[node] IN
    LET pub == KeyPair[pk] IN
    LET ledger == distributedLedger[node] IN
    \E prev \in Hash :
        ledger[prev] /= NoBlock /\ PublicKeyOf(ledger, prev) = pub /\
        \E newRep \in PublicKey :
            LET blk == [type |-> "change", previous |-> prev,
                        rep |-> newRep] IN
            LET h   == CalculateHash(blk, lastHash, lastHash') IN
            /\ received' = [received EXCEPT ![node] = @ \cup {
                [block |-> blk, signature |-> SignHash(h, pk)]}]
            /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessBlock(node) ==
    \E sigBlk \in received[node] :
        LET blk == sigBlk.block IN
        IF blk.type = "open" THEN
            /\ ValidateSignature(sigBlk.signature, blk.account,
                                 CalculateHash(blk, lastHash, lastHash'))
            /\ distributedLedger' = [distributedLedger EXCEPT
                  ![node][CalculateHash(blk, lastHash, lastHash')] = sigBlk]
        ELSE IF blk.type = "send" THEN
            /\ ValidateSignature(sigBlk.signature,
                 PublicKeyOf(distributedLedger[node], blk.previous),
                 CalculateHash(blk, lastHash, lastHash'))
            /\ distributedLedger' = [distributedLedger EXCEPT
                  ![node][CalculateHash(blk, lastHash, lastHash')] = sigBlk]
        ELSE IF blk.type = "receive" THEN
            /\ ValidateSignature(sigBlk.signature,
                 PublicKeyOf(distributedLedger[node], blk.previous),
                 CalculateHash(blk, lastHash, lastHash'))
            /\ distributedLedger' = [distributedLedger EXCEPT
                  ![node][CalculateHash(blk, lastHash, lastHash')] = sigBlk]
        ELSE /\ blk.type = "change"
            /\ ValidateSignature(sigBlk.signature,
                 PublicKeyOf(distributedLedger[node], blk.previous),
                 CalculateHash(blk, lastHash, lastHash'))
            /\ distributedLedger' = [distributedLedger EXCEPT
                  ![node][CalculateHash(blk, lastHash, lastHash')] = sigBlk]
        /\ received' = [received EXCEPT ![node] = @ \ {sigBlk}]

Next ==
    \/ \E pk \in PrivateKey : CreateGenesisBlock(pk)
    \/ \E n \in Node : CreateOpenBlock(n) \/ CreateSendBlock(n) \/ CreateReceiveBlock(n) \/ CreateChangeRepBlock(n)
    \/ \E n \in Node : ProcessBlock(n)
    \/ UNCHANGED <<>>

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

\* ----------------------------------------------------------------------
\* Type invariant (kept minimal to avoid spurious errors)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in DistLedger
    /\ received \in [Node -> SUBSET SignedBlock]

=============================================================================