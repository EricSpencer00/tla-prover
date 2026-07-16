---- MODULE Nano ----
(***************************************************************************)
(* An outdated and not-ultimately-useful specification of the original     *)
(* protocol used by the Nano blockchain. Primarily interesting as an       *)
(* example of how to model hash functions and cryptographic signatures,    *)
(* and the difficulties in using finite modelchecking to analyze           *)
(* blockchain-like data structures or anything else that records action    *)
(* history in an ordered way.                                              *)
(***************************************************************************)

EXTENDS Naturals, Bags, FiniteSets

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

(* --------------------------------------------------------------------- *)
(* Helper constants for the model (they will be instantiated in the cfg) *)
Hashes        == 1..3
NoHashVal     == 0
BlockVals     == 1..3

(* --------------------------------------------------------------------- *)
(* Functions to sign hashes with a private key and validate signatures   *)
(* against public key.                                                   *)

Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data |-> hash, signedWith |-> privateKey]

ValidateSignature(sig, expectedPub, expectedHash) ==
    LET pub == KeyPair[sig.signedWith] IN
    /\ pub = expectedPub
    /\ sig.data = expectedHash

(* --------------------------------------------------------------------- *)
(* Definitions of the various block types                               *)

AccountBalance == 0 .. GenesisBalance

GenesisBlock(publicKey) ==
    [type |-> "genesis",
     account |-> publicKey,
     balance |-> GenesisBalance]

SendBlock(previous, balance, destination) ==
    [type |-> "send",
     previous |-> previous,
     balance |-> balance,
     destination |-> destination]

OpenBlock(account, source, rep) ==
    [type |-> "open",
     account |-> account,
     source |-> source,
     rep |-> rep]

ReceiveBlock(previous, source) ==
    [type |-> "receive",
     previous |-> previous,
     source |-> source]

ChangeBlock(previous, rep) ==
    [type |-> "change",
     previous |-> previous,
     rep |-> rep]

Block ==
    { b \in [type : {"genesis", "send", "open", "receive", "change"},
             account : PublicKey,
             balance : Nat,
             previous : Hash,
             source : Hash,
             destination : PublicKey,
             rep : PublicKey] :
        (b.type = "genesis"    => b.balance = GenesisBalance /\ b.account \in PublicKey)
        /\ (b.type = "send"    => b.previous \in Hash /\ b.balance \in AccountBalance /\ b.destination \in PublicKey)
        /\ (b.type = "open"    => b.account \in PublicKey /\ b.source \in Hash /\ b.rep \in PublicKey)
        /\ (b.type = "receive"=> b.previous \in Hash /\ b.source \in Hash)
        /\ (b.type = "change" => b.previous \in Hash /\ b.rep \in PublicKey) }

SignedBlock == [block : Block, signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock

NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(* --------------------------------------------------------------------- *)
(* Utility functions for block lattice properties                         *)

PublicKeyOf(ledger, hash) ==
    IF ledger[hash] = NoBlock THEN NoHash
    ELSE
        LET blk == ledger[hash].block IN
        IF blk.type \in {"genesis", "open"}
        THEN blk.account
        ELSE PublicKeyOf(ledger, blk.previous)

RECURSIVE BalanceAt(_,_)
BalanceAt(ledger, hash) ==
    IF ledger[hash] = NoBlock THEN 0
    ELSE
        LET blk == ledger[hash].block IN
        CASE blk.type = "genesis" -> blk.balance
         [] blk.type = "send"    -> blk.balance
         [] blk.type = "receive" -> BalanceAt(ledger, blk.previous) + 
                                   BalanceAt(ledger, blk.source)
         [] blk.type = "open"    -> BalanceAt(ledger, blk.source)
         [] blk.type = "change"  -> BalanceAt(ledger, blk.previous)

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {} THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE IN
        e + SumBag(B (-) SetToBag({e}))

(* --------------------------------------------------------------------- *)
(* Safety invariant (cryptographic correctness)                          *)

SafetyInvariant ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A hash \in Hash :
            LET sb == ledger[hash] IN
            sb /= NoBlock =>
                LET pub == PublicKeyOf(ledger, hash) IN
                ValidateSignature(sb.signature, pub, hash)

(* --------------------------------------------------------------------- *)
(* Initial predicate                                                     *)

Init ==
    /\ lastHash = NoHashVal
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

(* --------------------------------------------------------------------- *)
(* Actions                                                               *)

CreateGenesisBlock ==
    \E pk \in PublicKey :
        /\ ~\E n \in Node : \E h \in Hash : distributedLedger[n][h].block.type = "genesis"
        /\ \E n \in Node :
            /\ \E h \in Hash :
                /\ CalculateHash(GenesisBlock(pk), lastHash, h)
                /\ distributedLedger' = [distributedLedger EXCEPT ![n][h] = 
                       [block |-> GenesisBlock(pk),
                        signature |-> SignHash(h, Ownership[n])]]
                /\ UNCHANGED <<lastHash, received>>

CreateOpenBlock(node) ==
    \E srcHash \in Hash :
        \E rep \in PublicKey :
            /\ distributedLedger[node][srcHash] /= NoBlock
            /\ distributedLedger[node][srcHash].block.type = "send"
            /\ \E h \in Hash :
                /\ CalculateHash(OpenBlock(KeyPair[Ownership[node]], srcHash, rep), lastHash, h)
                /\ received' = [received EXCEPT ![node] = @ \cup {
                      [block |-> OpenBlock(KeyPair[Ownership[node]], srcHash, rep),
                       signature |-> SignHash(h, Ownership[node])]}]
                /\ UNCHANGED <<lastHash, distributedLedger>>

CreateSendBlock(node) ==
    \E prev \in Hash :
        \E dst \in PublicKey :
            \E bal \in AccountBalance :
                /\ distributedLedger[node][prev] /= NoBlock
                /\ BalanceAt(distributedLedger[node], prev) >= bal
                /\ \E h \in Hash :
                    /\ CalculateHash(SendBlock(prev, bal, dst), lastHash, h)
                    /\ received' = [received EXCEPT ![node] = @ \cup {
                          [block |-> SendBlock(prev, bal, dst),
                           signature |-> SignHash(h, Ownership[node])]}]
                    /\ UNCHANGED <<lastHash, distributedLedger>>

CreateReceiveBlock(node) ==
    \E prev \in Hash :
        \E src \in Hash :
            /\ distributedLedger[node][prev] /= NoBlock
            /\ distributedLedger[node][src] /= NoBlock
            /\ distributedLedger[node][src].block.type = "send"
            /\ distributedLedger[node][src].block.destination = KeyPair[Ownership[node]]
            /\ \E h \in Hash :
                /\ CalculateHash(ReceiveBlock(prev, src), lastHash, h)
                /\ received' = [received EXCEPT ![node] = @ \cup {
                      [block |-> ReceiveBlock(prev, src),
                       signature |-> SignHash(h, Ownership[node])]}]
                /\ UNCHANGED <<lastHash, distributedLedger>>

CreateChangeBlock(node) ==
    \E prev \in Hash :
        \E newRep \in PublicKey :
            /\ distributedLedger[node][prev] /= NoBlock
            /\ \E h \in Hash :
                /\ CalculateHash(ChangeBlock(prev, newRep), lastHash, h)
                /\ received' = [received EXCEPT ![node] = @ \cup {
                      [block |-> ChangeBlock(prev, newRep),
                       signature |-> SignHash(h, Ownership[node])]}]
                /\ UNCHANGED <<lastHash, distributedLedger>>

ProcessBlock(node) ==
    \E sb \in received[node] :
        LET blk == sb.block IN
        /\ \IF blk.type = "open" THEN
                /\ publicKey = KeyPair[Ownership[node]]
                /\ ValidateSignature(sb.signature, publicKey, blk.source)
                /\ distributedLedger' = [distributedLedger EXCEPT ![node][blk.source] = sb]
           \ELSE IF blk.type = "send" THEN
                /\ publicKey = KeyPair[Ownership[node]]
                /\ ValidateSignature(sb.signature, publicKey, blk.previous)
                /\ distributedLedger' = [distributedLedger EXCEPT ![node][blk.previous] = sb]
           \ELSE IF blk.type = "receive" THEN
                /\ publicKey = KeyPair[Ownership[node]]
                /\ ValidateSignature(sb.signature, publicKey,
                        IF blk.previous # NoHashVal THEN blk.previous ELSE blk.source)
                /\ distributedLedger' = [distributedLedger EXCEPT ![node][blk.previous] = sb]
           \ELSE (* change block *)
                /\ publicKey = KeyPair[Ownership[node]]
                /\ ValidateSignature(sb.signature, publicKey, blk.previous)
                /\ distributedLedger' = [distributedLedger EXCEPT ![node][blk.previous] = sb]
        /\ received' = [received EXCEPT ![node] = @ \ {sb}]
        /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesisBlock
    \/ \E n \in Node : CreateOpenBlock(n)
    \/ \E n \in Node : CreateSendBlock(n)
    \/ \E n \in Node : CreateReceiveBlock(n)
    \/ \E n \in Node : CreateChangeBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec ==
    Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => SafetyInvariant

====