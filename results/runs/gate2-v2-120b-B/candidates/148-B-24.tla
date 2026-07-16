---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,                      \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),      \* An action calculating the hash of a block
    PrivateKey,                \* The set of all Ed25519 private keys
    PublicKey,                 \* The set of all Ed25519 public keys
    KeyPair,                   \* The public key paired with each private key
    Node,                      \* The set of all nodes in the network
    GenesisBalance,            \* The total number of coins in the network
    Ownership                  \* The private key owned by each node

VARIABLES
    lastHash,                  \* The last calculated block hash (or NoHash)
    distributedLedger,         \* The distributed ledger of confirmed blocks
    received                   \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
          /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Cryptographic primitives (modelled abstractly)
\* ----------------------------------------------------------------------
Signature ==
    [data       : Hash,
     signedWith : PrivateKey]

SignHash(hash, privateKey) ==
    [data       |-> hash,
     signedWith |-> privateKey]

ValidateSignature(sig, expectedPublicKey, expectedHash) ==
    LET pub == KeyPair[sig.signedWith] IN
    /\ pub = expectedPublicKey
    /\ sig.data = expectedHash

\* ----------------------------------------------------------------------
\* Block definitions
\* ----------------------------------------------------------------------
AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type    |-> "genesis",
     account |-> PublicKey,
     balance |-> GenesisBalance]

SendBlock ==
    [previous   |-> Hash,
     balance    |-> AccountBalance,
     destination|-> PublicKey,
     type       |-> "send"]

OpenBlock ==
    [account |-> PublicKey,
     source  |-> Hash,
     rep     |-> PublicKey,
     type    |-> "open"]

ReceiveBlock ==
    [previous |-> Hash,
     source   |-> Hash,
     type     |-> "receive"]

ChangeRepBlock ==
    [previous |-> Hash,
     rep      |-> PublicKey,
     type     |-> "change"]

Block ==
    GenesisBlock
    \cup SendBlock
    \cup OpenBlock
    \cup ReceiveBlock
    \cup ChangeRepBlock

SignedBlock ==
    [block     : Block,
     signature : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock
NoHash  == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

\* ----------------------------------------------------------------------
\* Utility functions
\* ----------------------------------------------------------------------
GenesisBlockExists ==
    lastHash # NoHash

IsAccountOpen(ledger, pub) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb # NoBlock /\ sb.block.type \in {"genesis", "open"} /\ sb.block.account = pub

IsSendReceived(ledger, src) ==
    \E h \in Hash :
        LET sb == ledger[h] IN
        sb # NoBlock /\ sb.block.type \in {"open", "receive"} /\ sb.block.source = src

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, h) ==
    LET sb == ledger[h] IN
    IF sb # NoBlock THEN
        IF sb.block.type \in {"genesis", "open"} THEN sb.block.account
        ELSE PublicKeyOf(ledger, sb.block.previous)
    ELSE PublicKeyOf(ledger, NoHash)  \* unreachable, but keeps recursion total

TopBlock(ledger, pub) ==
    CHOOSE h \in Hash :
        LET sb == ledger[h] IN
        sb # NoBlock /\ PublicKeyOf(ledger, h) = pub /\
        ~\E h2 \in Hash :
            LET sb2 == ledger[h2] IN
            sb2 # NoBlock /\ sb2.block.type \in {"send", "receive", "change"} /\
            sb2.block.previous = h

RECURSIVE BalanceAt(_, _)
BalanceAt(ledger, h) ==
    LET sb == ledger[h] IN
    CASE sb.block.type = "open"    -> ValueOfSendBlock(ledger, sb.block.source)
       [] sb.block.type = "send"    -> sb.block.balance
       [] sb.block.type = "receive" -> BalanceAt(ledger, sb.block.previous)
                                      + ValueOfSendBlock(ledger, sb.block.source)
       [] sb.block.type = "change"  -> BalanceAt(ledger, sb.block.previous)
       [] sb.block.type = "genesis" -> sb.block.balance

ValueOfSendBlock(ledger, h) ==
    LET sb == ledger[h] IN
    BalanceAt(ledger, sb.block.previous) - sb.block.balance

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A n \in Node :
          LET ledger == distributedLedger[n] IN
          \A h \in Hash :
            LET sb == ledger[h] IN
            sb # NoBlock =>
                ValidateSignature(sb.signature,
                                   PublicKeyOf(ledger, h),
                                   h)

BalanceInvariant ==
    /\ \A n \in Node :
          LET ledger == distributedLedger[n] IN
          LET openAccs == {pub \in PublicKey : IsAccountOpen(ledger, pub)} IN
          LET tops     == {TopBlock(ledger, pub) : pub \in openAccs} IN
          LET acctBal  == \{h \in tops : BalanceAt(ledger, h)} IN
          IF GenesisBlockExists THEN
              \A b \in acctBal : b \in AccountBalance
          ELSE TRUE

SafetyInvariant == CryptographicInvariant

\* ----------------------------------------------------------------------
\* Genesis creation (single‑use)
\* ----------------------------------------------------------------------
CreateGenesisBlock(priv) ==
    LET pub == KeyPair[priv] IN
    /\ ~GenesisBlockExists
    /\ CalculateHash([type |-> "genesis", account |-> pub, balance |-> GenesisBalance],
                     lastHash, newHash)
    /\ distributedLedger' = [n \in Node |-> [h \in Hash |-> 
                        IF h = newHash THEN
                            [block |-> [type |-> "genesis",
                                       account |-> pub,
                                       balance |-> GenesisBalance],
                             signature |-> SignHash(newHash, priv)]
                        ELSE NoBlock]]
    /\ lastHash' = newHash
    /\ UNCHANGED received

\* ----------------------------------------------------------------------
\* Block creation helpers
\* ----------------------------------------------------------------------
ValidateOpenBlock(ledger, blk) ==
    /\ blk.type = "open"
    /\ ledger[blk.source] # NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination = blk.account

ValidateSendBlock(ledger, blk) ==
    /\ blk.type = "send"
    /\ ledger[blk.previous] # NoBlock
    /\ blk.balance <= BalanceAt(ledger, blk.previous)

ValidateReceiveBlock(ledger, blk) ==
    /\ blk.type = "receive"
    /\ ledger[blk.previous] # NoBlock
    /\ ledger[blk.source] # NoBlock
    /\ ledger[blk.source].block.type = "send"
    /\ ledger[blk.source].block.destination = 
          PublicKeyOf(ledger, blk.previous)

ValidateChangeBlock(ledger, blk) ==
    /\ blk.type = "change"
    /\ ledger[blk.previous] # NoBlock

\* ----------------------------------------------------------------------
\* Block creation actions (append to received)
\* ----------------------------------------------------------------------
CreateOpenBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E repPub \in PublicKey :
         \E src \in Hash :
            LET blk == [account |-> pub,
                        source  |-> src,
                        rep     |-> repPub,
                        type    |-> "open"] IN
            /\ ValidateOpenBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' = [received EXCEPT ![node] = @ \cup
                 { [block |-> blk,
                    signature |-> SignHash(newHash, priv)}]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

CreateSendBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prev \in Hash :
         ledger[prev] # NoBlock /\
         PublicKeyOf(ledger, prev) = pub /\
         \E dest \in PublicKey :
           \E bal \in AccountBalance :
              LET blk == [previous |-> prev,
                         balance  |-> bal,
                         destination |-> dest,
                         type     |-> "send"] IN
              /\ ValidateSendBlock(ledger, blk)
              /\ CalculateHash(blk, lastHash, newHash)
              /\ received' = [received EXCEPT ![node] = @ \cup
                   { [block |-> blk,
                      signature |-> SignHash(newHash, priv)}]]
              /\ UNCHANGED <<lastHash, distributedLedger>>

CreateReceiveBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prev \in Hash :
         ledger[prev] # NoBlock /\
         PublicKeyOf(ledger, prev) = pub /\
         \E src \in Hash :
            LET blk == [previous |-> prev,
                       source  |-> src,
                       type    |-> "receive"] IN
            /\ ValidateReceiveBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' = [received EXCEPT ![node] = @ \cup
                 { [block |-> blk,
                    signature |-> SignHash(newHash, priv)}]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

CreateChangeRepBlock(node) ==
    LET priv == Ownership[node] IN
    LET pub  == KeyPair[priv] IN
    LET ledger == distributedLedger[node] IN
    /\ \E prev \in Hash :
         ledger[prev] # NoBlock /\
         PublicKeyOf(ledger, prev) = pub /\
         \E newRep \in PublicKey :
            LET blk == [previous |-> prev,
                       rep      |-> newRep,
                       type     |-> "change"] IN
            /\ ValidateChangeBlock(ledger, blk)
            /\ CalculateHash(blk, lastHash, newHash)
            /\ received' = [received EXCEPT ![node] = @ \cup
                 { [block |-> blk,
                    signature |-> SignHash(newHash, priv)}]]
            /\ UNCHANGED <<lastHash, distributedLedger>>

CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

\* ----------------------------------------------------------------------
\* Processing actions (move from received to ledger)
\* ----------------------------------------------------------------------
ProcessBlock(node) ==
    /\ \E sb \in received[node] :
          LET blk == sb.block IN
          /\ ( /\ blk.type = "open"
                /\ ValidateOpenBlock(distributedLedger[node], blk)
                /\ ValidateSignature(sb.signature, blk.account,
                                      [type |-> "open", account |-> blk.account,
                                       source |-> blk.source, rep |-> blk.rep])
                /\ CalculateHash(blk, lastHash, newHash)
                /\ distributedLedger' =
                     [distributedLedger EXCEPT
                         ![node][newHash] = sb]
                /\ lastHash' = newHash
                /\ received' = [received EXCEPT ![node] = @ \ {sb}]
                )
           \/ ( /\ blk.type = "send"
                /\ ValidateSendBlock(distributedLedger[node], blk)
                /\ ValidateSignature(sb.signature,
                       PublicKeyOf(distributedLedger[node], blk.previous),
                       newHash)
                /\ CalculateHash(blk, lastHash, newHash)
                /\ distributedLedger' =
                     [distributedLedger EXCEPT
                         ![node][newHash] = sb]
                /\ lastHash' = newHash
                /\ received' = [received EXCEPT ![node] = @ \ {sb}]
                )
           \/ ( /\ blk.type = "receive"
                /\ ValidateReceiveBlock(distributedLedger[node], blk)
                /\ ~IsSendReceived(distributedLedger[node], blk.source)
                /\ ValidateSignature(sb.signature,
                       PublicKeyOf(distributedLedger[node], blk.previous),
                       newHash)
                /\ CalculateHash(blk, lastHash, newHash)
                /\ distributedLedger' =
                     [distributedLedger EXCEPT
                         ![node][newHash] = sb]
                /\ lastHash' = newHash
                /\ received' = [received EXCEPT ![node] = @ \ {sb}]
                )
           \/ ( /\ blk.type = "change"
                /\ ValidateChangeBlock(distributedLedger[node], blk)
                /\ ValidateSignature(sb.signature,
                       PublicKeyOf(distributedLedger[node], blk.previous),
                       newHash)
                /\ CalculateHash(blk, lastHash, newHash)
                /\ distributedLedger' =
                     [distributedLedger EXCEPT
                         ![node][newHash] = sb]
                /\ lastHash' = newHash
                /\ received' = [received EXCEPT ![node] = @ \ {sb}]
                )
          )

\* ----------------------------------------------------------------------
\* Initialization and next-state relation
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E priv \in PrivateKey : CreateGenesisBlock(priv)
    \/ \E n \in Node : CreateBlock(n)
    \/ \E n \in Node : ProcessBlock(n)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

====