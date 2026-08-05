---- MODULE Nano ----
EXTENDS Naturals, Bags
CONSTANTS Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair,
          Node, GenesisBalance, Ownership
VARIABLES lastHash, distributedLedger, received

ASSUME /\ \A d, o, n : CalculateHash(d, o, n) \in BOOLEAN
       /\ KeyPair \in [PrivateKey -> PublicKey]
       /\ GenesisBalance \in Nat
       /\ Ownership \in [Node -> PrivateKey]

Signature == [data : Hash, signedWith : PrivateKey]
NoBlock   == CHOOSE b \in (Signature \X Signature) : FALSE
NoHash    == CHOOSE h \in (Hash \X Hash) : FALSE

Ledger == [Hash -> (Signature \X Signature) \cup {NoBlock}]

\* Signing is a primitive Ed25519 operation; this is a small wrapper around it.
SignHash(h, k) == [data |-> h, signedWith |-> k]
Validate(sig, pub, h) ==
  LET pk == KeyPair[sig.signedWith] IN pk = pub /\ sig.data = h

GenesisBlock ==
  [type |-> "genesis", account |-> (CHOOSE p \in PublicKey : TRUE),
   balance |-> {GenesisBalance}]

Balance == 0..GenesisBalance

OpenBlock == [account : PublicKey, source : Hash, rep : PublicKey, type |-> "open"]
SendBlock == [previous : Hash, balance : Balance, destination : PublicKey,
              type |-> "send"]
ReceiveBlock == [previous : Hash, source : Hash, type |-> "receive"]
ChangeRepBlock == [previous : Hash, rep : PublicKey, type |-> "change"]
Block == GenesisBlock \cup OpenBlock \cup SendBlock \cup ReceiveBlock
         \cup ChangeRepBlock
SignedBlock == [block : Block, sig : Signature]

TopAccount(ledger, pk) ==
  CHOOSE h \in Hash : ledger[h] # NoBlock /\ ledger[h].block.account = pk
                         /\ ~\E k \in Hash : ledger[k] # NoBlock
                                         /\ ledger[k].block.type # "genesis"
                                         /\ ledger[k].block.previous = h

BalanceAt(ledger, h) ==
  LET sb == ledger[h].block IN
    CASE sb.type = "open"   -> BalanceAt(ledger, sb.source)
    []  sb.type = "send"   -> sb.balance
    []  sb.type = "receive"-> BalanceAt(ledger, sb.previous) + BalanceAt(ledger, sb.source)
    []  sb.type = "change" -> BalanceAt(ledger, sb.previous)
    []  sb.type = "genesis"-> sb.balance

RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE LET e \in S : e + Sum(S \ {e})

\* A node may only confirm a block signed by the account it is sitting under.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ distributedLedger \in [Node -> Ledger]
  /\ received \in [Node -> SUBSET SignedBlock]

CryptoOK ==
  /\ \A n \in Node : \A h \in Hash :
       distributedLedger[n][h] # NoBlock => Validate(distributedLedger[n][h].sig,
                     CHOOSE pk \in PublicKey : TopAccount(distributedLedger[n], pk) = h,
                     h)
  /\ \A n \in Node : \A b \in received[n] : Validate(b.sig, b.block.account, b.block)

BalanceOK ==
  \A n \in Node : Sum({BalanceAt(distributedLedger[n],
                     TopAccount(distributedLedger[n], pk)) : pk \in PublicKey}) <= GenesisBalance

Spec == /\ TypeOK /\ CryptoOK /\ BalanceOK /\ TRUE

====