---- MODULE Nano ----
EXTENDS Naturals, Bags
CONSTANTS
    Hash, CalculateHash(_,_,_), PrivateKey, PublicKey, KeyPair, Node,
    GenesisBalance, Ownership
VARIABLES lastHash, distributedLedger, received

ASSUME /\ \A d, o, n : CalculateHash(d, o, n) \in BOOLEAN
       /\ KeyPair \in [PrivateKey -> PublicKey]
       /\ GenesisBalance \in Nat
       /\ Ownership \in [Node -> PrivateKey]

Signature == [data : Hash, signedWith : PrivateKey]
NoBlock == CHOOSE b \in (Block \cup {CHOOSE x : FALSE})
NoHash == CHOOSE h \in (Hash \cup {CHOOSE x : FALSE})
Ledger == [Hash -> Signature \cup {NoBlock}]

SignHash(hash, privateKey) == [data |-> hash, signedWith |-> privateKey]
ValidateSignature(s, pk, h) ==
    LET pk2 == KeyPair[s.signedWith] IN /\ pk2 = pk /\ s.data = h

Block ==
    [type : {"genesis", "send", "open", "receive", "change"},
     account : PublicKey, balance : {GenesisBalance},
     previous : Hash, source : Hash, destination : PublicKey, rep : PublicKey]

PublicKeyOf(ledger, hash) ==
    LET s == ledger[hash] IN
    IF s.block.type \in {"genesis", "open"} THEN s.block.account
    ELSE PublicKeyOf(ledger, s.block.previous)

BalanceAt(ledger, hash) ==
    LET s == ledger[hash] IN
    CASE s.block.type = "open"   -> BalanceAt(ledger, s.block.source)
      [] s.block.type = "send"   -> s.block.balance
      [] s.block.type = "receive"-> BalanceAt(ledger, s.block.previous)
                                   + BalanceAt(ledger, s.block.source)
      [] s.block.type = "change" -> BalanceAt(ledger, s.block.previous)
      [] s.block.type = "genesis"-> s.block.balance

GenesisBlockExists == lastHash # NoHash
IsAccountOpen(ledger, pk) ==
    \E h \in Hash : ledger[h] # NoBlock /\ ledger[h].block.account = pk
    /\ ledger[h].block.type \in {"genesis", "open"}

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
    /\ ~GenesisBlockExists
    /\ \E h \in Hash:
         /\ CalculateHash([type |-> "genesis", account |-> KeyPair[k],
                          balance |-> GenesisBalance], lastHash, h)
         /\ lastHash' = h
         /\ distributedLedger' =
              [n \in Node |-> [distributedLedger[n] EXCEPT ![h] = SignHash(h, k)]]
    /\ UNCHANGED received

Next == \E n \in Node : CreateGenesisBlock(Ownership[n])
Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM BalanceInvariant ==
    Spec => \A n \in Node : \A h \in Hash :
        (distributedLedger[n][h] # NoBlock =>
            BalanceAt(distributedLedger[n], h) <= GenesisBalance)
====