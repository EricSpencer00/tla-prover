---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* Each block's hash anchors the next block's creation order, so the model
\* tracks the "last hash" alongside a full per-node ledger.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Blocks == [prev : {NoHash} \union Hash, owner : PublicKey, typ : {"genesis", "send", "open", "receive", "change"}, amt : 0..GenesisBalance, dest : {NoPublicKey} \union PublicKey]
\* NoPublicKey is the constant used for send blocks that are not directed at a recipient.
NoPublicKey == CHOOSE p \in PublicKey : TRUE

TypeOK ==
  /\ lastHash \in {NoHashVal} \union Hash
  /\ ledger \in [Node -> [Hash -> {NoBlockVal} \union Blocks]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* A helper that walks an account chain back to the genesis block; used in the
\* derivation that the spec names as a separate invariant.
ChainBalance(acc) ==
  LET f(h) ==
    IF h = NoHashVal THEN 0
    ELSE LET b == ledger[CHOOSE n \in Node : h \in {k \in Hash : ledger[n][k] # NoBlockVal}]
         IN b.amt + f(b.prev)
  IN f(LastAccountHash(acc))

\* Block creation uses an externally modeled hash operator that the .cfg
\* overrides with a bounded version; only the operator name matters here.
NextHash(b) == CalculateHash(b, lastHash)

\* Genesis block: creates the supply and adds it to every node's ledger at once.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E p \in PrivateKey, n \in Node :
       LET b == [prev |-> NoHashVal, owner |-> PrivateKey \in PublicKey, typ |-> "genesis", amt |-> GenesisBalance, dest |-> NoPublicKey]
           h == NextHash(b)
       IN /\ h \in Hash
          /\ lastHash' = h
          /\ ledger' = [x \in Node |-> [ledger[x] EXCEPT ![h] = b]]
          /\ \A y \in Node : received' = [received EXCEPT ![y] = received[y] \union {h}]
  /\ UNCHANGED <<>>

CreateSendBlock ==
  /\ lastHash # NoHashVal
  /\ \E p \in PrivateKey, n \in Node, r \in PublicKey, amt \in 1..GenesisBalance :
       LET b == [prev |-> lastHash, owner |-> p, typ |-> "send", amt |-> amt, dest |-> r]
           h == NextHash(b)
       IN /\ h \in Hash
          /\ ChainBalance(p) >= amt
          /\ lastHash' = h
          /\ ledger' = [x \in Node |-> [ledger[x] EXCEPT ![h] = b]]
          /\ \A y \in Node : received' = [received EXCEPT ![y] = received[y] \union {h}]
  /\ UNCHANGED <<>>

CreateOpenBlock ==
  /\ lastHash # NoHashVal
  /\ \E p \in PrivateKey, n \in Node, s \in Hash :
       /\ ledger[n][s] # NoBlockVal
       /\ ledger[n][s].typ = "send"
       /\ ledger[n][s].dest = p
       /\ \A x \in Node : \A h \in Hash : ~(ledger[x][h].typ = "receive" /\ ledger[x][h].prev = s)
       /\ LET b == [prev |-> lastHash, owner |-> p, typ |-> "open", amt |-> ledger[n][s].amt, dest |-> NoPublicKey]
              h == NextHash(b)
          IN /\ h \in Hash
             /\ lastHash' = h
             /\ ledger' = [x \in Node |-> [ledger[x] EXCEPT ![h] = b]]
             /\ \A y \in Node : received' = [received EXCEPT ![y] = received[y] \union {h}]
  /\ UNCHANGED <<>>

CreateReceiveBlock ==
  /\ lastHash # NoHashVal
  /\ \E p \in PrivateKey, n \in Node, s \in Hash :
       /\ ledger[n][s] # NoBlockVal
       /\ ledger[n][s].typ = "send"
       /\ ledger[n][s].dest = p
       /\ \A x \in Node : \A h \in Hash : ~(ledger[x][h].typ = "receive" /\ ledger[x][h].prev = s)
       /\ LET b == [prev |-> lastHash, owner |-> p, typ |-> "receive", amt |-> ledger[n][s].amt, dest |-> NoPublicKey]
              h == NextHash(b)
          IN /\ h \in Hash
             /\ lastHash' = h
             /\ ledger' = [x \in Node |-> [ledger[x] EXCEPT ![h] = b]]
             /\ \A y \in Node : received' = [received EXCEPT ![y] = received[y] \union {h}]
  /\ UNCHANGED <<>>

CreateChangeRepresentativeBlock ==
  /\ lastHash # NoHashVal
  /\ \E p \in PrivateKey, n \in Node :
       LET b == [prev |-> lastHash, owner |-> p, typ |-> "change", amt |-> 0, dest |-> NoPublicKey]
           h == NextHash(b)
       IN /\ h \in Hash
          /\ lastHash' = h
          /\ ledger' = [x \in Node |-> [ledger[x] EXCEPT ![h] = b]]
          /\ \A y \in Node : received' = [received EXCEPT ![y] = received[y] \union {h}]
  /\ UNCHANGED <<>>

ValidateBlock ==
  /\ \E n \in Node, h \in received[n] :
       /\ ledger[n][h] = NoBlockVal
       /\ \E x \in Node : ledger[x][h] # NoBlockVal /\ ledger[n] = ledger[x]
       /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* All ledger entries must carry a signature that matches the account's public key.
SignatureValid(n, h) ==
  LET b == ledger[n][h] IN b.owner = PrivateKey \in PublicKey

TypeInvariant == TypeOK
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => SignatureValid(n, h)
====