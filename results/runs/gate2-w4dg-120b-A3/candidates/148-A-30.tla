---- MODULE Nano ----
EXTENDS Naturals

\* Ed25519 and Blake2b are modeled as abstract signatures and hashes; the
\* CalculateHashImpl substitution in the .cfg supplies the concrete hash set.
CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal
CONSTANTS CalculateHash, NoHash, NoBlock

\* The ledger is assumed to be a set, not a map, because a real blockchain
\* never mutates the same slot twice -- each block hash is one slot. We model
\* it as a function from hash to block because a function can be read without
\* needing an explicit "exists" test on that slot.
Block == [prev : Hash \cup {NoHash}, signer : PublicKey, btype : {"genesis", "send", "open", "receive", "repr"}, target : PublicKey \cup {NoPublicKey}]

VARIABLES lastHash, ledger, remote

vars == <<lastHash, ledger, remote>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ remote \in [Node -> SUBSET Hash]

\* Successor sums over an account chain; because the chain is a linked list,
\* each account's balance is derived from the blocks that make up that chain.
Successor(acc, h) ==
  IF h = NoHashVal THEN 0
  ELSE LET b == ledger[acc][h] IN
       IF b.signer = acc
         THEN IF b.btype = "receive" THEN Successor(acc, b.prev) + b.target
              ELSE IF b.btype = "open" THEN Successor(acc, b.prev)
              ELSE IF b.btype = "send" THEN Successor(acc, b.prev) - b.target
              ELSE IF b.btype = "repr" THEN Successor(acc, b.prev)
              ELSE Successor(acc, b.prev)
         ELSE Successor(acc, b.prev)

BalanceConsistent == \A acc \in PublicKey : Successor(acc, lastHash) <= GenesisBalance

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ remote = [n \in Node |-> {}]

ValidKey(k) == Cardinality({n \in Node : k \in PrivateKey[n]}) = 1
SignerOf(h) == IF h = NoHashVal THEN NoPublicKey ELSE ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].signer

SignatureValid(h) ==
  LET blk == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h] IN
    ValidKey(blk.signer)

ChainValid(h) == h = NoHashVal \/ (ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].prev # h)

ValidSend(h) ==
  LET blk == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h] IN
    blk.target <= Successor(blk.signer, blk.prev)

ValidOpen(h) ==
  LET blk == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h] IN
    \A n \in Node : ledger[n][blk.prev] = NoBlockVal

ValidReceive(h) ==
  LET blk == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h] IN
    ledger[blk.signer][blk.prev] # NoBlockVal

Validate(h) == SignatureValid(h) /\ ChainValid(h) /\ (Successor(blk.signer, blk.prev) >= blk.target)

SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => SignatureValid(h)

CreateGenesis(n, pub) ==
  /\ lastHash = NoHashVal
  /\ pub \in PrivateKey[n]
  /\ LET h == CalculateHash(<<NoHashVal, pub, "genesis", GenesisBalance>>)[n] IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [prev |-> NoHashVal, signer |-> pub, btype |-> "genesis", target |-> GenesisBalance]]]
       /\ remote' = [m \in Node |-> remote[m] \cup {h}]
  /\ UNCHANGED <<>>

CreateSend(n, pub, rec, amt) ==
  /\ lastHash # NoHashVal
  /\ pub \in PrivateKey[n]
  /\ amt <= Successor(pub, lastHash)
  /\ LET h == CalculateHash(<<lastHash, pub, "send", amt>>)[n] IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [prev |-> lastHash, signer |-> pub, btype |-> "send", target |-> amt]]]
       /\ remote' = [m \in Node |-> remote[m] \cup {h}]
  /\ UNCHANGED <<>>

CreateOpen(n, pub, send) ==
  /\ lastHash # NoHashVal
  /\ pub \in PrivateKey[n]
  /\ send \in remote[n]
  /\ LET h == CalculateHash(<<send, pub, "open", NoPublicKey>>)[n] IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [prev |-> send, signer |-> pub, btype |-> "open", target |-> NoPublicKey]]]
       /\ remote' = [m \in Node |-> remote[m] \cup {h}]
  /\ UNCHANGED <<>>

CreateReceive(n, pub, send) ==
  /\ lastHash # NoHashVal
  /\ pub \in PrivateKey[n]
  /\ send \in remote[n]
  /\ LET h == CalculateHash(<<send, pub, "receive", NoPublicKey>>)[n] IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [prev |-> send, signer |-> pub, btype |-> "receive", target |-> NoPublicKey]]]
       /\ remote' = [m \in Node |-> remote[m] \cup {h}]
  /\ UNCHANGED <<>>

CreateRepr(n, pub) ==
  /\ lastHash # NoHashVal
  /\ pub \in PrivateKey[n]
  /\ LET h == CalculateHash(<<lastHash, pub, "repr", NoPublicKey>>)[n] IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [prev |-> lastHash, signer |-> pub, btype |-> "repr", target |-> NoPublicKey]]]
       /\ remote' = [m \in Node |-> remote[m] \cup {h}]
  /\ UNCHANGED <<>>

ReceiveBlock(n, h) ==
  /\ h \in remote[n]
  /\ Validate(h)
  /\ remote' = [remote EXCEPT ![n] = remote[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

ValidateSend(n, h) == /\ h \in remote[n] /\ ValidSend(h) /\ remote' = [remote EXCEPT ![n] = remote[n] \ {h}] /\ UNCHANGED <<lastHash, ledger>>
ValidateOpen(n, h) == /\ h \in remote[n] /\ ValidOpen(h) /\ remote' = [remote EXCEPT ![n] = remote[n] \ {h}] /\ UNCHANGED <<lastHash, ledger>>
ValidateReceive(n, h) == /\ h \in remote[n] /\ ValidReceive(h) /\ remote' = [remote EXCEPT ![n] = remote[n] \ {h}] /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E n \in Node, pub \in PublicKey : CreateGenesis(n, pub)
  \/ \E n \in Node, pub \in PublicKey, rec \in PublicKey, amt \in 1..GenesisBalance : CreateSend(n, pub, rec, amt)
  \/ \E n \in Node, pub \in PublicKey, send \in Hash : CreateOpen(n, pub, send)
  \/ \E n \in Node, pub \in PublicKey, send \in Hash : CreateReceive(n, pub, send)
  \/ \E n \in Node, pub \in PublicKey : CreateRepr(n, pub)
  \/ \E n \in Node, h \in Hash : ReceiveBlock(n, h)
  \/ \E n \in Node, h \in Hash : ValidateSend(n, h)
  \/ \E n \in Node, h \in Hash : ValidateOpen(n, h)
  \/ \E n \in Node, h \in Hash : ValidateReceive(n, h)

Spec == Init /\ [][Next]_vars

====