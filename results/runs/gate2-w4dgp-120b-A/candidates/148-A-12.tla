---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash

\* Hashing is abstracted as a constant operator; the .cfg substitutes a concrete, type-correct
\* implementation for CalculateHash (usually a bounded or finite-version of CalculateHashImpl).
VARIABLES lastHash, distributedLedger, received

vars == <<lastHash, distributedLedger, received>>

TypeOK ==
  /\ lastHash \in {NoHashVal} \cup Hash
  /\ distributedLedger \in {NoHashVal} \cup Hash
  /\ received \in [Node -> SUBSET {NoHashVal} \cup Hash]

\* Signature verification: the signer of a block must be the private key whose derived
\* public key is the chain's account owner.
SignatureValid(b) ==
  /\ b \in {NoBlockVal} \cup Hash
  /\ IF b = NoBlockVal
       THEN TRUE
       ELSE \E sk \in PrivateKey :
              /\ \E path \in [Hash -> NO_PATH :> {NoBlockVal} \cup Hash] :
                    /\ path[NoHashVal] = NoBlockVal
                    /\ \A h \in {NoHashVal} \cup Hash : h # NoHashVal => path[h] # NoBlockVal
                    /\ b = CALCULATEHASH(path, sk)
                    /\ path[NoHashVal] = sk
                    /\ \A h \in {NoHashVal} \cup Hash :
                         h # NoHashVal /\ path[h] # NoBlockVal => path[h] \in (distributedLedger \cup {NoBlockVal})
                    /\ LET prev == IF path[NoHashVal] = NoHashVal THEN NoBlockVal ELSE path[path[NoHashVal]] IN
                         IF path[NoHashVal] = NoHashVal
                           THEN \E genesisOwner \in PublicKey : sk = genesisOwner
                           ELSE path[path[NoHashVal]] # NoBlockVal /\ path[path[NoHashVal]] \in (distributedLedger \cup {NoBlockVal})
                           /\ sk \in {NoBlockVal} \cup PrivateKey
              /\ \E pk \in PublicKey : sk \in PrivateKey /\ pk \in PublicKey

\* A public key is the account owner of the chain a block belongs to.
OwnerOf(b) == CHOOSE pk \in PublicKey : b \in {NoBlockVal} \cup (distributedLedger \cup {NoBlockVal})

\* The genesis balance is conserved as a total across all accounts.  The invariant below
\* asserts no coin is created, and this definition is the one it measures; it is not itself
\* a system property.
RECURSIVE SumBalances(_)
SumBalances(X) ==
  IF X = {} THEN 0
  ELSE LET pk == CHOOSE k \in X : TRUE
           x == LET path == CHOOSE p \in {NoHashVal} \cup Hash :
                      /\ p # NoHashVal /\ path[p] # NoBlockVal
                      /\ path[p] = pk
                  IN IF path[NoHashVal] = NoHashVal THEN GenesisBalance ELSE 1
       IN x + SumBalances({k \in X : k # pk})

RECURSIVE AccountBalance(_, _)
AccountBalance(pk, X) ==
  IF X = {} THEN 0
  ELSE LET h == CHOOSE k \in X : OwnerOf(k) = pk
           x == LET path == CHOOSE p \in {NoHashVal} \cup Hash :
                      /\ p # NoHashVal /\ path[p] = h
                      /\ path[NoHashVal] = NoHashVal
                  IN IF path[NoHashVal] = NoHashVal THEN GenesisBalance ELSE 1
       IN x + AccountBalance(pk, X \ {h})

\* A send block must draw from a balance that actually exists on the local ledger copy.
SendFundsAvailable(pk) ==
  LET X == {h \in {NoBlockVal} \cup (distributedLedger \cup {NoBlockVal}) : OwnerOf(h) = pk}
  IN IF X = {} THEN FALSE ELSE AccountBalance(pk, X) >= 1

Init ==
  /\ lastHash = NoHashVal
  /\ distributedLedger = [h \in {NoHashVal} \cup Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(sender) ==
  /\ lastHash = NoHashVal
  /\ LET path == [NoHashVal |-> NoHashVal, NoHashVal |-> sender]
     IN LET h == CALCULATEHASH(path, sender)
        IN /\ lastHash' = h
           /\ distributedLedger' = [hh \in {NoHashVal} \cup Hash |-> IF hh = h THEN h ELSE distributedLedger[hh]]
           /\ received' = [n \in Node |-> received[n] \cup {h}]

\* A send block may only be created if the sender has real funds; every other field can be
\* written arbitrarily.
CreateSendBlock(sender, recipient) ==
  /\ lastHash # NoHashVal
  /\ SendFundsAvailable(sender)
  /\ LET path == [NoHashVal |-> lastHash, lastHash |-> recipient]
     IN LET h == CALCULATEHASH(path, sender)
        IN /\ lastHash' = h
           /\ distributedLedger' = [hh \in {NoHashVal} \cup Hash |-> IF hh = h THEN h ELSE distributedLedger[hh]]
           /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateOpenBlock(accountKey, send) ==
  /\ lastHash # NoHashVal
  /\ \A n \in Node : send \in (distributedLedger \cup {NoBlockVal})
  /\ OwnerOf(send) # accountKey
  /\ LET path == [NoHashVal |-> lastHash, lastHash |-> accountKey]
     IN LET h == CALCULATEHASH(path, accountKey)
        IN /\ lastHash' = h
           /\ distributedLedger' = [hh \in {NoHashVal} \cup Hash |-> IF hh = h THEN h ELSE distributedLedger[hh]]
           /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateReceiveBlock(receiverKey, send) ==
  /\ lastHash # NoHashVal
  /\ \A n \in Node : send \in (distributedLedger \cup {NoBlockVal})
  /\ OwnerOf(send) = receiverKey
  /\ LET path == [NoHashVal |-> lastHash, lastHash |-> send]
     IN LET h == CALCULATEHASH(path, receiverKey)
        IN /\ lastHash' = h
           /\ distributedLedger' = [hh \in {NoHashVal} \cup Hash |-> IF hh = h THEN h ELSE distributedLedger[hh]]
           /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateChangeBlock(accountKey) ==
  /\ lastHash # NoHashVal
  /\ LET path == [NoHashVal |-> lastHash, lastHash |-> accountKey]
     IN LET h == CALCULATEHASH(path, accountKey)
        IN /\ lastHash' = h
           /\ distributedLedger' = [hh \in {NoHashVal} \cup Hash |-> IF hh = h THEN h ELSE distributedLedger[hh]]
           /\ received' = [n \in Node |-> received[n] \cup {h}]

\* Validation checks signatures, existence of referenced blocks, and type-specific rules.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ SignatureValid(h)
  /\ LET path == [p \in {NoHashVal} \cup Hash |-> NoBlockVal]
       IN LET path' == [p \in {NoHashVal} \cup Hash |-> IF p = NoHashVal THEN h ELSE path[p]]
          IN LET path'' == [p \in {NoHashVal} \cup Hash |->
                              IF p = NoHashVal
                                THEN path'[NoHashVal]
                                ELSE IF path'[p] # NoBlockVal /\ path'[p] \in {NoBlockVal} \cup (distributedLedger \cup {NoBlockVal})
                                      THEN path'[p]
                                      ELSE NoBlockVal]
             IN LET send == path''[lastHash] IN
                  /\ IF path''[lastHash] = NoBlockVal THEN TRUE ELSE path''[NoHashVal] # NoHashVal
                  /\ IF path''[lastHash] = NoBlockVal
                       THEN TRUE
                       ELSE OwnerOf(send) # OwnerOf(path''[NoHashVal])
                  /\ IF path''[lastHash] = NoBlockVal
                       THEN TRUE
                       ELSE IF path''[lastHash] = OwnerOf(send)
                            THEN send \in (distributedLedger \cup {NoBlockVal}) /\ SendFundsAvailable(OwnerOf(send))
                            ELSE TRUE
                  /\ LET senderAcct == OwnerOf(path''[NoHashVal]) IN
                       IF path''[lastHash] # NoBlockVal /\ path''[lastHash] = OwnerOf(send)
                         THEN senderAcct # OwnerOf(send)
                         ELSE TRUE
                  /\ LET receiverAcct == OwnerOf(path''[lastHash]) IN
                       IF receiverAcct = OwnerOf(send) THEN TRUE
                       ELSE
                         LET amountSent == IF path''[lastHash] = OwnerOf(send) THEN 1 ELSE 0 IN
                         LET amountReceived == IF path''[lastHash] = OwnerOf(send) THEN 0 ELSE 1 IN
                         LET balanceAtPrev == LET X == {h \in {NoBlockVal} \cup (distributedLedger \cup {NoBlockVal}) : OwnerOf(h) = receiverAcct}
                                               IN IF X = {} THEN 0 ELSE AccountBalance(receiverAcct, X)
                         IN (balanceAtPrev + amountReceived) >= amountSent
                  /\ distributedLedger' = [hh \in {NoHashVal} \cup Hash |-> IF hh = h THEN h ELSE distributedLedger[hh]]
                  /\ received' = [Node |-> IF Node = n THEN received[n] \ {h} ELSE received[Node]]
  /\ UNCHANGED lastHash

Next ==
  \/ \E sender \in PublicKey : CreateGenesisBlock(sender)
  \/ \E sender, recipient \in PublicKey : CreateSendBlock(sender, recipient)
  \/ \E accountKey \in PublicKey, send \in {NoHashVal} \cup Hash : CreateOpenBlock(accountKey, send)
  \/ \E receiverKey \in PublicKey, send \in {NoHashVal} \cup Hash : CreateReceiveBlock(receiverKey, send)
  \/ \E accountKey \in PublicKey : CreateChangeBlock(accountKey)
  \/ \E n \in Node, h \in {NoHashVal} \cup Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger copy must have a signature matching the account
\* chain it belongs to; this must hold regardless of how slow validation is.
SafetyInvariant == \A h \in {NoHashVal} \cup Hash : h \in (distributedLedger \cup {NoBlockVal}) => SignatureValid(h)

====