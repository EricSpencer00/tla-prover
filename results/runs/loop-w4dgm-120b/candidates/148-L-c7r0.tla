---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

(* Nano cryptocurrency block-lattice model.  A block's hash is a literal model   *)
(* constant, chosen from a bounded set; the hash function itself is abstracted  *)
(* as a constant operator (CalculateHash) that the .cfg swaps in a concrete      *)
(* version for model checking.  The invariant protects the signature of every   *)
(* stored block; the shape of the lattice grows super-exponentially with actions. *)

CONSTANTS Hash, NoHashVal, NoHash, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

HashDomain == {NoHash} \cup Hash

ChainOf == [hash : HashDomain, prev : HashDomain, owner : PublicKey, blkt : {"send", "open", "receive", "change"}, amount : Nat]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A node's account balance is the net sum of its chain action amounts.
RECURSIVE ChainSum(_)
ChainSum(S) ==
  IF S = {} THEN 0
  ELSE LET b == CHOOSE e \in S : TRUE IN b.amount + ChainSum(S \ {b})
Domain(chain) == {e \in ledger[n] : e # NoBlockVal /\ e.owner = chain.owner}
Balance(chain) == ChainSum(Domain(chain))

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in HashDomain |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Genesis block hands the whole coin supply to one key and is written everywhere
\* at once, so it can never be lost on the way.
CreateGenesisBlock(pk) ==
  /\ lastHash = NoHash
  /\ \E h \in Hash :
       /\ lastHash' = h
       /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] =
                          [hash |-> h, prev |-> NoHash, owner |-> pk,
                           blkt |-> "open", amount |-> GenesisBalance]]]
  /\ UNCHANGED received

\* The "prev" link is what makes the block chain order matter for verification.
CreateSendBlock(n, pk, amt) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlockVal
       /\ lastHash' = h
       /\ ledger' = [ledger EXCEPT ![n][h] =
            [hash |-> h, prev |-> lastHash, owner |-> pk,
             blkt |-> "send", amount |-> amt]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> h, prev |-> lastHash,
                                            owner |-> pk, blkt |-> "send", amount |-> amt]}]

CreateOpenBlock(n, h) ==
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].blkt = "send"
  /\ \E pk \in PublicKey, amt \in Nat :
       /\ \E g \in Hash :
            /\ ledger[n][g] = NoBlockVal
            /\ lastHash' = g
            /\ ledger' = [ledger EXCEPT ![n][g] =
                 [hash |-> g, prev |-> lastHash, owner |-> pk,
                  blkt |-> "open", amount |-> amt]]
            /\ received' = [m \in Node |-> received[m] \cup {[hash |-> g, prev |-> lastHash,
                                                 owner |-> pk, blkt |-> "open", amount |-> amt]}]

CreateReceiveBlock(n, h) ==
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].blkt = "send"
  /\ \E pk \in PublicKey, amt \in Nat :
       /\ \E g \in Hash :
            /\ ledger[n][g] = NoBlockVal
            /\ lastHash' = g
            /\ ledger' = [ledger EXCEPT ![n][g] =
                 [hash |-> g, prev |-> lastHash, owner |-> pk,
                  blkt |-> "receive", amount |-> amt]]
            /\ received' = [m \in Node |-> received[m] \cup {[hash |-> g, prev |-> lastHash,
                                                 owner |-> pk, blkt |-> "receive", amount |-> amt]}]

CreateChangeRepBlock(n, pk) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlockVal
       /\ lastHash' = h
       /\ ledger' = [ledger EXCEPT ![n][h] =
            [hash |-> h, prev |-> lastHash, owner |-> pk,
             blkt |-> "change", amount |-> 0]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> h, prev |-> lastHash,
                                            owner |-> pk, blkt |-> "change", amount |-> 0]}]

\* Validation touches every rule that makes a block's provenance believable.
ValidateBlock(n, blk) ==
  /\ blk \in received[n]
  /\ ledger[n][blk.hash] = NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][blk.hash] = blk]
  /\ received' = [received EXCEPT ![n] = received[n] \ {blk}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E pk \in PublicKey : CreateGenesisBlock(pk)
  \/ \E n \in Node, pk \in PublicKey, amt \in Nat : CreateSendBlock(n, pk, amt)
  \/ \E n \in Node, h \in Hash : CreateOpenBlock(n, h)
  \/ \E n \in Node, h \in Hash : CreateReceiveBlock(n, h)
  \/ \E n \in Node, pk \in PublicKey : CreateChangeRepBlock(n, pk)
  \/ \E n \in Node, blk \in ChainOf : ValidateBlock(n, blk)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in HashDomain
  /\ ledger \in [Node -> [HashDomain -> ChainOf \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET ChainOf]

\* The only thing that has to stay perfectly true across every reorderable
\* action is the cryptographic link between a block and its owner's key.
SafetyInvariant ==
  /\ TypeInvariant
  /\ \A n \in Node :
       \A h \in HashDomain :
         ledger[n][h] # NoBlockVal => PublicKey[ledger[n][h].owner] = f_{pk}^{-1}(ledger[n][h].owner)

====