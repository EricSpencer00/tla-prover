---------------------------- MODULE Nano ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal,
    CalculateHash,
    NoHash,
    NoBlock

VARIABLES
    lastHash,
    ledger,
    received

vars == <<lastHash, ledger, received>>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> [kind: {"send", "receive", "open", "change", "genesis"},
                                     account: PublicKey,
                                     prev: Hash \cup {NoHash},
                                     src: Hash \cup {NoHash},
                                     amt: 0..GenesisBalance,
                                     sig: PrivateKey]]]
    /\ received \in [Node -> SUBSET [kind: {"send", "receive", "open", "change", "genesis"},
                                      account: PublicKey,
                                      prev: Hash \cup {NoHash},
                                      src: Hash \cup {NoHash},
                                      amt: 0..GenesisBalance,
                                      sig: PrivateKey]]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* The hash of block b is derived from its contents; the constant ComputeHash
\* is a placeholder for a real hash function, here modeled abstractly.
CreateGenesisBlock ==
    /\ lastHash = NoHash
    /\ \E n \in Node, sk \in PrivateKey, pk \in PublicKey :
         /\ ledger' = [m \in Node |->
                        [ledger[m] EXCEPT ![NoHash] =
                            [kind |-> "genesis", account |-> pk, prev |-> NoHash,
                             src |-> NoHash, amt |-> GenesisBalance, sig |-> sk]]]
         /\ lastHash' = NoHash
    /\ UNCHANGED received

ValidSignature(b) == b.sig \in {sk \in PrivateKey : pk \in PublicKey /\ pk = b.account}

\* The balance of an account is the sum of its own receive/open blocks minus
\* its send blocks, so the account chain is walked recursively.
\* This is defined as a helper, not a model action.
AccountBalance(chain) ==
    LET Sum(S) ==
        IF S = {} THEN 0
        ELSE LET b == CHOOSE e \in S : TRUE IN b.amt + Sum(S \ {b})
    IN Sum(chain)

\* chainOf(a) is the set of block hashes in the chain belonging to account a.
ChainOf(a) ==
    {h \in Hash : ledger[CHOOSE n \in Node : TRUE][h] # NoBlockVal
                    /\ ledger[CHOOSE n \in Node : TRUE][h].account = a}

CreateSendBlock(n, sk, toPk, amt) ==
    /\ lastHash \in Hash
    /\ ledger[n][lastHash] # NoBlockVal
    /\ ledger[n][lastHash].account \in PublicKey
    /\ amt > 0
    /\ amt <= AccountBalance(ChainOf(ledger[n][lastHash].account))
    /\ LET h2 == CalculateHash([kind |-> "send", account |-> ledger[n][lastHash].account,
                                prev |-> lastHash, src |-> NoHash, amt |-> amt, sig |-> sk])
       IN /\ ledger' = [ledger EXCEPT ![n][h2] =
                          [kind |-> "send", account |-> ledger[n][lastHash].account,
                           prev |-> lastHash, src |-> NoHash, amt |-> amt, sig |-> sk]]
          /\ lastHash' = h2
          /\ received' = [m \in Node |-> received[m] \cup
                            {[kind |-> "send", account |-> ledger[n][lastHash].account,
                              prev |-> lastHash, src |-> NoHash, amt |-> amt, sig |-> sk]}]

CreateOpenBlock(n, sk, src) ==
    /\ lastHash \in Hash
    /\ ledger[n][lastHash] # NoBlockVal
    /\ src \in Hash
    /\ ledger[n][src] # NoBlockVal
    /\ ledger[n][src].account # ledger[n][lastHash].account
    /\ ~(\E h \in Hash : ledger[n][h] # NoBlockVal /\ ledger[n][h].kind = "open"
                            /\ ledger[n][h].src = src)
    /\ LET h2 == CalculateHash([kind |-> "open", account |-> ledger[n][src].account,
                                prev |-> lastHash, src |-> src, amt |-> ledger[n][src].amt, sig |-> sk])
       IN /\ ledger' = [ledger EXCEPT ![n][h2] =
                          [kind |-> "open", account |-> ledger[n][src].account,
                           prev |-> lastHash, src |-> src, amt |-> ledger[n][src].amt, sig |-> sk]]
          /\ lastHash' = h2
          /\ received' = [m \in Node |-> received[m] \cup
                            {[kind |-> "open", account |-> ledger[n][src].account,
                              prev |-> lastHash, src |-> src, amt |-> ledger[n][src].amt, sig |-> sk]}]

CreateReceiveBlock(n, sk, src) ==
    /\ lastHash \in Hash
    /\ ledger[n][lastHash] # NoBlockVal
    /\ src \in Hash
    /\ ledger[n][src] # NoBlockVal
    /\ ledger[n][src].src \in Hash
    /\ ledger[n][src].account \in PublicKey
    /\ ~(\E h \in Hash : ledger[n][h] # NoBlockVal /\ ledger[n][h].kind = "receive"
                            /\ ledger[n][h].src = src)
    /\ LET h2 == CalculateHash([kind |-> "receive", account |-> ledger[n][lastHash].account,
                                prev |-> lastHash, src |-> src, amt |-> ledger[n][src].amt, sig |-> sk])
       IN /\ ledger' = [ledger EXCEPT ![n][h2] =
                          [kind |-> "receive", account |-> ledger[n][lastHash].account,
                           prev |-> lastHash, src |-> src, amt |-> ledger[n][src].amt, sig |-> sk]]
          /\ lastHash' = h2
          /\ received' = [m \in Node |-> received[m] \cup
                            {[kind |-> "receive", account |-> ledger[n][lastHash].account,
                              prev |-> lastHash, src |-> src, amt |-> ledger[n][src].amt, sig |-> sk]}]

CreateChangeBlock(n, sk) ==
    /\ lastHash \in Hash
    /\ ledger[n][lastHash] # NoBlockVal
    /\ LET h2 == CalculateHash([kind |-> "change", account |-> ledger[n][lastHash].account,
                                prev |-> lastHash, src |-> NoHash, amt |-> 0, sig |-> sk])
       IN /\ ledger' = [ledger EXCEPT ![n][h2] =
                          [kind |-> "change", account |-> ledger[n][lastHash].account,
                           prev |-> lastHash, src |-> NoHash, amt |-> 0, sig |-> sk]]
          /\ lastHash' = h2
          /\ received' = [m \in Node |-> received[m] \cup
                            {[kind |-> "change", account |-> ledger[n][lastHash].account,
                              prev |-> lastHash, src |-> NoHash, amt |-> 0, sig |-> sk]}]

ProcessReceived(n, b) ==
    /\ b \in received[n]
    /\ ValidSignature(b)
    /\ \A h \in Hash : ledger[n][h] = NoBlockVal
    /\ \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].prev # b.prev
    /\ \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].src # b.src
    /\ LET h2 == CalculateHash([kind |-> b.kind, account |-> b.account,
                                prev |-> b.prev, src |-> b.src, amt |-> b.amt, sig |-> b.sig])
       IN /\ ledger' = [ledger EXCEPT ![n][h2] = b]
          /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
    /\ UNCHANGED lastHash

Next ==
    \/ CreateGenesisBlock
    \/ \E n \in Node, sk \in PrivateKey, toPk \in PublicKey, amt \in 1..GenesisBalance :
         CreateSendBlock(n, sk, toPk, amt)
    \/ \E n \in Node, sk \in PrivateKey, src \in Hash : CreateOpenBlock(n, sk, src)
    \/ \E n \in Node, sk \in PrivateKey, src \in Hash : CreateReceiveBlock(n, sk, src)
    \/ \E n \in Node, sk \in PrivateKey : CreateChangeBlock(n, sk)
    \/ \E n \in Node, b \in [kind: {"send", "receive", "open", "change", "genesis"},
                              account: PublicKey, prev: Hash \cup {NoHash},
                              src: Hash \cup {NoHash}, amt: 0..GenesisBalance, sig: PrivateKey] :
         ProcessReceived(n, b)

Spec == Init /\ [][Next]_vars

SafetyInvariant == \A n \in Node, h \in Hash :
    (ledger[n][h] # NoBlockVal) => ValidSignature(ledger[n][h])

=======================================================================