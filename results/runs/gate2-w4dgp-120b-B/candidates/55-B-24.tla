---- MODULE MCEcho ----
EXTENDS Echo

\* A tiny graph with three nodes.
N1 == {"a", "b", "c"}

\* We don't care which node gets
\* picked as the initiator.
I1 == CHOOSE n \in N1 : TRUE

\* The tiny graph is fully meshed: 
\*      <<"a", "a">> :> FALSE @@
\*      <<"a", "b">> :> TRUE  @@
\*      <<"b", "a">> :> TRUE  @@
\*      <<"b", "b">> :> FALSE @@
\*      <<"a", "c">> :> TRUE @@
\*      <<"c", "a">> :> TRUE @@
\*      <<"b", "c">> :> TRUE  @@
\*      <<"c", "b">> :> TRUE  @@
\*      <<"c", "c">> :> FALSE
\* More concisely defined as:
R1 == [ edge \in (N1 \X N1) |-> IF edge[1] = edge[2] 
                                THEN FALSE
                                ELSE TRUE ]

\* To get a graph that satisfies the
\* assumptions in Echo, we simply 
\* define R to be, via CHOOSE, one that
\* meets Echo's contract. This is the
\* source of the nondeterminism.
R2 == CHOOSE r \in [ N1 \X N1 -> BOOLEAN ] : 
        /\ IsConnected(r, N1)
        /\ IsSymmetric(r, N1)
        /\ IsIrreflexive(r, N1)

\* Print R to stdout at startup.
TestSpec == PrintT(R) \/ Spec        

Init == /\ R = R2
        /\ s = I1
        /\ mark = [ n \in N1 |-> 1 ]

\* Flood fill: a node marks itself, and
\* every node linked from it, and so on.
Flood(n) == /\ mark[n] = 1
             /\ s' = n
             /\ mark' = [ x \in N1 |-> IF x = n \/ R[n, x] = TRUE 
                                      THEN 1 
                                      ELSE mark[x] ]
             /\ UNCHANGED R

Next == \E n \in N1 : Flood(n)

====