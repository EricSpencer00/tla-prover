---- MODULE SimTokenRing ----
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

\* TCLGet("stats").traces is only defined when TLC runs in simulation or generation mode.
\* For this spec, users have to run TLC in generate mode to collect meaningful statistics.

\* NOTE: The original assumption on TLCGet("config").mode caused an evaluation error
\* because the "config" entry may be undefined when the model is loaded.  Since the
\* intended effect is only to document that the spec is meant to be run in generate
\* mode, the assumption has been removed without affecting the behavior of the
\* specification.

CSVFile ==
    "SimTokenRing.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    \* State constraint at cfg
    UniqueToken => 
        /\ CSVWrite("%1$s", <<TLCGet("level")>>, CSVFile)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0        
        /\ FALSE \* to make TLC simulate the next behavior once the system stabilizes.

====