---- MODULE MC ----

\* @type: Set(SERVER);
Server == {
    "sv1_OF_SERVER",
    "sv2_OF_SERVER",
    "sv3_OF_SERVER",
    "sv4_OF_SERVER",
    "sv5_OF_SERVER"
    }

\* @type: STATE;
Follower == "Follower_OF_STATE"
\* @type: STATE;
Candidate == "Candidate_OF_STATE"
\* @type: STATE;
Leader == "Leader_OF_STATE"

VARIABLES
    \* @type: MESSAGE -> Int;
    messages,

    \* @type: SERVER -> STATE;
    state

INSTANCE Raft
====
