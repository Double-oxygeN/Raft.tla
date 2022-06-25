---- MODULE Raft ----
\* Formal specification for the Raft consensus algorithm.
\*
\* Original document is by Diego Ongaro, 2014 (CC BY-4.0).
\* Source: https://github.com/ongardie/raft.tla
\* Please check https://creativecommons.org/licenses/by/4.0 for more information.
\* This document includes some adaptions by Yuya Shiratori.
\*
\* Changes:
\*   - Change the format
\*   - Annotate types for Apalache
\*   - Change the type of the variable `votedFor` from `Server \cup { Nil }` to `Seq(SERVER)`
\*   - Use `clientRequest` instead of `v \in Value` (thanks to @jinlmsft)
\*

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    \* The set of server IDs
    \* @type: Set(SERVER);
    Server

CONSTANTS
    \* Server states.
    \* @type: STATE;
    Follower,
    \* @type: STATE;
    Candidate,
    \* @type: STATE;
    Leader

CONSTANTS
    \* Message types:
    \* @type: MESSAGE_TYPE;
    RequestVoteRequest,
    \* @type: MESSAGE_TYPE;
    RequestVoteResponse,
    \* @type: MESSAGE_TYPE;
    AppendEntriesRequest,
    \* @type: MESSAGE_TYPE;
    AppendEntriesResponse

----
\* Global variables

\* The type representing both requests and responses sent from a server.
\* @typeAlias: MESSAGE = [mtype: MESSAGE_TYPE, mterm: Int, mlastLogIndex: Int,
\*     mlastLogTerm: Int, msource: SERVER, mdest: SERVER];
MSGTypeAliases == TRUE

\* The type representing a log item.
\* @typeAlias: LOG_ITEM = [term: Int];
LITypeAliases == TRUE

VARIABLES
    \* A bag of records representing requests and responses sent from one server
    \* to another.
    \* @type: MESSAGE -> Int;
    messages

----
\* The following variables are all per server.

VARIABLES
    \* The server's term.
    \* @type: SERVER -> Int;
    currentTerm,

    \* The server's state (Follower, Candidate, or Leader).
    \* @type: SERVER -> STATE;
    state,

    \* The candidate the server voted for in its current term.
    \* If it hasn't voted for any, the value is empty.
    \* @type: SERVER -> Seq(SERVER);
    votedFor

serverVars == <<currentTerm, state, votedFor>>

VARIABLES
    \* A sequence of log entries. The index into this sequence is the index of the
    \* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
    \* with index 1, so be careful not to use that!
    \* @type: SERVER -> Seq(LOG_ITEM);
    log

\* @type: <<SERVER -> Seq(LOG_ITEM)>>;
logVars == <<log>>

\* The following variables are used only on candidates:
VARIABLES
    \* The set of servers from which the candidate has received a RequestVote
    \* response in its currentTerm.
    \* @type: SERVER -> Set(SERVER);
    votesResponded,

    \* The set of servers from which the candidate has received a vote in its
    \* currentTerm.
    \* @type: SERVER -> Set(SERVER);
    votesGranted,

    \* A history variable used in the proof. This would not be present in an
    \* implementation.
    \* @type: SERVER -> SERVER -> Seq(LOG_ITEM);
    voterLog

candidateVars == <<votesResponded, votesGranted, voterLog>>

----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, logVars>>

----
\* Helpers

\* The term of the last entry in a log, or 0 if the log is empty.
\* @type: (Seq(LOG_ITEM)) => Int;
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (MESSAGE, MESSAGE -> Int) => MESSAGE -> Int;
AppendMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2]
    ELSE
        msgs @@ (m :> 1)

\* Add a message to the bag of messages.
\* @type: (MESSAGE) => Bool;
Send(m) == messages' = AppendMessage(m, messages)

----
\* Define initial values for all variables

\* @type: Bool;
InitHistoryVars == voterLog = [i \in Server |-> [j \in {} |-> <<>>]]

\* @type: Bool;
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state = [i \in Server |-> Follower]
                  /\ votedFor = [i \in Server |-> <<>>]

\* @type: Bool;
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]

\* @type: Bool;
InitLogVars == log = [i \in Server |-> <<>>]

\* @type: Bool;
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = <<>>]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, logVars>>

\* @type: (SERVER, SERVER) => Bool;
SendRequestVoteRequest(src, dest) ==
    Send([mtype |-> RequestVoteRequest,
          mterm |-> currentTerm[src],
          mlastLogIndex |-> Len(log[src]),
          mlastLogTerm |-> LastTerm(log[src]),
          msource |-> src,
          mdest |-> dest])

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ SendRequestVoteRequest(i, j)
    /\ UNCHANGED <<serverVars, candidateVars, logVars>>

----
\* Defines how the variables may transition.
\* @type: Bool;
Next == \/ \E i \in Server : Timeout(i)
        \/ \E i,j \in Server : RequestVote(i, j)

\* The specification must start with the initial state and transition according
\* to Next.
\* @type: Bool;
Spec == Init /\ [][Next]_vars

====
