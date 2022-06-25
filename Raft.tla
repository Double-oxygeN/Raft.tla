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
\*   - Change the codomain of the variable `votedFor` from `Server \cup { Nil }` to `Set(SERVER)`
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
\*     mlastLogTerm: Int, mvoteGranted: Bool, mlog: Seq(LOG_ITEM),
\*     msource: SERVER, mdest: SERVER];
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
    \* @type: SERVER -> Set(SERVER);
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

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (MESSAGE, MESSAGE -> Int) => MESSAGE -> Int;
DropMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0]
    ELSE
        msgs

\* Messages in a bag.
\* @type: (MESSAGE -> Int) => Set(MESSAGE);
MessagesInBag(msgs) == {m \in DOMAIN msgs : msgs[m] > 0}

\* Messages whose multiplicity is one in a bag.
\* @type: (MESSAGE -> Int) => Set(MESSAGE);
SingleMessages(msgs) == {m \in DOMAIN msgs : msgs[m] = 1}

\* Add a message to the bag of messages.
\* @type: (MESSAGE) => Bool;
Send(m) == messages' = AppendMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
\* @type: (MESSAGE) => Bool;
Discard(m) == messages' = DropMessage(m, messages)

\* Combination of Send and Discard
\* @type: (MESSAGE, MESSAGE) => Bool;
Reply(response, request) ==
    messages' = DropMessage(request, AppendMessage(response, messages))

----
\* Define initial values for all variables

\* @type: Bool;
InitHistoryVars == voterLog = [i \in Server |-> [j \in {} |-> <<>>]]

\* @type: Bool;
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state = [i \in Server |-> Follower]
                  /\ votedFor = [i \in Server |-> {}]

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
              /\ votedFor' = [votedFor EXCEPT ![i] = {}]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, logVars>>

\* @type: (SERVER, SERVER) => Bool;
SendRequestVote(src, dest) ==
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
    /\ SendRequestVote(i, j)
    /\ UNCHANGED <<serverVars, candidateVars, logVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

ReplyRequestVote(src, dest, msg, grant) ==
    Reply([mtype |-> RequestVoteResponse,
           mterm |-> currentTerm[src],
           mvoteGranted |-> grant,
           mlog |-> log[src],
           msource |-> src,
           mdest |-> dest],
           msg)

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
HandleRequestVoteRequest(i, j, m) ==
    LET logOk ==
            \* The voter i agree with the vote when the
            \* candidate's log is up-to-date for the voter;
            \* see Section 5.4.1.
            \/ m.mlastLogTerm > LastTerm(log[i])
            \/ /\ m.mlastLogTerm = LastTerm(log[i])
               /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 \* The first-come-first-served basis
                 /\ votedFor[i] \in {{}, {j}}
    IN \* When m.mterm > currentTerm[i], first update the voter's term
       /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = votedFor[i] \cup {j}]
          \/ ~grant /\ UNCHANGED votedFor
       /\ ReplyRequestVote(i, j, m, grant)
       /\ UNCHANGED <<state, currentTerm, candidateVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currrentTerm[i].
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, logVars>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![i] = {}]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, logVars>>

\* Responses with stale terms are ignored.
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars>>

\* Receive a message.
\* @type: (MESSAGE) => Bool;
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)

\* End of message handlers.
----
\* Defines how the variables may transition.
\* @type: Bool;
Next == \/ \E i \in Server : Timeout(i)
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E m \in MessagesInBag(messages) : Receive(m)

\* The specification must start with the initial state and transition according
\* to Next.
\* @type: Bool;
Spec == Init /\ [][Next]_vars

====
