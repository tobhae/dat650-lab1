mtype = {ok, err, msg1, msg2, msg3, keyA, keyB, agentA, agentB,
	 nonceA, nonceB, agentI, keyI, nonceI };

typedef Crypt { mtype key, content1, content2 };

chan network = [0] of {mtype, /* msg# */
		       mtype, /* receiver */
		       Crypt
};

/* LTL properties */
ltl task2 { <> (statusA == ok && statusB == ok) }

/* If both run to completion then they must have each other as partner */
ltl propAB { [] ((statusA == ok && statusB == ok) -> (partnerA == agentB && partnerB == agentA)) }

/* If A finishes and believes it talked to B, then Intruder must not know A's nonce */
ltl propA { [] ((statusA == ok && partnerA == agentB) -> (! knows_nonceA)) }

/* If B finishes and believes it talked to A, then Intruder must not know B's nonce */
ltl propB { [] ((statusB == ok && partnerB == agentA) -> (! knows_nonceB)) }

/* global variables for verification*/
mtype partnerA, partnerB;
mtype statusA = err;
mtype statusB = err;

/* Intruder ghost variables */
bool knows_nonceA = false;
bool knows_nonceB = false;

active proctype Alice() {
  /* local variables */

  mtype pkey;      /* the other agent's public key                 */
  mtype pnonce;    /* nonce that we receive from the other agent   */
  Crypt messageAB; /* our encrypted message to the other party     */
  Crypt data;      /* received encrypted message                   */


  /* Initialization  */

  partnerA = agentB;
  pkey     = keyB;

  /* Prepare the first message */

  messageAB.key = pkey;
  messageAB.content1 = agentA;
  messageAB.content2 = nonceA;

  /* Send the first message to the other party */

  network ! msg1 (partnerA, messageAB);

  /* Wait for an answer. Observe that we are pattern-matching on the
     messages that start with msg2 and agentA, that is, we block until 
     we see a message with values msg2 and agentA as the first and second  
     components. The third component is copied to the variable data. */

  network ? (msg2, agentA, data);

  /* We proceed only if the key field of the data matches keyA and the
     received nonce is the one that we have sent earlier; block
     otherwise.  */

  (data.key == keyA) && (data.content1 == nonceA);

  /* Obtain Bob's nonce */

  pnonce = data.content2;

  /* Prepare the last message */
  messageAB.key = pkey;
  messageAB.content1 = pnonce;
  messageAB.content2 = 0;  /* content2 is not used in the last message,
                              just set it to 0 */


  /* Send the prepared messaage */
  network ! msg3 (partnerA, messageAB);


  /* and last - update the auxilary status variable */
  statusA = ok;
}

active proctype Bob() {

  mtype pkey;      /* the other agent's public key                 */
  mtype pnonce;    /* nonce that we receive from the other agent   */
  Crypt messageBA; /* our encrypted message to the other party     */
  Crypt data;      /* received encrypted message                   */

  /* Initialization */
  partnerB = agentA;
  pkey = keyA;

  /* Wait for the first message from Alice */
  network ? (msg1, agentB, data);

  /* Verify the message, must be encrypted with Bob's public key */
  (data.key == keyB);

  /* Obtain Alice's nonce */
  pnonce = data.content2;

  /* Prepare message 2*/
  messageBA.key = pkey;
  messageBA.content1 = pnonce;
  messageBA.content2 = nonceB;

  /* Send message to Alice */
  network ! msg2 (partnerB, messageBA);

  /* Wait for message 3 */
  network ? (msg3, agentB, data);

  /* Verify correctness, must be encrypted with Bob's key and contains his nonce */
  (data.key == keyB) && (data.content1 == nonceB);

  /* and last - update the auxilary status variable */
  statusB = ok;
}

active proctype Intruder() {
  mtype msg, recpt;
  Crypt data, intercepted;

  do
  :: network ? (msg, _, data) ->
       if
       :: intercepted.key      = data.key;
          intercepted.content1 = data.content1;
          intercepted.content2 = data.content2;

          /* If the message is encrypted with the intruder's key, 
             decrypt it and learn any nonces it contains. */
          if
          :: (data.key == keyI) ->
               /* msg1 format: { agent, nonce } -> content2 is the nonce */
               if
               :: (data.content2 == nonceA) -> knows_nonceA = true;
               :: (data.content2 == nonceB) -> knows_nonceB = true;
               :: else -> skip;
               fi;

               /* msg2 format: { nonce1, nonce2 } -> both fields could be nonces */
               if
               :: (data.content1 == nonceA) -> knows_nonceA = true;
               :: (data.content1 == nonceB) -> knows_nonceB = true;
               :: else -> skip;
               fi;

               if
               :: (data.content2 == nonceA) -> knows_nonceA = true;
               :: (data.content2 == nonceB) -> knows_nonceB = true;
               :: else -> skip;
               fi
          :: else -> skip  /* Not encrypted to intruder, cannot decrypt */
          fi
       :: skip  /* Choose not to store this message */
       fi;

  ::  /* Replay or send a message */
     /* choose message type */
     if
     :: msg = msg1;
     :: msg = msg2;
     :: msg = msg3;
     fi;

     /* choose recipient */
     if
     :: recpt = agentA;
     :: recpt = agentB;
     fi;

     /* Choose to replay previously intercepted message or assemble a new one */
     if
     :: /* replay stored intercepted message (unmodified) */
        data.key      = intercepted.key;
        data.content1 = intercepted.content1;
        data.content2 = intercepted.content2;
     :: /* assemble content1 */
        if
        :: data.content1 = agentA;
        :: data.content1 = agentB;
        :: data.content1 = agentI;

        /* Intruder can also put nonceA/nonceB here only if it knows it */
        :: (knows_nonceA) -> data.content1 = nonceA;
        :: (knows_nonceB) -> data.content1 = nonceB;
        fi;

        
        if /* assemble key */
        :: data.key = keyA;
        :: data.key = keyB;
        :: data.key = keyI;
        fi;

        if
        :: (msg == msg3) -> data.content2 = 0; /* msg3 carries only content1 */
        :: /* msg1 or msg2: allow nonce usage only if known */
           if
           :: (knows_nonceA) -> data.content2 = nonceA;
           :: (knows_nonceB) -> data.content2 = nonceB;
           :: else -> data.content2 = nonceI;  /* Use Intruder's own nonce if nothing known */
           fi
        fi
     fi;

     network ! msg (recpt, data)
  od;
}