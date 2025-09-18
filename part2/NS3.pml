active proctype Intruder() {
  mtype msg, recpt;
  Crypt data, intercepted;
  do
    :: network ? (msg, _, data) ->
       if /* perhaps store the message */
	 :: intercepted.key   = data.key;
	    intercepted.content1 = data.content1;
	    intercepted.content2 = data.content2;
	 :: skip;
       fi ;

    :: /* Replay or send a message */
       if /* choose message type */
	 :: msg = msg1;
	 :: msg = msg2;
	 :: msg = msg3;
       fi ;
       if /* choose a recepient */
	 :: recpt = agentA;
	 :: recpt = agentB;
       fi ;
       if /* replay intercepted message or assemble it */
	 :: data.key    = intercepted.key;
	    data.content1  = intercepted.content1;
	    data.content2  = intercepted.content2;
	 :: if /* assemble content1 */
	      :: data.content1 = agentA;
	      :: data.content1 = agentB;
	      :: data.content1 = agentI;
	      :: data.content1 = nonceI;
	    fi ;
	    if /* assemble key */
	      :: data.key = keyA;
	      :: data.key = keyB;
	      :: data.key = keyI;
	    fi ;
	    data.content2 = nonceI;
       fi ;
      network ! msg (recpt, data);
  od
}