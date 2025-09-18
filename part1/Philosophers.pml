#define N 4

/* Forks: 0 = available, 1 = taken */
byte fork[N];

/* LTL, no fork should ever exceed 1 */
ltl mutual_exclusion { [] (fork[0] <= 1 && fork [1] <= 1 && fork [2] <= 1 && fork[3] <= 1) }

/* Liveness property: A philosopher eventually eats */
ltl some_eating { []<> (phil0_eating || phil1_eating || phil2_eating || phil3_eating) }

/* Track when philosophers are eating */
bool phil0_eating = false;
bool phil1_eating = false;
bool phil2_eating = false;
bool phil3_eating = false;

proctype phil(int id) {
  int left = id;
  int right = (id+1) % N;

  do
  :: printf("Philosopher %d is thinking\n", id);

    if
    :: (id % 2 == 0) ->   /* Even phils pick up left fork*/

      atomic {
        if
        :: (fork[left] == 0 && fork[right] == 0) -> 
            fork[left] = 1; 
            fork[right] = 1;
            
            /* Value should not be > 1 */
            assert(fork[left] <= 1);
            assert(fork[right] <= 1);
            printf("Philosopher %d picked up forks %d and %d\n", id, left, right);

        :: else -> skip
        fi
      }

    
    :: else ->    /* Odd phils pick up right fork */
      
      atomic {
        if 
        :: (fork[right] == 0 && fork[left] == 0) -> 
            fork[right] = 1; 
            fork[left] = 1;

            /* Value should not be > 1 */
            assert(fork[right] <= 1);
            assert(fork[left] <= 1);
            printf("Philosopher %d picked up forks %d and %d\n", id, right, left);

        :: else -> skip
        fi
      }
    fi;

    atomic {
      if 
      :: (fork[left] == 1 && fork[right] == 1)  ->

        /* Has both forks */
        if
        :: (id == 0) -> phil0_eating = true
        :: (id == 1) -> phil1_eating = true
        :: (id == 2) -> phil2_eating = true
        :: (id == 3) -> phil3_eating = true
        fi;
        
        printf("Philosopher %d is eating with forks %d and %d\n", id, left, right);

        /* Put down both forks after eating */
        fork[left] = 0;
        fork[right] = 0;
        printf("Philosopher %d put down fork %d\n", id, left);
        printf("Philosopher %d put down fork %d\n", id, right);

        /* Reset flags */
        if
        :: (id == 0) -> phil0_eating = false
        :: (id == 1) -> phil1_eating = false
        :: (id == 2) -> phil2_eating = false
        :: (id == 3) -> phil3_eating = false
        fi;

      fi
    }
      
    progress: skip;
  od
}

init {
  int i = 0;
  /* Set forks as available */
  atomic {
    i = 0;
    do
    :: i < N -> fork[i] = 0; i++
    :: else -> break
    od
  }

  /* Init philosophers */
  i = 0;
  do
  :: i >= N -> break
  :: else -> run phil(i); i++
  od
}
