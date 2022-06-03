---- MODULE Compare_and_swap ----

(**************************************)
(* State |  Mutual Exclusion Code     *)
(* init  | int lock_ = 0; // mutual   *)
(********|*****************************)
(* 0, 1  | lock(&lock_);              *)
(* 2     | start_critical();          *)
(* 3     | action_in_critical();      *)
(* 4     | end_critical();            *)
(* 5     | unlock(&lock_);            *)
(**************************************)

(************************************************************)
(*               Compare-And-Swap Code                      *)
(************************************************************)
(*  int CompareAndSwap(int *ptr, int expected, int new) {   *)
(*     int actual = *ptr;                                   *)
(*     if (actual == expected)                              *)
(*         *ptr = new;                                      *)
(*     return actual;                                       *)
(*  }                                                       *)
(************************************************************)
(*               Lock Code                                  *)
(************************************************************)
(*  void lock(int* lock_) {                                 *)
(*      while (CompareAndSwap(&lock_, 0, 1) == 1)           *)
(*          ; // активное ожидание                          *)
(*  }                                                       *)
(************************************************************)
(*               Unlock Code                                *)
(************************************************************)
(*  void unlock(int* lock_) {                               *)
(*      *lock_ = 0;                                         *)
(*  }                                                       *)
(************************************************************)

EXTENDS Integers

CONSTANTS 
  PROCESSES,
  STATES,
  FINAL_STATE,
  LOCK_STATES,
  UNLOCK_STATES

VARIABLES
  lock,
  in_critical, 
  current_state,
  compare_and_swap_result

vars == <<lock, in_critical, current_state, compare_and_swap_result>>

TypeOK ==
  /\ lock \in 0..1
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]
  /\ compare_and_swap_result \in [PROCESSES -> 0..1]

Init ==
  /\ lock = 0
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ compare_and_swap_result = [p \in PROCESSES |-> 0]

Exclusion == 
  ~ \E p1, p2 \in PROCESSES:
    /\ p1 /= p2
    /\ in_critical[p1]
    /\ in_critical[p2] 

End_program == 
  /\ current_state[0] = FINAL_STATE
  /\ current_state[1] = FINAL_STATE
  /\ UNCHANGED vars


Increment_state(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<lock, in_critical, compare_and_swap_result>> 

Set_state(p, state) == 
  /\ current_state' = [current_state EXCEPT ![p] = state]
  /\ UNCHANGED <<lock, in_critical, compare_and_swap_result>>

Set_critical_increment_state(p, critical_value) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ in_critical' = [in_critical EXCEPT ![p] = critical_value]
  /\ UNCHANGED <<lock, compare_and_swap_result>>

Compare_and_swap_increment_state(p, expected, new) == 
  /\ (\/ (lock /= expected /\ lock' = lock)
    \/ (lock = expected /\ lock' = new))
  /\ compare_and_swap_result' = [compare_and_swap_result EXCEPT ![p] = lock]
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<in_critical>>

Enter_critical(p) ==
  /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
  /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<lock, compare_and_swap_result>>

Do_critical(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
  /\ UNCHANGED <<lock, in_critical, compare_and_swap_result>>

Exit_critical(p) == 
  /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<lock, compare_and_swap_result>>

Lock(p) == 
  \/ (current_state[p] = 0 /\ Compare_and_swap_increment_state(p, 0, 1))
  \/ (current_state[p] = 1 /\ (
    \/ (compare_and_swap_result[p] = 1  /\ Set_state(p, 0))
    \/ (compare_and_swap_result[p] /= 1 /\ Increment_state(p))))

Unlock(p) == 
  /\ lock' = 0
  /\ current_state' = [current_state EXCEPT ![p] = FINAL_STATE]
  /\ UNCHANGED <<in_critical, compare_and_swap_result>>

Run_process(p) == 
  \/ (current_state[p] \in LOCK_STATES /\ Lock(p))
  \/ (current_state[p] = 2 /\ Enter_critical(p))
  \/ (current_state[p] = 3 /\ Do_critical(p)) 
  \/ (current_state[p] = 4 /\ Exit_critical(p))
  \/ (current_state[p] \in UNLOCK_STATES /\ Unlock(p))


Next == 
  \/ \E p \in PROCESSES: Run_process(p)
  \/ End_program

Fairness ==
  \A p \in PROCESSES: WF_vars(Run_process(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Ends == 
  <>[] \A s \in PROCESSES: current_state[s] = FINAL_STATE

--------------------------------------

PROCESSES_const == 0..5
LOCK_STATES_const == 0..1
UNLOCK_STATES_const == {5}
STATES_const == 0..FINAL_STATE

====