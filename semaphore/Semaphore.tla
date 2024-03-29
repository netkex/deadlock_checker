---- MODULE Semaphore ----

(*******************************************)
(* State |  Mutual Exclusion Code          *)
(* init  | int semaphore = 1; // mutual    *)
(********|**********************************)
(* 0     | wait(&semaphore)                *)
(* 1     | start_critical();               *)
(* 2     | action_in_critical();           *)
(* 3     | end_critical();                 *)
(* 4     | signal(&semaphore)              *)
(*******************************************)

(*******************************************)
(*                Wait Code                *)
(*******************************************)
(*  void wait(int* s) {                    *)
(*     s--;                                *)
(*     if (s < 0) {                        *)
(*         P блокируется                   *)
(*         P -> queue                      *)
(*     }                                   *)
(*  }                                      *)
(*******************************************)
(*                Signal Code              *)
(*******************************************)
(*  void signal(int* s) {                  *)
(*      s++;                               *)
(*      if (s <= 0) {                      *)
(*          P <- queue                     *)
(*          P освобождается                *)
(*      }                                  *)
(*  }                                      *)
(*******************************************)

EXTENDS Integers

CONSTANTS 
  PROCESSES,
  STATES,
  FINAL_STATE

VARIABLES
  semaphore,
  in_critical, 
  current_state,
  blocked

vars == <<semaphore, in_critical, current_state, blocked>>

TypeOK ==
  /\ semaphore \in Int
  /\ in_critical \in [PROCESSES -> BOOLEAN]
  /\ current_state \in [PROCESSES -> STATES]
  /\ blocked \in [PROCESSES -> BOOLEAN]

Semaphore_is_good ==
  /\ semaphore <= 1

Init ==
  /\ semaphore = 1
  /\ in_critical = [p \in PROCESSES |-> FALSE]
  /\ current_state = [p \in PROCESSES |-> 0]
  /\ blocked = [p \in PROCESSES |-> FALSE]

Exclusion == 
  ~ \E p1, p2 \in PROCESSES:
    /\ p1 /= p2
    /\ in_critical[p1]
    /\ in_critical[p2] 

End_program == 
  /\ current_state[0] = FINAL_STATE
  /\ current_state[1] = FINAL_STATE
  /\ UNCHANGED vars


Wait(p) == 
  \/ (
    /\ semaphore > 0
    /\ semaphore' = semaphore - 1
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<in_critical, blocked>>)
  \/ (
    /\ semaphore <= 0
    /\ semaphore' = semaphore - 1
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ blocked' = [blocked EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<in_critical>>)
      
Enter_critical(p) ==
  /\ ~blocked[p]
  /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
  /\ current_state'= [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<semaphore, blocked>>

Do_critical(p) == 
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1] 
  /\ UNCHANGED <<semaphore, in_critical, blocked>>

Exit_critical(p) == 
  /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
  /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<semaphore, blocked>>

Signal(p) == 
  \/ (
    /\ semaphore < 0
    /\ semaphore' = semaphore + 1
    /\ (\E other \in PROCESSES: blocked[other] /\ blocked' = [blocked EXCEPT ![other] = FALSE])
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<in_critical>>)
  \/ (
    /\ semaphore >= 0
    /\ semaphore' = semaphore + 1
    /\ current_state' = [current_state EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<in_critical, blocked>>)

Run_process(p) == 
  \/ (current_state[p] = 0 /\ Wait(p))
  \/ (current_state[p] = 1 /\ Enter_critical(p))
  \/ (current_state[p] = 2 /\ Do_critical(p))
  \/ (current_state[p] = 3 /\ Exit_critical(p))
  \/ (current_state[p] = 4 /\ Signal(p))


Next == 
  \/ \E p \in PROCESSES: Run_process(p)
  \/ End_program

Fairness ==
  \A p \in PROCESSES: WF_vars(Run_process(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Ends == 
  <>[] (\A s \in PROCESSES: current_state[s] = FINAL_STATE) /\ (semaphore = 1)

--------------------------------------

PROCESSES_const == 0..4
STATES_const == 0..FINAL_STATE

====