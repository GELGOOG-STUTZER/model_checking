----------------------------- MODULE CANBus -----------------------------
EXTENDS Integers, Sequences

(* Constants *)
CONSTANTS MaxControllers, MaxMessages

(* Variables *)
VARIABLES messages, controllers, message_queues, bus_idle, mutex

(* Initialize variables *)
Init == 
    /\ messages = {}
    /\ controllers \in SUBSET (1..MaxControllers)
    /\ message_queues = [c \in controllers |-> <<>>]
    /\ bus_idle = TRUE
    /\ mutex = FALSE

(* Transmit action *)
Transmit(controller, message) == 
    /\ bus_idle = TRUE
    /\ message \notin messages
    /\ messages' = messages \cup {message}
    /\ bus_idle' = FALSE
    /\ mutex' = TRUE

(* Receive action *)
Receive(controller) == 
    LET msg == Head(message_queues[controller])
    IN 
        /\ bus_idle = FALSE
        /\ msg \in messages
        /\ messages' = messages \ {msg}
        /\ mutex' = TRUE

(* Bus idle action *)
BusIdle == 
    /\ bus_idle = FALSE
    /\ UNCHANGED <<messages, controllers, message_queues, mutex>>

(* Next state *)
Next == 
    \E c \in controllers, msg \in (messages \cup UNION {message_queues[ctrl] : ctrl \in controllers}) :
        /\ mutex = FALSE
        /\ (Transmit(c, msg) \/ Receive(c))
    \/ IF \E ctrl \in controllers : Len(message_queues[ctrl]) > 0 THEN BusIdle ELSE TRUE

(* Temporal properties *)
TemporalProperties == 
    \A controller \in controllers : []<>(Len(message_queues[controller]) <= 1)

(* Spec *)
Spec == Init /\ [][Next]_<<messages, controllers, message_queues, bus_idle>> /\ TemporalProperties

=============================================================================