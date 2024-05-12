module CANBus

open util/ordering[Time_Slot] as ord

sig Node {}

sig State {
	from: Node,
	to: set Node
}

abstract sig Message {
	state: State,
	sentOn: Time_Slot,
	readOn: Node -> lone Time_Slot
}{
	readOn.Time_Slot in state.to
}

sig Message_Data, Message_Remote, Message_Error, Message_Overload extends Message {}

sig Time_Slot {
	inChannel: Node -> Message,

	read: Node -> Message,

	sent: Node -> Message,

	available: set Message,

	needsToSend: Node -> Message
}

fun Messages_Sent_On_Time_Slot[t: Time_Slot]: set Message { t.sent[Node] }
fun Messages_Read_On_Time_Slot[t: Time_Slot]: set Message { t.read[Node] }

fact RulesOfCANBus {

	Message in Time_Slot.sent[Node]

	no ord/first.inChannel[Node]

	all pre: Time_Slot - ord/last | let post = ord/next[pre] | {
        post.available = pre.available - Messages_Sent_On_Time_Slot[pre]
     }

	all t: Time_Slot | {

		Messages_Sent_On_Time_Slot[t] in t.available

		Messages_Sent_On_Time_Slot[t].sentOn in t
		Messages_Read_On_Time_Slot[t].readOn[Node] in t

		Messages_Sent_On_Time_Slot[t] = t.sent[Node]

		all n: Node, m: Message | m.readOn[n] = t => m in t.read[n]
		all n: Node | t.sent[n].state.from in n

		all n: Node, m: Message | {
			(m in t.inChannel[n] => (n in m.state.to && m.sentOn in ord/prevs[t]))
			(m in t.read[n] => m !in ord/nexts[t].inChannel[n])
		}
	}
}

fact Frame_Configuration {
	all pre: Time_Slot - ord/last | let post = ord/next[pre] | {
		#pre.read.Message_Overload > 0 => #post.sent.Message = 0
		all n:Node | pre.read[n] in Message_Remote && post.sent[n] in Message_Data
		all n:Node | pre.read[n] in Message_Error &&
							post.sent[n] in Message_Data &&
							post.sent[n].state.to = pre.read[n].state.to
     }
}

fun Messages_Live_On_Time_Slot[t: Time_Slot]: set Message {
	Message - { future: Message | future.sentOn in ord/nexts[t] }
           - { past: Message | all n: past.state.to | past.readOn[n] in ord/prevs[t] }
}

pred Read_In_Order  {

	all n1, n2: Node | all m1, m2: Message | {
		m1.state.from = n1
		m2.state.from = n1
		m1.state.to = n2
		m2.state.to = n2
	} => {
		(some m1.readOn[n2] && some m2.readOn[n2] &&
			m1.readOn[n2] in ord/prevs[m2.readOn[n2]]) =>
			ord/lte[m1.sentOn, m2.sentOn]
		}
}

pred No_Message_Shortage {
	all t: Time_Slot - ord/last | (sum n: Node | # t.needsToSend[n]) =< # t.available
}

pred Num_Of_State  {
   #Node > 1
}

pred Out_Of_Order  {
   ! Read_In_Order
   #Message = 3
}

run Num_Of_State for 3
run Out_Of_Order for 4

fun FROM: Message -> Node {{m: Message, n: Node | n in m.state.from}}
fun TO: Message -> Node {{m: Message, n: Node | n in m.state.to}}
