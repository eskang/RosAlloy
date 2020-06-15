/**
	A simple model of ROS for security analysis
**/

open util/ordering[Time] as TO


/**
	Basics: Process & Events
**/
sig Time {}

abstract sig Process {
	events : set Event 
}
abstract sig Event {
	at : Time	// time at which this event takes place
}
fact {
	// At every time step, there's exactly one event that takes place
	all t : Time - last | one e : Event | e.at = t
}

/**
	Architectural layer: Components
**/
abstract sig Data {}
abstract sig Component extends Process {}
abstract sig CallEvent extends Event {
	caller, callee : Component
}{
	this in caller.events
	this in callee.events
}

/** 
	Instantiation: Turtlebot 3 (from Miguel's report)
**/

abstract sig RosMsg {} 	// topic messages

// Data Distribution Service (DDS) middleware 
// Provides publish-subscribe pattern of commmunication
one sig DDS extends Component {
	// A set of subscribers 
	subs : Topic -> RosNode -> Time	// subscribes
}{
	// add a subscriber
	all e : Subscribe | let t = e.at, t' = t.next {
		subs.t' = subs.t + e.topic -> e.caller
	}

	all e : Callback | let t = e.at {
		// Every callback event is in response to some
		// previous Publish event
		some e_prev : evtsBefore[e] & Publish {
			e.topic = e_prev.topic
			e.m = e_prev.msg
			// the creator of the callback must be
			// one of the subscribers to the topic
			e.callee in subs.t[e.topic]
		}		
	}

	// frame conditions
	all t : Time - last | let t' = t.next {
		// subs can only change when some Subscribe event occurs
		subs.t' != subs.t implies some e : callee.this & Subscribe | e.at = t
	}

}

// Events related to the pub-sub communication in ROS
abstract sig DDSEvent extends CallEvent {
	topic : Topic
}
sig Publish extends DDSEvent {
	msg : RosMsg
}{
	callee = DDS
	caller in RosNode
}
sig Subscribe extends DDSEvent {}{
	callee = DDS
	caller in RosNode
}
sig Callback extends DDSEvent {
	m : RosMsg
}{
	caller = DDS
	callee in RosNode
}

// ROS-specific data
sig LaserData extends Data {}
sig Velocity extends Data {}

// Topic messages
sig ScanMsg extends RosMsg {
	laserData : LaserData
}
sig VelMsg extends RosMsg {
	velocity : Velocity
}

// ROS nodes
abstract sig RosNode extends Component {}

// ROS node for sensing Lidar data
// publishes to Scan topic
one sig LidarNode extends RosNode {
	// set of laser data that this node may publish
	data : set LaserData
}{
	this.publishesTo[Scan]
	this.subscribesTo[none]

	all e : this.invokes[Publish] {
		e.topic = Scan implies {
			e.msg in ScanMsg
			// only publish what's in this.data
			e.msg.laserData in data
		}
	}

}

// ROS node that interfaces with the wheel controller
// subscribes to CmdVel topic
one sig WheelNode extends RosNode {
	// history of wheel commands generated
	// for now, we just keep track of all commands ever generated
	// without their ordering
	cmdsGenerated : Velocity -> Time
}{

	this.publishesTo[none]
	this.subscribesTo[CmdVel]

	all e : this.receives[Callback] | let t = e.at, t' = t.next {
		e.topic = CmdVel implies 
			cmdsGenerated.t' = cmdsGenerated.t + e.m.velocity
	}

	// frame conditions
	all t : Time - last | let t' = t.next {
		// cmdsGenerate can only change during callback to CmdVel topic
		cmdsGenerated.t' != cmdsGenerated.t implies
			some e : callee.this & Callback | t = e.at and e.topic = CmdVel
	}
}

// ROS node that the human operator interacts with
// subscribes to Scan and publishes to CmdVel
one sig JoystickNode extends RosNode {
	// captures the behavior of a "trusted" operator
	// in terms of what velocity command it generates given some laser data
	// for now, assume it's fixed
	operatorBehavior : LaserData lone -> lone Velocity
}{	
	this.publishesTo[CmdVel]
	this.subscribesTo[Scan]

	all e : this.invokes[Publish] {
		e.topic = CmdVel
		e.msg in VelMsg
		// there must be some previous Callback event for Scan
		some e_prev : evtsBefore[e] & callee.this & Callback {
			e_prev.topic = Scan
			// the velocity being published is what the operator would produce
			// given the laser data received the Scan topic
			 e.msg.velocity in operatorBehavior[e_prev.m.laserData]
		}
	}
}

// Attacker node, can subscribe & pubilsh to anything
lone sig Attacker extends RosNode {}


// Topics
abstract sig Topic {}
// "cmd_vel" topic in TurtleBot, for modifying the velocity of the robot
one sig CmdVel extends Topic {}
// "scan topic", used to get laser sensor data
one sig Scan extends Topic {}

// Initial configurations
fact InitState {
	DDS.subs.first = CmdVel -> WheelNode + Scan -> JoystickNode
	no WheelNode.cmdsGenerated.first
}

// Some helper functions

// Set of events that happened before e
fun evtsBefore[e : Event] : set Event {
	{ _e : Event | _e.at in e.at.prevs } 
}

fun receives[c : Component, eventType : Event] : set Event {
	callee.c & eventType
}

fun invokes[c : Component, eventType : Event] : set Event {
	caller.c & eventType
}

pred publishesTo[n : RosNode, topics : Topic] {
	n.invokes[Publish].topic in topics
}

pred subscribesTo[n : RosNode, topics : Topic] {
	n.invokes[Subscribe].topic in topics
}

/**
	Properties
**/

pred unknownWheelCommand {
	some t : Time, v : Velocity |
		// WheelNode generates some velocity command
		// that has not been initiated by the trusted human operator
		v in WheelNode.cmdsGenerated.t and
		v not in JoystickNode.operatorBehavior[LaserData]
}

// When there's no attacker (i.e., all nodes are behaving correctly),
// the wheel integrity property should hold
// this shouldn't generate an instance
check WheelCommandIntegrity {
	no Attacker implies 
		not unknownWheelCommand	
} for 3 but 5 Time, 4 Event

// When there's an attacker, the property will be violated
// this should generate an instance
check WheelCommandIntegrityUnderAttacker {
	not unknownWheelCommand	
} for 3 but 5 Time, 4 Event

// A sanity check to make sure there's no overconstraint in the model
// this should generate an instance
run test {
	some t : Time, v : Velocity |
		// WheelNode generates some velocity command
		// that was initiated by the trusted human operator
		v in WheelNode.cmdsGenerated.t and
		v in JoystickNode.operatorBehavior[LaserData]
} for 3 but 5 Time, 4 Event

