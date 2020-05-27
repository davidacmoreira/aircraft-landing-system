open util/ordering[State]
sig State {}


sig PilotInterface {
	button : Bstate -> State,
	handle_sensor : Hstate -> State,
	analogical_switch_sensor : ASstate -> State,
	gear_sensor : Gstate -> State,
	gear_shock_absorber_sensor : DSstate -> State ,
	door_sensor : Dstate -> State
}


abstract sig Gstate {}
one sig SExtended, SRetracted extends Gstate {}


abstract sig Bstate {}
one sig Up, Down extends Bstate {}


sig LandingSet {
	landingset : Lstate -> State,
	valvesDoor : one Door,
	valvesHydraulic : one Hydraulic
}

abstract sig Lstate {}
one sig Lock, Unlock extends Lstate {}


abstract sig Door {
	door : set Dstate -> State
}

abstract sig Dstate {}
one sig Open, Close extends Dstate {}
one sig SOpen, SClose extends Dstate {}


abstract sig Hydraulic {
	hydraulic : set Hstate -> State
}

abstract sig Hstate {}
one sig Extend, Retract extends Hstate {}
one sig SExtend, SRetract extends Hstate {}


sig DigitalSystem {
	anomaly : DSstate -> State,
	emergency : one AnalogicSystem
}

abstract sig DSstate {}
one sig Detect, Undetect extends DSstate {}
one sig SDetect, SUndetect extends DSstate {}


abstract sig AnalogicSystem {
	manual : ASstate -> State
}

abstract sig ASstate {}
one sig Active, Inactive extends ASstate {}
one sig SActive, SInactive extends ASstate {}



fact Init {
	PilotInterface.button.first = Up
	PilotInterface.handle_sensor.first =SExtend
	PilotInterface.analogical_switch_sensor. first = 
	PilotInterface.gear_sensor.first = 
	PilotInterface.gear_shock_absorber_sensor.first = 
	PilotInterface.door_sensor.first = 
	LandingSet.landingset.first = Lock
	Door.door.first = Close
	Hydraulic.hydraulic.first = Extend
	DigitalSystem.anomaly.first = Undetect
	AnalogicSystem.manual.first = Inactive
}

fact Trans {
	all s : State, s' : s.next {
		oneState [s']		
		moving [s, s'] or halt [s, s'] or manualsystem [s, s'] or anomalyDetector [s, s']
	}
}

pred oneState [s : State] {
	one button.s
	one landingset.s
	one door.s
	one hydraulic.s
	one anomaly.s
	one manual.s
}

pred moving [s, s' : State] {
	AnalogicSystem.manual.s = Inactive
	DigitalSystem.anomaly.s = Undetect
	LandingSet.landingset.s = Lock
	Door.door.s = Close

	PilotInterface.button.s' = PilotInterface.button.s 
	LandingSet.landingset.s' != LandingSet.landingset.s
	Door.door.s' != Door.door.s
	Hydraulic.hydraulic.s' = Hydraulic.hydraulic.s
	
	DigitalSystem.anomaly.s' = DigitalSystem.anomaly.s
	AnalogicSystem.manual.s' = AnalogicSystem.manual.s
}

pred halt [s, s' : State] {
	DigitalSystem.anomaly.s = Undetect
	LandingSet.landingset.s = Unlock
	Door.door.s = Open

	PilotInterface.button.s' != PilotInterface.button.s
	LandingSet.landingset.s' != LandingSet.landingset.s
	Door.door.s' != Door.door.s
	Hydraulic.hydraulic.s' != Hydraulic.hydraulic.s
}

pred manualsystem [s, s' : State] {
	AnalogicSystem.manual.s = Active
	DigitalSystem.anomaly.s = Detect
	LandingSet.landingset.s = Lock
	Door.door.s = Close

	PilotInterface.button.s' = PilotInterface.button.s
	LandingSet.landingset.s' != LandingSet.landingset.s
	Door.door.s' != Door.door.s
	Hydraulic.hydraulic.s' = Hydraulic.hydraulic.s 
}

pred anomalyDetector [s, s' : State] {
	DigitalSystem.anomaly.s = Detect
	AnalogicSystem.manual.s = Inactive
	
	AnalogicSystem.manual.s' != AnalogicSystem.manual.s
}



run {} for 3 but 3 State, 1 PilotInterface, 1 LandingSet, 1 Door, 1 Hydraulic, 1 DigitalSystem, 1 AnalogicSystem