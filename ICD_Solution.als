sig Role {}
sig Person {}

sig Cardiologist extends Role {}
sig ClinicalAssistant extends Role {}
sig Patient extends Role {}

abstract sig Mode {}
sig On extends Mode {}
sig Off extends Mode {}

-- A list of 50 shocks
sig Shocks {}

sig ICD {
	---The person whose ICD this is.
    owner : Person,

	---A relation describing which people are assigned to 
	---particular roles for this ICD.
	roleAssigned: Person->Role,

	--- ICD state variables.
	upperBound: Int,
	numberOfJoulesToDeliver: Int,
   last50Shocks: Shocks,
	mode: Mode
}
--constraints for each ICD
fact {
   --make sure that there are no other roles
	Cardiologist + ClinicalAssistant + Patient = Role
   -- all ICD must have one owner and the owner must be a Patient
   one  icd : ICD | one icd.owner && icd.roleAssigned[icd.owner] in Patient
 
}
--preconditions, defined in the second attempt
pred precondition(icd : ICD){ 
   --each person must have only one role
   all p : Person |  one icd.roleAssigned[p]
   -- there is only one Patient
   one p1 : Person | icd.roleAssigned[p1] in Patient
   -- there may be multiple Cardiologists
   some p2 : Person | icd.roleAssigned[p2] in Cardiologist
   -- there may be multiple ClinicalAssistants
   some p3 : Person | icd.roleAssigned[p3] in ClinicalAssistant 

}
run precondition for 1 ICD, 6 Person, 3 Role, 2  Mode, 1 Shocks

pred SwitchMode (icd, icd' : ICD, person : Person) {
   --make sure each ICD holds the precondition and they are different
   precondition[icd] and  precondition[icd'] and not icd in icd' and
   -- Patients cannot switch the mode
   not icd.roleAssigned[person] in Patient
   --since the Mod signature is abstract, there is no mode apart from On and Off
   --so that we can find the other from difference
   icd'.mode = Mode- icd.mode
}

run SwitchMode for 2 ICD, 6 Person, 3 Role, 2  Mode, 5 Shocks

-- last50Shocks is the output variable
pred ReadLast50Shocks (icd : ICD, person : Person, last50shocks : Shocks) {
   -- make sure the ICD holds the preconditions
   precondition[icd] and
   --ICD must be Off to read the shocks
   not icd.mode in On
   --assign to output variable
   last50shocks = icd.last50Shocks
   --the number of shocks must be lower than 51, {however couldn't be tested, alloy always gives only one?}
   #last50shocks < 51

}

run ReadLast50Shocks for 1 ICD, 6 Person, 3 Role, 2 Mode, 520 Shocks
-- upperBound and numberOfJoules are the output variables
pred ReadSettings (icd : ICD, person : Person, upperbound : Int, numberOfJoules : Int) {
     -- make sure the ICD holds the preconditions
     precondition[icd] and 
     -- ICD must be Off
     not icd.mode in On and
     -- Patients cannot read settings
     not icd.roleAssigned[person] in Patient
   --assign to output variables
     upperbound = icd.upperBound
     numberOfJoules = icd.numberOfJoulesToDeliver
}

run ReadSettings for 1 ICD, 6 Person, 3 Role, 2  Mode, 5 Shocks

pred ChangeSettings (icd, icd' : ICD, person : Person, upperbound : Int, numberOfJoules : Int) {
     --make sure each ICD holds the precondition and they are different
     precondition[icd] and precondition[icd'] and icd not in icd' and
     --ICD must be Off
     not icd.mode in On and
     --Patients and ClinicalAssistants cannot change settings
     not icd.roleAssigned[person] in Patient and
     not icd.roleAssigned[person] in ClinicalAssistant
     -- assign to output variables
     icd'.upperBound = icd.upperBound ++ upperbound
     icd'.numberOfJoulesToDeliver = icd.numberOfJoulesToDeliver ++ numberOfJoules

}
run ChangeSettings for 2 ICD, 6 Person, 3 Role, 2 Mode, 5 Shocks

assert assertChanges{
    all person : Person,  icd, icd' : ICD |
    all oldUpperBound, oldJoule, newUpperBound, newJoule, checkUpperBound, checkJoule : Int |
    --pre-state oldUpperBound and oldJoule
    ReadSettings [icd, person, oldUpperBound, oldJoule]  =>
       --change settings with values of newUpperBound and newJoule variables
    	ChangeSettings [icd, icd', person, newUpperBound, newJoule] => 
           --post-state checkUpperBound and checkJoule
			(ReadSettings [ icd, person, checkUpperBound, checkJoule] => 
             -- check the post-state values with the newUpperBound and newJoule variables
             -- if they are equal the ChangeSettings predicate is valid
				newUpperBound = checkUpperBound and newJoule = checkJoule)
}
check assertChanges for 2 ICD, 6 Person, 3 Role, 2 Mode, 5 Shocks

assert assertOwnerIsPatient{
    -- run the precondition
    one icd : ICD | precondition[icd] =>
    -- check the role of owner
    icd.roleAssigned[icd.owner] in Patient
}
check assertOwnerIsPatient for 1 ICD, 6 Person, 3 Role, 2 Mode, 5 Shocks

assert assertOneRoleForEachPerson{
    -- run the precondition
    one icd : ICD | precondition[icd] =>
    -- check the role of each person whether they have only one role
    all p : Person | one icd.roleAssigned[p]
}
check assertOneRoleForEachPerson for 1 ICD, 6 Person, 3 Role, 2 Mode, 5 Shocks

assert assertMultipleCardiologistAndClinicalAssistant{
    -- run the precondition
    one icd : ICD | precondition[icd] =>
    -- check if there are multiple cardiologists or clinical assistants
    some Cardiologist and some ClinicalAssistant
}
check assertMultipleCardiologistAndClinicalAssistant for 1 ICD, 6 Person, 3 Role, 2 Mode, 5 Shocks



