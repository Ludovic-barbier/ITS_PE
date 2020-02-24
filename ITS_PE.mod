/*********************************************
 * OPL 12.9.0.0 Model
 * Author: ludov
 * Creation Date: 24 f�vr. 2020 at 10:51:33
 *********************************************/
 
 
 /*											DATA 					*/
{int} Operator = ...; //  J operators
{int} Competence = ...; // K competences

//Competences
int demand[Competence];	// The hourly demand of the competence (dk)

//Operators
int hourlyAvailability[Operator];	// The hourly availability of operator (aj)

//Others
int minOperator[Competence];		// The minimum number of operators that has to be qualified on competence k
int maxOperator[Competence];		// The maximum number of operators that has to be qualified on competence k



int OperatorCompetenceMatrix[Operator][Competence] = ...; //xjk
int HourlyWorkingTime[Operator][Competence] = ...; //tjk
int nbOfCompetencesOwned[Operator] = ...; //oij

int Team[Operator] = ...; // zj 

dexpr int totalTeam = sum(i in Operator) Team[i]; // Sum(zj)

int c[Competence][Competence]; //ckk'

int alpha[Competence];
minimize totalTeam;
constraints {

  forall(k in Competence)
     sum(j in Operator) OperatorCompetenceMatrix[j][k] >= minOperator[k]; // (II.4)(1)
       
  forall(k in Competence)
     sum(j in Operator) OperatorCompetenceMatrix[j][k] <= maxOperator[k]; // (II.4)(2)
       
  forall(j in Operator)    
  	 forall(k in Competence)
  	   forall(k2 in Competence)
  	     if(c[k][k2] == 0) {
  	     	OperatorCompetenceMatrix[j][k] + OperatorCompetenceMatrix[j][k2] <= 1;  	 //(II.4)(3)     
  	     }
  
  forall(j in Operator)
    sum(k in Competence) HourlyWorkingTime[j][k] <= hourlyAvailability[j]; // (II.4)(4)
      
  forall(k in Competence)
    sum(j in Operator) HourlyWorkingTime[j][k] >= demand[k]; // (II.4)(5)
      
  forall(j in Operator)
    forall(k in Competence)
      HourlyWorkingTime[j][k] >= alpha[k]*hourlyAvailability[j]*OperatorCompetenceMatrix[j][k]; // (II.4)(6)
      
  forall(j in Operator)
    forall(k in Competence)
      HourlyWorkingTime[j][k] <= hourlyAvailability[j]*OperatorCompetenceMatrix[j][k]; // (II.4)(7)
  
  forall(j in Operator)
    sum(k in Competence)
//  forall (j in Operator)
//      forall (p in periods[i])
//         alwaysIn(r[i], (p.start.hours * 60 + p.start.minutes) div timeStep,
//                        (p.end.hours * 60 + p.end.minutes) div timeStep,
//                           0,
//                        (p.rate * timeStep + 59) div 60);
//
//
//   // a flight enters a sector at its expected time-over plus its delay;
//   // since the time scale of a resource is divided by the time step,
//   // we do the same for the start time of the activity
//   forall (i in Enters)
//      startOf(a[i]) == (delay[e[i].flight] + e[i].eto.hours * 60 + e[i].eto.minutes) div timeStep;
//
//   forall(i in SectorNames)
//     r[i] <= nbOfFlights;
}

execute {
  writeln("Member in team = " + totalTeam);
}