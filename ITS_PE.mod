/*********************************************
 * OPL 12.9.0.0 Model
 * Author: ludov
 * Creation Date: 24 f�vr. 2020 at 10:51:33
 *********************************************/


 /*											DATA 					*/
{int} Operator = ...; //  J operators
{int} Competence = ...; // K competences

//Competences
int demand[Competence];	// (dk) The hourly demand of the competence

//Operators
int hourlyAvailability[Operator];	// (aj) The hourly availability of operator

//Others
int minOperator[Competence];		// (min_opk) The minimum number of operators that has to be qualified on competence k
int maxOperator[Competence];		// (min_opj) The maximum number of operators that has to be qualified on competence k

int minVersatility;	// The maximum number of competences an operator can possess
int maxVersatility; // The minimum number of competences an operator can possess

{int} nbOfCompetencesPerPerson;
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
    sum(k in Competence) OperatorCompetenceMatrix[j][k] >= Team[j] * minVersatility; // (II.4)(8)
  
  forall(j in Operator)
    sum(k in Competence) OperatorCompetenceMatrix[j][k] <= Team[j] * maxVersatility; // (II.4)(9)
      
  forall(j in Operator)
    sum(i in minVersatility..maxVersatility) nbOfCompetencesOwned[j]<=1; // (II.4)(10)
      
  forall(j in Operator)
    sum(i in minVersatility..maxVersatility) nbOfCompetencesOwned[j] >= Team[j]; // (II.4)(11)
  
  forall(i in minVersatility..maxVersatility)
    forall(j in Operator)
      sum(k in Competence) OperatorCompetenceMatrix[j][k] >= i*nbOfCompetencesOwned[j]; // (II.4)(12)
  
  forall(i in minVersatility..maxVersatility)
    forall(j in Operator)
      maxVersatility*(1-Team[j])+i-sum(k in Competence)OperatorCompetenceMatrix[j][k] >= maxVersatility*(1-nbOfCompetencesOwned[j]); // (II.4)(13)
  
  if(nbOfCompetencesPerPerson == 0)
  {
  	forall(j in Operator)
  	  1-Team[j] <= nbOfCompetencesOwned[j]; // (II.4)(14)
  }
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
