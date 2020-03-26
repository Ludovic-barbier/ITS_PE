/*********************************************
 * OPL 12.9.0.0 Model
 * Author: ludov
 * Creation Date: 24 f�vr. 2020 at 10:51:33
 *********************************************/
 
using CPLEX;

 /*											DATA 					*/
{int} Operator = ...; //  J operators
{int} Competence = ...; // K competences
//Competences
float demand[Competence] = ...;	// (dk) The hourly demand of the competence

//Operators
float hourlyAvailability[Operator] = ...;	// (aj) The hourly availability of operator

//Others
int minOperator[Competence] = ...;		// (min_opk) The minimum number of operators that has to be qualified on competence k
int maxOperator[Competence] = ...;		// (min_opk) The maximum number of operators that has to be qualified on competence k

int minVersatility = ...;	// The maximum number of competences an operator can possess
int maxVersatility = ...; // The minimum number of competences an operator can possess

int compatibility[Competence][Competence] = ...; //(ckk') Say if the competence k and k' can be associated

float timeRatio = ...; //(alpha k) Ratio of time an operator has to spend on competence k


/*											Donn�es int�ressantes � afficher pour la suitee						*/
//int nbCompetencesPerOperator[Operator];
float ratioSkills[minVersatility..maxVersatility]=...;	// (vi) The ratio of operators with i competences. The sum of (vi) have to be 1


/*											VARIABLES							*/
dvar boolean OperatorCompetenceMatrix[Operator][Competence]; //xjk
dvar float HourlyWorkingTime[Operator][Competence]; //tjk
dvar boolean Team[Operator]; // zj
dvar boolean nbOfCompetencesOwned[0..maxVersatility][Operator]; //oij
dvar int nbOfMinCompetencesNeeded[minVersatility..maxVersatility]; //Nimin
dvar int nbOfMaxCompetencesNeeded[minVersatility..maxVersatility]; //Nimax
//dvar int ratioSkills[0..maxVersatility];	// (vi) The ratio of operators with i competences. The sum of (vi) have to be 1


dexpr int totalTeam = sum(j in Operator) Team[j]; // Sum(zj)

    execute
    {
    writeln("demand = ",demand);
    writeln("minOperator = ",minOperator);
    writeln("maxOperator = ",maxOperator);
    writeln("compatibility = ",compatibility);
    }


minimize totalTeam;
constraints {

  c1:
  forall(k in Competence)
     sum(j in Operator) OperatorCompetenceMatrix[j][k] >= minOperator[k]; // (II.4)(1)
  c2:
  forall(k in Competence)
     sum(j in Operator) OperatorCompetenceMatrix[j][k] <= maxOperator[k]; // (II.4)(2)
  c3:
  forall(j in Operator)
       forall(k in Competence)
         forall(k2 in Competence)
           OperatorCompetenceMatrix[j][k] + OperatorCompetenceMatrix[j][k2] <= 1+compatibility[k][k2];  // (II.4)(3)
  c4:
  forall(j in Operator)
    sum(k in Competence) HourlyWorkingTime[j][k] <= hourlyAvailability[j]; // (II.4)(4)
  c5:
  forall(k in Competence)
    sum(j in Operator) HourlyWorkingTime[j][k] >= demand[k]; // (II.4)(5)
  c6:
  forall(j in Operator)
    forall(k in Competence)
      HourlyWorkingTime[j][k] >= timeRatio*hourlyAvailability[j]*OperatorCompetenceMatrix[j][k]; // (II.4)(6)
  c7:
  forall(j in Operator)
    forall(k in Competence)
      HourlyWorkingTime[j][k] <= hourlyAvailability[j]*OperatorCompetenceMatrix[j][k]; // (II.4)(7)

  c8:
  forall(j in Operator)
    sum(k in Competence) OperatorCompetenceMatrix[j][k] >= Team[j] * minVersatility; // (II.4)(8)

  c9:
  forall(j in Operator)
    sum(k in Competence) OperatorCompetenceMatrix[j][k] <= Team[j] * maxVersatility; // (II.4)(9)

  c10:
  forall(j in Operator)
    forall(i in 0..maxVersatility-1)
      nbOfCompetencesOwned[i][j]>= nbOfCompetencesOwned[i+1][j];  // (II.4)(10)

  c11:
  forall(j in Operator)
    sum(i in 0..maxVersatility) nbOfCompetencesOwned[i][j] >= Team[j]*sum(k in Competence) OperatorCompetenceMatrix[j][k] +1; // (II.4)(11)

  c12:
  forall(i in 0..maxVersatility)
	forall(j in Operator)
      sum(k in Competence) OperatorCompetenceMatrix[j][k]  >= i*nbOfCompetencesOwned[i][j]; // (II.4)(12)
   /*
  forall(i in 0..maxVersatility)
    forall(j in Operator)
      maxVersatility*(1-Team[j])+i-sum(k in Competence)OperatorCompetenceMatrix[j][k] >= maxVersatility*(1-nbOfCompetencesOwned[i][j]); // (II.4)(13)
   */

  c14:
  forall(j in Operator)
  	1-Team[j] <= nbOfCompetencesOwned[0][j]; // (II.4)(14)

  c15:
  forall(i in minVersatility..maxVersatility)
    nbOfMinCompetencesNeeded[i] <= ratioSkills[i]*sum(j in Operator) Team[j]; // (II.4)(15)

  c16:
  forall(i in minVersatility..maxVersatility)
    nbOfMinCompetencesNeeded[i] >= sum(j in Operator) Team[j]*ratioSkills[i] - 0.99; // (II.4)(16)

  c17:
  forall(i in minVersatility..maxVersatility)
    nbOfMaxCompetencesNeeded[i] >= sum(j in Operator) Team[j]*ratioSkills[i]; // (II.4)(17)

  c18:
  forall(i in minVersatility..maxVersatility)
    nbOfMaxCompetencesNeeded[i] <= sum(j in Operator) Team[j]*ratioSkills[i]+ 0.99; // (II.4)(18)

  c19:
  forall(i in minVersatility..maxVersatility)
     sum(j in Operator) nbOfCompetencesOwned[i][j] >= nbOfMinCompetencesNeeded[i]; // (II.4)(19)

  c20:
  forall(i in minVersatility..maxVersatility)
    sum(j in Operator) nbOfCompetencesOwned[i][j] <= nbOfMaxCompetencesNeeded[i]; //(II.4)(20)

  cut1:
  sum(j in Operator, k in Competence) HourlyWorkingTime[j][k] >= sum(k in Competence) demand[k];

  cut2:
  sum(j in Operator, k in Competence) HourlyWorkingTime[j][k] <= sum(j in Operator) hourlyAvailability[j];
}
/*
execute {
	var f = new IloOplOutputFile("results.csv");
	for(var i in Competence) {
	  for (var j in Competence) {
	    f.writeln(OperatorCompetenceMatrix[i][j],"\t");
	  }
	  f.writeln("\n");
	}
	f.close();
}*/

execute {
  var ofile = new IloOplOutputFile("stats.txt");

	ofile.writeln("Nb Op: ");
	ofile.write(totalTeam);
	ofile.writeln("\n");
	
	var TotalWorkingTime = 0.0;
	ofile.writeln("Unanswered Demand: ");
	for(var i in Operator){
		for (var j in Competence) {
			TotalWorkingTime = TotalWorkingTime + HourlyWorkingTime[i][j];
		}
	}
	var TotalDemand = 0.0;
	for(var j in Competence) {
	  TotalDemand = TotalDemand + demand[j];
	}
	var UnansweredDemand = 100-(TotalWorkingTime* 100)/TotalDemand;
	ofile.write(UnansweredDemand);
	ofile.write("%");
	ofile.writeln("\n");

	var TotalOperator = Operator.size;
	ofile.writeln("Unoccupied Operators: ");
	var UnoccupiedOperators = 100-(totalTeam*100)/TotalOperator;
	ofile.write(UnoccupiedOperators);
	ofile.write("%");
	ofile.writeln("\n");

  ofile.close();
  
}


execute {
	var ofile = new IloOplOutputFile("results.txt");

	ofile.writeln("Xjk: ");
	for(var i in Competence){
		for (var j in Competence) {
			ofile.write(OperatorCompetenceMatrix[i][j]+"\t");
			}
	ofile.write("\n");
	}
	ofile.writeln("\n");

	ofile.writeln("Tjk: ");
	for(var i in Operator){
		for (var j in Competence) {
			ofile.write(HourlyWorkingTime[i][j]+"\t");
			}
	ofile.write("\n");
	}
	ofile.writeln("\n");

	ofile.writeln("Oij: ");
	for(var i = 0 ; i<maxVersatility ; i++){
		for (var j in Operator) {
			ofile.write(nbOfCompetencesOwned[i][j]+"\t");
			}
	ofile.write("\n");
	}
	ofile.writeln("\n");

	ofile.writeln("Zj: ");
	for(var j in Operator){
		ofile.write(Team[j]+"\t");
	}
	ofile.writeln("\n");

  	ofile.writeln("Nimin: ");
	for(var i = minVersatility ; i<maxVersatility ; i++){
		ofile.write(nbOfMinCompetencesNeeded[i]+"\t");
	}
	ofile.writeln("\n");

	ofile.writeln("Nimax: ");
	for(var i = minVersatility ; i<maxVersatility ; i++){
		ofile.write(nbOfMaxCompetencesNeeded[i]+"\t");
	}
	ofile.writeln("\n");

  ofile.close();
}
