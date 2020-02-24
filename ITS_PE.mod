/*********************************************
 * OPL 12.9.0.0 Model
 * Author: ludov
 * Creation Date: 24 févr. 2020 at 10:51:33
 *********************************************/
 
{int} Operator = ...;
{int} Competence = ...;
int OperatorCompetenceMatrix[Operator][Competence] = ...;
int HourlyWorkingTime[Operator][Competence] = ...;
{int} OperatorIsIncluded = ...;
int nbOfCompetencesOwned[Operator] = ...;

int Team[Operator] = ...;

dexpr int totalTeam = sum(i in Operator) Team[i];

minimize totalTeam;
constraints {

  // the capacity rate is adapted to intervals of 10 minutes;
  // the time scale of a resource is divided by the time step
  forall (i in SectorNames)
      forall (p in periods[i])
         alwaysIn(r[i], (p.start.hours * 60 + p.start.minutes) div timeStep,
                        (p.end.hours * 60 + p.end.minutes) div timeStep,
                           0,
                        (p.rate * timeStep + 59) div 60);


   // a flight enters a sector at its expected time-over plus its delay;
   // since the time scale of a resource is divided by the time step,
   // we do the same for the start time of the activity
   forall (i in Enters)
      startOf(a[i]) == (delay[e[i].flight] + e[i].eto.hours * 60 + e[i].eto.minutes) div timeStep;

   forall(i in SectorNames)
     r[i] <= nbOfFlights;
}

execute {
  writeln("Member in team = " + totalTeam);
}