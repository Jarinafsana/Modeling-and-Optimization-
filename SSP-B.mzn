/*
 *
 * Copyright: Gustav Bjordal and Pierre.Flener at it.uu.se, 2024.
 *
 * This file is part of courses 1DL442 and 1DL451 at Uppsala
 * University in Sweden.
 *
 * Permission is hereby granted only to the registered students of
 * those courses to use this file, for a homework assignment.
 *
 * The copyright notice and permission notice above shall be
 * included in all copies and extensions of this file, and those
 * are not allowed to appear publicly on the internet, both during
 * a course instance and forever after.
 *
 */

%%% Team 17, UU, courses 1DL442 and 1DL451, Assignment 3, 2024
%%%
%%% Fill in for every "..." and delete all irrelevant text

include "globals.mzn";
%include "gecode.mzn";     
%%% Parameters:
int: nScooters;  % number of scooters
int: nEmployees; % number of employees
int: dummy;      % dummy employee        
constraint assert(not(dummy in 1..nEmployees), "Dummy cannot be an employee");

%%% Derived parameters:
int: nNodes = nScooters + 2*nEmployees; % number of nodes: each scooter location, and each employee has start and end locations, defined a few lines down
%% Some of the following sets may be unnecessary for your model, and you may want to add more sets:
set of int: Scooters = 1..nScooters;
set of int: Employees = 1..nEmployees;
set of int: EmployeesAndDummy = 1..nEmployees union {dummy};
set of int: Nodes = 1..nNodes;
% StartNode[e] = start location of employee e:
array[Employees] of int: StartNode = [n | n in (nScooters+1)..(nScooters+nEmployees)];
% EndNode[e] = end location of employee e:
array[Employees] of int: EndNode = [n | n in (nScooters+nEmployees+1)..(nScooters+nEmployees+nEmployees)]; 

%%% More parameters:
% TravelTime[f,t] = estimated time of travelling from node f to node t and then servicing the scooter, if any, at node t:
array[Nodes, Nodes] of int: TravelTime;
% Priority[s] = priority that some employee services scooter s:
array[Scooters] of int: Priority;
% Payment[s] = payment that any employee would receive for servicing scooter s:
array[Scooters] of int: Payment;   
% MinNumScooters[e] = minimum number of scooters that employee e is willing to service:
array[Employees] of int: MinNumScooters;
% MaxNumScooters[e] = maximum number of scooters that employee e is willing to service:
array[Employees] of int: MaxNumScooters;
% MaxTime[e] = preferred maximum travel time of employee e:
array[Employees] of int: MaxTime;
int: alpha; % weight in objective function of total overtime
int: beta;  % weight in objective function of total payment
int: gamma; % weight in objective function of total priority loss

%%% Variables (including redundant ones) and constraints (including channelling ones):

%% Giant-tour formulation:
array[Nodes] of var Nodes: Succ; % Succ[n] = successor of node n
constraint subcircuit(Succ) :: domain_propagation; % it's a sub-tour
constraint forall(e in 1..nEmployees - 1) (
    Succ[EndNode[e]] = StartNode[e + 1]  % Successor points to the next employee's start node
);

constraint Succ[EndNode[nEmployees]] = StartNode[1];

%% Which node is visited by which employee (as per the giant tour):
% VisitedBy[n] = employee, possibly dummy, who visits node n:
array[Nodes] of var EmployeesAndDummy: VisitedBy; % non-mutually redundant with Succ
% Each StartNode[e] and EndNode[e] are visited by employee e:
constraint forall(e in Employees)(VisitedBy[StartNode[e]] = e /\ VisitedBy[EndNode[e]] = e);
% The successor of each scooter node n is visited by the same employee as n, even if it is their end node:
constraint forall(s in Scooters)(VisitedBy[Succ[s]] = VisitedBy[s]);
% The successor of each start node n is visited by the employee starting at n, even if it is their end node:
constraint forall(e in Employees)(VisitedBy[Succ[StartNode[e]]] = e);
% The successor of each scooter node n is n if and only if node n is visited by the dummy employee:
constraint forall(n in Nodes)(
    (Succ[n] == n) -> (VisitedBy[n] = dummy)
);

%% Number of scooters serviced by each employee:
% NumServiced[e] = number of scooters serviced by employee e:
array[Employees] of var 0..nScooters: NumServiced; % non-mutually redundant with VisitedBy
constraint forall(e in Employees)(
  NumServiced[e] = sum(s in Scooters)(if VisitedBy[s] = e then 1 else 0 endif)
);
% Each employee e services either 0 scooters or from MinNumScooters[e] to MaxNumScooters[e] scooters:
constraint forall(e in Employees)(
  (NumServiced[e] = 0) \/ (MinNumScooters[e] <= NumServiced[e] /\ NumServiced[e] <= MaxNumScooters[e])
);

%% Overtime cost:
% AccumulatedTravelTime[n] = travel time accumulated when arriving at node n since its employee departed from their start node:
array[Nodes] of var 0..sum(TravelTime): AccumulatedTravelTime; % non-mutually redundant with Succ

constraint forall(e in Employees)(
    AccumulatedTravelTime[StartNode[e]] = 0
);
constraint forall(n in Nodes)(
    if (Succ[n] in Scooters \/ Succ[n] in EndNode) /\ (VisitedBy[n] != dummy) then
        AccumulatedTravelTime[Succ[n]] = AccumulatedTravelTime[n] + TravelTime[n, Succ[n]]
    else
        true
    endif
    
   );

array[Employees] of var 0..sum(TravelTime): EmployeeAccumulatedTravelTime;  
% Set each employee's accumulated travel time based on their corresponding end node
constraint forall(e in Employees)(
    EmployeeAccumulatedTravelTime[e] = AccumulatedTravelTime[EndNode[e]]
);
% Overtime[e] = amount of travel time of employee e that exceeds MaxTime[e]:
% array[Employees] of var 0..sum(TravelTime): Overtime; % non-mutually redundant with AccumulatedTravelTime
% constraint ...; % ... semantics ...; 1-way channelling from ... to ...
% Total overtime over all the employees:
var 0..sum(TravelTime): totalOvertime; % non-mutually redundant with Overtime
constraint 
    totalOvertime = sum(i in 1..nEmployees)(
        max(0, EmployeeAccumulatedTravelTime[i] - MaxTime[i])
    );

%% Employee payment:
% EmployeePayment[e] = payment to employee e, possibly dummy, for all scooters serviced by e:
array[EmployeesAndDummy] of var 0..sum(Payment): EmployeePayment; % non-mutually redundant with VisitedBy (note that we only include the dummy employee here so that the indexing matches the domain of the variablees VisitedBy[n] in case this is useful for using a global constraint)
constraint forall(e in EmployeesAndDummy)(
  EmployeePayment[e] = sum(s in Scooters)(if VisitedBy[s] = e then Payment[s] else 0 endif)
);
% Total payment over all the employees, excluding the dummy one:
var 0..sum(Payment): totalPayment; % non-mutually redundant with EmployeePayment
constraint totalPayment = sum(e in Employees)(EmployeePayment[e]);

%% Priority loss:
% Total priority of all scooters that are not serviced by any actual employee:
var 0..sum(Priority): totalPriorityLoss; % non-mutually redundant with VisitedBy
constraint totalPriorityLoss = sum(s in Scooters)(if VisitedBy[s] = dummy then Priority[s] else 0 endif);

%% Objective variable:
var int: obj; % non-mutually redundant with ...
constraint obj = alpha * totalOvertime - beta * totalPayment + gamma * totalPriorityLoss; % 1-way channelling from ... to ...

include "gecode.mzn";                      % use only for Task B

% Task B tuning parameters rho and sigma:
int: rho; 
int: sigma;

% Solve with annotations for Gecode (restart strategy and LNS)
solve :: restart_constant(rho)  % Restart after 'rho' nodes
      :: relax_and_reconstruct(Succ, sigma)  % Use 'sigma' percentage of variables  
minimize obj;
