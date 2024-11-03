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

%%% Parameters:
int: nScooters;  % number of scooters
int: nEmployees; % number of employees
int: dummy;      % dummy employee        
constraint assert(not(dummy in 1..nEmployees), "Dummy cannot be an employee");

%%% Derived parameters:
int: nNodes = nScooters + 2*nEmployees; % number of nodes: each scooter location, and each employee has start and end locations, defined a few lines down
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
%% Decision variable:
%% Giant-tour formulation:
array[Nodes] of var Nodes: Succ; % Succ[n] = successor of node n
constraint subcircuit(Succ) :: domain_propagation; % it's a sub-tour

% Each node's Successor points to the next employee's start node:
constraint forall(e in 1..nEmployees - 1) (
    Succ[EndNode[e]] = StartNode[e + 1] % 1-way channelling from EndNode to StartNode.
);

% The last end node's successor points to the first employee's start node:
constraint Succ[EndNode[nEmployees]] = StartNode[1]; % 1-way channelling from EndNode[nEmployees] to StartNode[1].

%% Which node is visited by which employee (as per the giant tour):
% VisitedBy[n] = employee, possibly dummy, who visits node n:
%% Decision variable:
array[Nodes] of var EmployeesAndDummy: VisitedBy; % non-mutually redundant with Succ

% Each StartNode[e] and EndNode[e] are visited by employee e:
constraint forall(e in Employees)(VisitedBy[StartNode[e]] = e /\ VisitedBy[EndNode[e]] = e); %1-way channelling from StartNode and EndNode to VisitedBy

% The successor of each scooter node n is visited by the same employee as n, even if it is their end node:
constraint forall(s in Scooters)(VisitedBy[Succ[s]] = VisitedBy[s]); % 1-way channelling from Succ to VisitedBy.

% The successor of each start node n is visited by the employee starting at n, even if it is their end node:
constraint forall(e in Employees)(VisitedBy[Succ[StartNode[e]]] = e); %  1-way channelling from Succ[StartNode[e]] to VisitedBy

% The successor of each scooter node n is n if and only if node n is visited by the dummy employee:
constraint forall(n in Nodes)(
    (Succ[n] == n) -> (VisitedBy[n] = dummy) % 1-way channelling from Succ to VisitedBy
);

%% Decision variable:
%% Number of scooters serviced by each employee:
% NumServiced[e] = number of scooters serviced by employee e:
array[Employees] of var 0..nScooters: NumServiced; % non-mutually redundant with VisitedBy

% The number of scooters serviced by each employee
constraint forall(e in Employees)(
  NumServiced[e] = sum(s in Scooters)(if VisitedBy[s] = e then 1 else 0 endif)
); % 1-way channelling from VisitedBy to NumServiced.

% Each employee e services either 0 scooters or from MinNumScooters[e] to MaxNumScooters[e] scooters:
constraint forall(e in Employees)(
  (NumServiced[e] = 0) \/ (MinNumScooters[e] <= NumServiced[e] /\ NumServiced[e] <= MaxNumScooters[e]) % 1-way channelling from NumServiced to ensure the range between MinNumScooters and MaxNumScooters.
);

%% Overtime cost:
%% Decision variable:
% AccumulatedTravelTime[n] = travel time accumulated when arriving at node n since its employee departed from their start node:
array[Nodes] of var 0..sum(TravelTime): AccumulatedTravelTime; % non-mutually redundant with Succ

% The accumulated travel time at each employee's start node is set to 0:
constraint forall(e in Employees)(
    AccumulatedTravelTime[StartNode[e]] = 0 % 1-way channelling from StartNode to AccumulatedTravelTime
);

% The accumulated travel time is updated for the successor node based on the travel time from the current node, but only if the successor is a scooter or end node and the current node is visited by an actual employee:
constraint forall(n in Nodes)(
    if (Succ[n] in Scooters \/ Succ[n] in EndNode) /\ (VisitedBy[n] != dummy) then
        AccumulatedTravelTime[Succ[n]] = AccumulatedTravelTime[n] + TravelTime[n, Succ[n]]
    else
        true
    endif
    
   ); % 1-way channelling from Succ and VisitedBy to AccumulatedTravelTime to propagate travel time between nodes.

% EmployeeAccumulatedTravelTime[n] = travel time accumulated accured by each employee:
array[Employees] of var 0..sum(TravelTime): EmployeeAccumulatedTravelTime;  
% Each employee's accumulated travel time is set based on their corresponding end node
constraint forall(e in Employees)(
    EmployeeAccumulatedTravelTime[e] = AccumulatedTravelTime[EndNode[e]] 
); % 1-way channelling from EndNode and AccumulatedTravelTime to EmployeeAccumulatedTravelTime

%% Decision variable:
% Total overtime over all the employees:
var 0..sum(TravelTime): totalOvertime; % non-mutually redundant with Overtime
 
% The total overtime based on how much each employee exceeds their allowed maximum time.
constraint 
    totalOvertime = sum(i in 1..nEmployees)(
        max(0, EmployeeAccumulatedTravelTime[i] - MaxTime[i])
    ); % 1-way channelling from EmployeeAccumulatedTravelTime and MaxTime to totalOvertime

%% Decision variable:
%% Employee payment:
% EmployeePayment[e] = payment to employee e, possibly dummy, for all scooters serviced by e:
array[EmployeesAndDummy] of var 0..sum(Payment): EmployeePayment; % non-mutually redundant with VisitedBy (note that we only include the dummy employee here so that the indexing matches the domain of the variablees VisitedBy[n] in case this is useful for using a global constraint)

% The payment for each employee and the dummy based on the scooters they service.
constraint forall(e in EmployeesAndDummy)(
  EmployeePayment[e] = sum(s in Scooters)(if VisitedBy[s] = e then Payment[s] else 0 endif)
);%1-way channelling from VisitedBy and Payment to EmployeePayment

% Total payment over all the employees, excluding the dummy one:
var 0..sum(Payment): totalPayment; % non-mutually redundant with EmployeePayment
constraint totalPayment = sum(e in Employees)(EmployeePayment[e]); % 1-way channelling from EmployeePayment to totalPayment 

%% Decision variable:
%% Priority loss:
% Total priority of all scooters that are not serviced by any actual employee:
var 0..sum(Priority): totalPriorityLoss; % non-mutually redundant with VisitedBy
constraint totalPriorityLoss = sum(s in Scooters)(if VisitedBy[s] = dummy then Priority[s] else 0 endif); % 1-way channelling from VisitedBy and Priority to totalPriorityLoss

%% Objective variable:
var int: obj; % non-mutually redundant with ...
constraint obj = alpha * totalOvertime - beta * totalPayment + gamma * totalPriorityLoss; % 1-way channelling from totalOvertime, totalPayment, and totalPriorityLoss to obj 

solve
  %%% Search strategy:
  %% for Task A:
  % Search strategy:
  % Using int_search on the Succ array to find a solution:
  % first_fail: selects the variable with the smallest domain first, helping to reduce the branching factor by focusing on the most constrained variable. 
  % indomain_min: assigns the smallest possible value within the domain to the selected variable, aiming to find feasible solutions early.
  % complete: performs a complete search to ensure that all possible assignments are explored until an optimal solution is found.
  % This strategy is used to efficiently explore the space of successor nodes in the giant tour representation of the problem, ensuring quick discovery of feasible tours and eventual optimization.
  :: int_search(Succ, first_fail, indomain_min, complete)
  %% Objective and objective function:
  minimize obj;