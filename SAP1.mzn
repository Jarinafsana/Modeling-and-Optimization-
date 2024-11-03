/*
 *
 * Copyright: Pierre.Flener at it.uu.se and his TAs, 2024.
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

%%% Team 17, UU, courses 1DL442 and 1DL451, Assignment 2, 2024
%%%
%%% This model minimizes the storage and setup costs in a spacecraft
%%% assembly problem. The goal is to assemble spacecrafts by their 
%%% due dates while minimizing the total cost.

include "globals.mzn";

%% Parameters:
int: weeks; % number of weeks for the planning
int: types; % number of types of spacecraft
% Order[t,w] = number of spacecrafts of type t that are to be assembled by the end of week w:
array[1..types, 1..weeks] of int: Order;
int: storageCost; % cost of storing one spacecraft during one week
% SetupCost[t1,t2] = cost of adapting factory from type t1 to t2:
array[1..types, 1..types] of int: SetupCost;

%% Derived parameters:
int: spacecrafts = sum(Order); % total number of spacecrafts to assemble

% Flatten the Order array to create a list of spacecrafts, their types, and due weeks:
array[1..spacecrafts] of int: DueWeek = 
  [w | t in 1..types, w in 1..weeks, o in 1..Order[t,w]where Order[t, w] > 0];
array[1..spacecrafts] of int: Type = 
  [t | t in 1..types, w in 1..weeks, o in 1..Order[t,w] where Order[t,w] >0];

%% Decision variables:
% Assignment of each spacecraft to a specific week:
array[1..spacecrafts] of var 1..weeks: WeekAssigned; 
% WeekType[w] indicates the spacecraft type assembled in week w (0 if no spacecraft is assembled):
array[1..weeks] of var 0..types: WeekType;
var int: totalStorageCost;
var int: totalSetupCost;
%% Redundant decision variables:
% ... semantics ...; (non-)mutually redundant with ...
% None

%% Channelling constraints:
% 1-way from ... to ... / 2-way between ... and ...
% None
%% Problem constraints:
% Ensure each spacecraft is assembled no later than its due week:
constraint forall(s in 1..spacecrafts) (
    WeekAssigned[s] <= DueWeek[s]
);
% Ensure no more than one spacecraft is assembled per week:
constraint forall(w in 1..weeks) (
    sum([bool2int(WeekAssigned[s] == w) | s in 1..spacecrafts]) <= 1
);

% WeekType[w] must match the type of spacecraft assembled in that week:
constraint forall(w in 1..weeks) (
    WeekType[w] = sum([Type[s] * bool2int(WeekAssigned[s] == w) | s in 1..spacecrafts])
);

% Storage cost: Only incurred if spacecraft is assembled before its due date
constraint totalStorageCost = sum(
    [storageCost * (DueWeek[s] - WeekAssigned[s]) * bool2int(WeekAssigned[s] < DueWeek[s]) 
     | s in 1..spacecrafts]
);
% Setup cost: Switching between different spacecraft types from one week to the next,
% even if there are gaps with no assembly
constraint totalSetupCost = sum(
    [SetupCost[WeekType[w], WeekType[w_gap]] 
     | w in 1..weeks-1, w_gap in w+1..weeks 
     where WeekType[w] > 0 /\ WeekType[w_gap] > 0 /\ forall(i in w+1..w_gap-1)(WeekType[i] == 0)]
);
% Objective: Minimize the sum of storage and setup costs
solve minimize totalStorageCost + totalSetupCost;
%% Pretty-print solutions:
output [

  "Total Storage Cost: ", show(totalStorageCost), "\n",
  "Total Setup Cost: ", show(totalSetupCost), "\n",
  "TotalCost: ", show(totalStorageCost + totalSetupCost), "\n",
  "Spacecrafts assigned to weeks: ", show(WeekAssigned), "\n",
  "Types assembled in each week: ", show(WeekType)
];