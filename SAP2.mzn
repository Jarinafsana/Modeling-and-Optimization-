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

include "globals.mzn";

%% Parameters:
int: weeks; % number of weeks for the planning
int: types; % number of types of spacecraft
% Order[t,w] = number of spacecrafts of type t that are to be assembled by the end of week w:
array[1..types,1..weeks] of int: Order;
int: storageCost; % cost of storing one spacecraft during one week
% SetupCost[t1,t2] = cost of adapting factory from type t1 to t2:
array[1..types,1..types] of int: SetupCost;

%% Derived parameters:
int: spacecrafts = sum(Order); % number of spacecrafts to assemble
% DueWeek[s] = week where spacecraft s is due:
array[1..spacecrafts] of int: DueWeek = [w | t in 1..types, w in 1..weeks, n in 1..Order[t, w] where Order[t, w] > 0];
% Type[s] = type of spacecraft s:
array[1..spacecrafts] of int: Type = [t | t in 1..types, w in 1..weeks, n in 1..Order[t, w] where Order[t, w] > 0];

%% Decision variables:
% WeekAssigned[s] = week where spacecraft s is assigned to:
array[1..spacecrafts] of var 1..weeks: WeekAssigned;
% SortedIndices[s] = Indices of the sorted WeekAssigned representing the original WeekAssigned:
array[1..spacecrafts] of var int: SortedIndices;
% SortedTypes[s] = Shuffled spacecraft types according to the sorted indices:
array[1..spacecrafts] of var int: SortedTypes;
var int: totalSetupCost; % setup cost of the spacecraft type change

var int: totalStorageCost; % storage cost of the spacecraft

%% Redundant decision variables:
% None

%% Channelling constraints:
% None

%% Problem constraints:
% Ensuring that no spacecraft is assembled after its due date:
constraint forall(s in 1..spacecrafts) (
    WeekAssigned[s] <= DueWeek[s]
);

% At most one spacecraft assembled per week:
constraint forall(w in 1..weeks) (
    sum(s in 1..spacecrafts)(WeekAssigned[s] == w) <= 1
);

% Storage cost calculation using the difference between due week and assigned week:
constraint totalStorageCost = sum(s in 1..spacecrafts) (
    storageCost * max(0, DueWeek[s] - WeekAssigned[s])
);
%Sorting the WeekAssigned array using arg_sort and generating an array representing the indices of the sorted array from the original array:
constraint SortedIndices = arg_sort(WeekAssigned);

%Shuffling the Type array based on sorted_indices:
constraint SortedTypes = [ Type[SortedIndices[s]] | s in 1..spacecrafts ];

% The total setup cost from the shuffled type array:
constraint totalSetupCost = sum(s in 1..spacecrafts-1)(
    SetupCost[SortedTypes[s], SortedTypes[s+1]]
);


%% Implied constraints:
% None
var int: totalCost = totalStorageCost + totalSetupCost :: add_to_output;
%% Objective and objective function:
solve minimize totalCost;

%% Pretty-print solutions:
output [
    "Total cost: ", show(totalStorageCost + totalSetupCost), "\n",
    "Week assignments: ", show(WeekAssigned), "\n",
    "Spacecraft types: ", show(Type), "\n",
    "Due weeks: ", show(DueWeek)
];