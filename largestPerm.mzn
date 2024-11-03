
% products of all pairs of successive values in the permutation.

% Parameters
int: n; % The number of integers to permute.

% Derived Parameters
set of int: V = 1..n;

% Decision Variables
array[V] of var V: v; % The permutation of the integers from 1 to n.
% Explanation: 'v' is an array representing the permutation of the numbers 1 to n.

% Correct Constraint for Permutation
constraint forall(i, j in V where i != j) (v[i] != v[j]); 
% Explanation: This constraint ensures that all elements in the array 'v' are distinct,

% Objective Function
var int: objective = sum(i in 1..n-1)(v[i] * v[i+1]);
% Explanation: The 'objective' variable calculates the sum of the products of successive pairs 
% in the permutation. This is the value we want to maximize.

solve maximize objective;
% Explanation: The solve directive aims to maximize the value of the 'objective' variable, 
% which represents the sum of the products of all successive pairs in the permutation.

% Pretty-print solutions: Output
output [
    "The maximum sum of products of successive pairs is: \(objective)\n",
    "The optimal permutation is: [", show(v), "]"
];