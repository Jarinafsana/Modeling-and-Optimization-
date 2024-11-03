include "globals.mzn";

% (Parametters) Number of couples
int: couples = 5; 
int: n = 2 * couples;  % Total number of people (both husbands and wives).

% (Derived Parameter) Set representing all individuals (husbands and wives) where husbands (1..5) and wives (6..10).
set of int: Persons = 1..n;

% Decision variable: 2D array where each element indicates whether person i shakes hands with person j
array[Persons, Persons] of var 0..1: handshake; 
 
% The `handshake[i, j]` variable is a decision variable where:
%   - 1 means that person `i` shakes hands with person `j`.
%   - 0 means that they do not shake hands.
% The array is symmetric and has size `n x n`, representing all handshakes among all people.

% (Derived parameters): To represent spouses
array[1..couples] of int: spouse_wife = [i | i in 1..couples];  
% This array represents that husband `i` is married to wife `i`. For example, husband 1 is married to wife 1.

array[1..couples] of int: spouse_husband = [i | i in 1..couples];  
% Similarly, this array represents that wife `i` is married to husband `i`.

% Problem constraints enforced by decision variables:

% Constraint: No husband shakes hands with his own wife
constraint forall(h in 1..couples) (
    handshake[h, couples + h] = 0  % `handshake[h, couples + h] = 0` ensures that husband `h` does not shake hands with his wife.
);

% Constraint: No wife shakes hands with her own husband
constraint forall(w in (couples + 1)..n) (
    handshake[w, w - couples] = 0  % `handshake[w, w - couples] = 0` ensures that wife `w` does not shake hands with her husband.
);

% Constraint: No one shakes hands with themselves
constraint forall(h in 1..couples) (
    handshake[h, h] = 0  % `handshake[h, h] = 0` ensures that husband `h` does not shake hands with himself.
);

constraint forall(w in (couples + 1)..n) (
    handshake[w, w] = 0  % `handshake[w, w] = 0` ensures that wife `w` does not shake hands with herself.
);

% Constraint: Handshakes are mutual (if person i shakes hands with person j, then person j also shakes hands with person i)
constraint forall(i in Persons, j in Persons where i != j) (
    handshake[i, j] = handshake[j, i]  % Enforces that `handshake[i, j]` is symmetric, meaning mutual handshakes between `i` and `j`.
);

% Derived parameter: Array of row sums representing how many people each individual shakes hands with
array[Persons] of var 0..(n-1): row_sums = [sum([handshake[i, j] | j in Persons]) | i in Persons];  


% Constraint: Ensure that all row sums (handshakes) are different, except for Halmos (person 1)
constraint all_different([row_sums[h] | h in 2..n]);  

% Constraint: Count handshakes for Halmos' wife (person 6)
var int: halmos_wife_handshakes = row_sums[couples + 1];  % Halmos' wife is person 6

% Array to store handshake counts for wives only (wives are indexed from 6 to 10)
array[1..couples] of var 0..(n-1): wife_handshake_counts = [row_sums[couples + w] | w in 1..couples];  

% Constraint: Ensure uniqueness of Halmos' wife's handshake count among all wives
constraint all_different(wife_handshake_counts); 

% Solving the problem to satisfy the constraints
solve satisfy;

% Output:
% - The handshake matrix shows whether two individuals shake hands (1 means they do, 0 means they don't).
% - The row sums show how many people each person shakes hands with.
% - Halmos' wife's handshake sum is shown separately.
output [
    "Handshake matrix:\n",
    concat([concat([show(handshake[i, j]) ++ " " | j in Persons]) ++ "\n" | i in Persons]),  % Display the handshake matrix
    "\nRow sums:\n",
    concat([show(row_sums[i]) ++ " " | i in Persons]),  % Display the handshake sums for each person
    "\n\nHalmos' wife's handshake sum: ",
    show(row_sums[couples + 1])  % Display the number of people Halmos' wife shakes hands with
];