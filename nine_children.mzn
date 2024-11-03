% Use this editor as a MiniZinc scratch book
% Parameters:
int: maxAge = 150; % The maximum possible age for any person
int: numChildren = 9; % The number of children

% Derived parameters:
set of int: Ages = 1..maxAge; % Possible range of ages for both the parent and the children

% Decision variables:
var Ages: parentAge; % Age of the parent
array[1..numChildren] of var Ages: childrenAges; % Ages of the nine children

% Constraints:
constraint forall(i in 1..numChildren - 1) (
  childrenAges[i+1] - childrenAges[i] = childrenAges[2] - childrenAges[1]
); 
% Ensures equal gaps between the ages of consecutive children

constraint parentAge^2 = sum([childrenAges[i] * childrenAges[i] | i in 1..numChildren]);
% The squared age of the parent equals the sum of the squares of the ages of the children

% Ensure all children's ages are distinct
constraint forall(i, j in 1..numChildren where i < j) (childrenAges[i] != childrenAges[j]);

% Ensure parent's age is greater than any child's age
constraint parentAge > max(childrenAges);

% Ensure that ages are within realistic limits
constraint parentAge <= maxAge;

solve satisfy;
% To prove that the solution is unique and to find youngest parent we have to change solve,such as
%solve minimize parentAge
%% Pretty-print solutions:
output [
  "Parent age: \(parentAge) \n",
  "Children ages: " ++ show(childrenAges) ++ "\n",
  "Gap between consecutive children's ages: \(childrenAges[2] - childrenAges[1]) \n",
  "Sum of squares of children's ages: \(sum([childrenAges[i] * childrenAges[i] | i in 1..numChildren])) \n",
  "Squared parent age: \(parentAge * parentAge) \n"
];

