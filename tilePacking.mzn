include "globals.mzn"; 

% (Parameter) Number of tiles (1×1, 2×2, ..., n×n)
int: n;  % Number of tiles

% (Decision Variables) Declare the width and height of the bounding rectangle
var n..n*(n+1) div 2: w;  % Width of the bounding rectangle
var n..n*(n+1) div 2: h;  % Height of the bounding rectangle

% (Derived Parameter) Set representing all tiles
set of int: Tiles = 1..n;

% (Derived Parameter) The size of each tile is i×i for tile i
array[Tiles] of int: sizes = [i | i in Tiles];

% (Parameter) Maximum possible width and height (used for bounds in x and y)
int: max_size = n * (n + 1) div 2;

% (Decision Variables) Variables representing the bottom-left corner coordinates of each tile (x[i], y[i])
array[Tiles] of var 0..max_size: x;  
array[Tiles] of var 0..max_size: y;

% (Constraints) Ensure that all tiles fit within the bounding rectangle
constraint forall(i in Tiles) (
    x[i] + sizes[i] <= w /\ y[i] + sizes[i] <= h
);

% (Constraint) Using the diffn predicate to ensure no overlapping tiles
constraint diffn(x, y, sizes, sizes);

% (Symmetry-breaking Constraint) Ensure the largest tile is placed in a specific area
constraint 2 * x[n] < w /\ 2 * y[n] < h;

% (Objective) Minimize the area of the bounding rectangle (w * h)
solve minimize w * h;

% (Output) Display the results
output [
    "Width: ", show(w), "\n",
    "Height: ", show(h), "\n",
    "Tile positions:\n",  % 
    concat([ "Tile " ++ show(i) ++ ": (" ++ show(x[i]) ++ "," ++ show(y[i]) ++ ")\n" | i in Tiles ]),  % Display positions of each tile
    "\n(w, h, w * h): (", show(w), ", ", show(h), ", ", show(w * h), ")\n"  % Include the tuple in the output
];
