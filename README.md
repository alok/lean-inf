# lean-inf


Compute with infinities and infinitesimals! A calculator using the Levi-Civita field, implemented in Lean 4 as a datatype.

## Usage Examples

```lean

-- create a number 

def x := lc[1, ϵ] -- 1 + ϵ

-- compute with it

def y := x^2 -- 1 + 2ϵ + ϵ^2

#eval y -- 1 + 2ϵ + ϵ^2

```

