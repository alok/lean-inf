import LeanInf.LeviCivitaNum
import LeanInf.Basic
import LeanInf.Parser



/-- d represents epsilon since it's easier to type.-/
def testCases : List (String × Option LeviCivitaNum) := [
  ("1+ε", some lc[1, ε]),
  ("1/ε", some lc[H]),
  ("ε+ε", some lc[2ε]),
  ("d^2", some lc[ε^2]),
  ("2+2", some lc[4]),
  ("2ε", none),
  ("1+ε", some lc[1, ε]),
  ("1/ε", some lc[H]),
  ("ε+ε", some lc[2ε]),
  ("a=6*7;a+5", some lc[47]),
  ("zzz=1;zzz==1", some lc[1]),
  ("f x=x^2;f(f(2))", some lc[16]),
  ("(1+ε)^pi", none),
  ("ε^pi", none),
  ("[sqrt(ε+ε^2)]^2", some lc[ε^(1/2) , ε^2])
]

/-- Entry point.-/
def main : IO Unit := do
  -- TODO add printing
  IO.println "1+d"

#eval  (p[1ε, 2ε^2, 3ε^3])
#eval! lc[1,H,-1,-1]
#eval! (lc[H,ε, 2ε^2, 3ε^3] : LeviCivitaNum).toPoly

-- Test cases based on the image
-- We'll use the given approximations and verify they square to the original value
-- and that their inverses are close to what's given in the image

-- Test case for √(1 + ε)
#eval let approx := lc[1, 0.5 ε, -0.125 ε^2, 0.0625 ε^3, -0.0390625 ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 + ε, 1 - 0.5ε + 0.375ε^2 - 0.3125ε^3)

-- Test case for √(1 - 0.5ε)
#eval let approx := lc[1, -0.25 ε, -0.03125 ε^2, -0.015625 ε^3, -0.009765625 ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 - 0.5ε, 1 + 0.25ε + 0.1875ε^2 + 0.15625ε^3)

-- Test case for √(1 + ε + ε^2)
#eval let approx := lc[1, 0.5 ε, 0.125 ε^2, 0.0625 ε^3, 0.0390625 ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 + ε + ε^2, 1 - 0.5 ε + 0.125 ε^2 + 0.0625 ε^3)

-- Test case for √(1 - 0.5ε + 0.375ε^2 - 0.3125ε^3)
#eval let approx := lc[1, -0.25ε, -0.03125ε^2, -0.015625ε^3, -0.009765625ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 - 0.5ε + 0.375ε^2 - 0.3125ε^3, 1 + 0.25ε + 0.1875ε^2 + 0.15625ε^3)

-- Test case for √(2 - 0.2813ε^3)
#eval let approx := lc[1.4142135623730950488, -0.0078125ε^3]  -- √2 - 0.0078125ε^3
      let squared := approx * approx
      dbg_trace s!"squared: {squared}"
      let inverse := 1 / approx
      (squared * inverse)
-- Should be close to (2 - 0.2813ε^3, 1/√2 + 0.00276ε^3)

-- Additional test case for √(2 + ε)
#eval let approx := lc[1.4142135623730950488, 0.3535533905932737622ε, -0.0441941738241592203ε^2, 0.0220970869120796101ε^3, -0.0138106793200497563ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (2 + ε, 1/2 - ε/(4√2) + 3ε^2/(32√2) - 5ε^3/(128√2))
#eval lc[1, H, -H]
