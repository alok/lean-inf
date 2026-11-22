import LeanInf.LeviCivitaNum
import LeanInf.VerifiedRefactor
import LeanInf.TestSuite

namespace LeanInf.Bench

open LeanInf

/-- Timing measurement for a single benchmark scenario. -/
structure BenchRow where
  /-- Benchmark category (`mul_dense`, `mul_sparse`, `signum`, `pow`, `inv`). -/
  category : String
  /-- Problem size parameter (number of terms, exponent, or truncation order). -/
  size : Nat
  /-- Number of repeated iterations measured. -/
  iters : Nat
  /-- Mean microseconds per operation for the original naive algorithm. -/
  naiveUs : Float
  /-- Mean microseconds per operation for the balanced-tree sparse refactor (if applicable). -/
  sparseUs : Option Float := none
  /-- Mean microseconds per operation for the verified fast refactor (`FastLC`). -/
  fastUs : Float
  /-- Speedup factor `naiveUs / fastUs`. -/
  speedup : Float
  /-- Checksum verifying real work was computed and both implementations agree. -/
  verified : Bool

/-- Non-inlined timing harness passing a distinct loop index `i` to prevent Lean 4 LICM/CSE
    from hoisting pure calls out of the benchmark loop. -/
@[noinline]
private def timeItersUs (iters : Nat) (f : Nat → Int) : IO (Float × Int) := do
  -- Warmup pass
  let _ := f 0
  let t0 ← IO.monoNanosNow
  let mut acc : Int := 0
  for i in [:iters] do
    acc := acc + f i
  let t1 ← IO.monoNanosNow
  let elapsedNs := t1 - t0
  let us := (Float.ofNat elapsedNs) / (Float.ofNat (max iters 1) * 1000.0)
  return (us, acc)

/-- Dense integer-coefficient series `∑_{k=0}^{n-1} c_k ε^k` so `Rat` GCD stays bounded
    and asymptotic complexity (`O(n^2)` vs `O(n^1.585)`) is cleanly measured. -/
private def makeBenchDense (n : Nat) (seed : Int) : FastLC :=
  let terms : TermList := (List.range n).map fun k =>
    let v : Int := ((Int.ofNat k * 13 + seed) % 17) - 8
    let c : Rat := mkRat (if v == 0 then 3 else v) 1
    (-(Int.ofNat k : Rat), c)
  FastLC.ofTerms terms

/-- Sparse rational-exponent series for sparse multiplication benchmarks. -/
private def makeBenchSparse (n : Nat) (seed : Int) : FastLC :=
  let terms : TermList := (List.range n).map fun k =>
    let expNum : Int := Int.ofNat (n * 4) - Int.ofNat (k * k + 3 * k)
    let expDen : Nat := (k % 5) + 1
    let v : Int := ((Int.ofNat k * 11 + seed) % 13) - 6
    let c : Rat := mkRat (if v == 0 then 2 else v) 1
    (mkRat expNum expDen, c)
  FastLC.ofTerms terms

@[noinline] private def runMulNaive (a b : LeviCivitaNum) : Int :=
  let p := LeviCivitaNum.mulNaive a b
  p.std.num + Int.ofNat p.infinitesimal.coeffs.size

@[noinline] private def runMulSparse (a b : FastLC) : Int :=
  let p := FastLC.mulSparse a b
  (p.coeff 0).num + Int.ofNat p.terms.length

@[noinline] private def runMulFast (a b : FastLC) : Int :=
  let p := a * b
  (p.coeff 0).num + Int.ofNat p.terms.length

@[noinline] private def runSignumNaive (a : LeviCivitaNum) : Int := a.signum
@[noinline] private def runSignumFast (a : FastLC) : Int := a.signum

@[noinline] private def runPowNaive (a : LeviCivitaNum) (k : Nat) : Int :=
  let p := LeviCivitaNum.powNaive a k
  p.std.num + Int.ofNat p.infinitesimal.coeffs.size

@[noinline] private def runPowFast (a : FastLC) (k : Nat) : Int :=
  let p := a.powFast k
  (p.coeff 0).num + Int.ofNat p.terms.length

@[noinline] private def runInvNaive (a : LeviCivitaNum) (ord : Nat) : Int :=
  let p := LeviCivitaNum.invOrder a ord
  p.std.num + Int.ofNat p.infinitesimal.coeffs.size

@[noinline] private def runInvFast (a : FastLC) (ord : Nat) : Int :=
  match FastLC.invNewton a ord with
  | .ok p => (p.coeff 0).num + Int.ofNat p.terms.length
  | .error _ => 0

/-- Run all head-to-head Naive vs Verified FastLC benchmarks with distinct prebuilt inputs
    per slot so nothing can be hoisted or CSE'd across iterations. -/
def runAllBenchmarks : IO (Array BenchRow) := do
  let mut rows : Array BenchRow := #[]
  let mut globalChecksum : Int := 0
  let poolSize : Nat := 8

  -- 1. Dense multiplication: HashMap mulNaive vs mulSparse (mulTree) vs FastLC.mul (Karatsuba)
  for (n, iters) in [(8, 80), (16, 40), (32, 24), (64, 12), (128, 6), (256, 3), (512, 2)] do
    let poolF : Array (FastLC × FastLC) :=
      (Array.range poolSize).map fun i =>
        (makeBenchDense n (Int.ofNat i * 3 + 1), makeBenchDense n (Int.ofNat i * 5 + 7))
    let poolN : Array (LeviCivitaNum × LeviCivitaNum) :=
      poolF.map fun (a, b) => (a.toLeviCivitaNum, b.toLeviCivitaNum)
    let (a0, b0) := poolF[0]!
    let (an0, bn0) := poolN[0]!
    let prodCheck := (a0 * b0) == FastLC.ofLeviCivitaNum (LeviCivitaNum.mulNaive an0 bn0)
    let (naiveUs, c1) ← timeItersUs iters fun i =>
      let (a, b) := poolN[i % poolSize]!
      runMulNaive a b
    let (sparseUs, c2) ← timeItersUs iters fun i =>
      let (a, b) := poolF[i % poolSize]!
      runMulSparse a b
    let (fastUs, c3) ← timeItersUs iters fun i =>
      let (a, b) := poolF[i % poolSize]!
      runMulFast a b
    globalChecksum := globalChecksum + c1 + c2 + c3
    rows := rows.push {
      category := "mul_dense"
      size := n
      iters
      naiveUs
      sparseUs := some sparseUs
      fastUs
      speedup := if fastUs > 0.0 then naiveUs / fastUs else 0.0
      verified := prodCheck
    }

  -- 2. Sparse rational-exponent multiplication: HashMap mulNaive vs verified mulTree
  for (n, iters) in [(16, 40), (32, 16), (64, 8)] do
    let poolF : Array (FastLC × FastLC) :=
      (Array.range poolSize).map fun i =>
        (makeBenchSparse n (Int.ofNat i * 2 + 1), makeBenchSparse n (Int.ofNat i * 3 + 5))
    let poolN : Array (LeviCivitaNum × LeviCivitaNum) :=
      poolF.map fun (a, b) => (a.toLeviCivitaNum, b.toLeviCivitaNum)
    let (a0, b0) := poolF[0]!
    let (an0, bn0) := poolN[0]!
    let prodCheck := (a0 * b0) == FastLC.ofLeviCivitaNum (LeviCivitaNum.mulNaive an0 bn0)
    let (naiveUs, c1) ← timeItersUs iters fun i =>
      let (a, b) := poolN[i % poolSize]!
      runMulNaive a b
    let (fastUs, c2) ← timeItersUs iters fun i =>
      let (a, b) := poolF[i % poolSize]!
      runMulFast a b
    globalChecksum := globalChecksum + c1 + c2
    rows := rows.push {
      category := "mul_sparse"
      size := n
      iters
      naiveUs
      fastUs
      speedup := if fastUs > 0.0 then naiveUs / fastUs else 0.0
      verified := prodCheck
    }

  -- 3. Signum: O(n log n) HashMap+qsort vs O(1) FastLC.signum
  for (n, iters) in [(32, 800), (128, 300), (256, 150)] do
    let poolF : Array FastLC := (Array.range poolSize).map fun i => makeBenchDense n (Int.ofNat i + 1)
    let poolN : Array LeviCivitaNum := poolF.map (·.toLeviCivitaNum)
    let ok := poolF[0]!.signum == poolN[0]!.signum
    let (naiveUs, c1) ← timeItersUs iters fun i => runSignumNaive (poolN[i % poolSize]!)
    let (fastUs, c2) ← timeItersUs iters fun i => runSignumFast (poolF[i % poolSize]!)
    globalChecksum := globalChecksum + c1 + c2
    rows := rows.push {
      category := "signum"
      size := n
      iters
      naiveUs
      fastUs
      speedup := if fastUs > 0.0 then naiveUs / fastUs else 0.0
      verified := ok
    }

  -- 4. Exponentiation: O(k) linear powNaive vs O(log k) verified powFast
  let powPoolF : Array FastLC := (Array.range poolSize).map fun i =>
    let s : Int := if i % 2 == 0 then 1 else -1
    FastLC.ofTerms [(1, 1), (0, mkRat (Int.ofNat (i % 3) + 1) 1), (-1, mkRat s 1)]
  let powPoolN : Array LeviCivitaNum := powPoolF.map (·.toLeviCivitaNum)
  for (k, iters) in [(16, 12), (32, 6), (48, 3)] do
    let ok := powPoolF[0]!.powFast k == powPoolF[0]!.powNaive k
    let (naiveUs, c1) ← timeItersUs iters fun i => runPowNaive (powPoolN[i % poolSize]!) k
    let (fastUs, c2) ← timeItersUs iters fun i => runPowFast (powPoolF[i % poolSize]!) k
    globalChecksum := globalChecksum + c1 + c2
    rows := rows.push {
      category := "pow"
      size := k
      iters
      naiveUs
      fastUs
      speedup := if fastUs > 0.0 then naiveUs / fastUs else 0.0
      verified := ok
    }

  -- 5. Inversion: O(N) geometric series vs O(log N) Newton-Raphson
  let invPoolF : Array FastLC := (Array.range poolSize).map fun i =>
    FastLC.ofTerms [(0, 1), (-1, mkRat (-(Int.ofNat (i % 3) + 1)) 1), (-2, 1)]
  let invPoolN : Array LeviCivitaNum := invPoolF.map (·.toLeviCivitaNum)
  for (ord, iters) in [(12, 24), (24, 8), (40, 4)] do
    let a0 := invPoolF[0]!
    let invN := FastLC.ofLeviCivitaNum (LeviCivitaNum.invOrder invPoolN[0]! ord)
    let invF := match FastLC.invNewton a0 ord with | .ok v => v | .error _ => 0
    -- Verify both are true inverses modulo O(ε^ord) and agree through ε^(ord - 1)
    let minExp : Rat := -((ord - 1 : Nat) : Rat)
    let ok := ((a0 * invF) - 1).dropBelow minExp == 0 &&
              invF.dropBelow minExp == invN.dropBelow minExp
    let (naiveUs, c1) ← timeItersUs iters fun i => runInvNaive (invPoolN[i % poolSize]!) ord
    let (fastUs, c2) ← timeItersUs iters fun i => runInvFast (invPoolF[i % poolSize]!) ord
    globalChecksum := globalChecksum + c1 + c2
    rows := rows.push {
      category := "inv"
      size := ord
      iters
      naiveUs
      fastUs
      speedup := if fastUs > 0.0 then naiveUs / fastUs else 0.0
      verified := ok
    }

  -- Ensure globalChecksum is observable so no timed computation is dead-code eliminated
  if globalChecksum == 999999999999999 then
    IO.eprintln s!"checksum={globalChecksum}"
  return rows

private def fmt1 (x : Float) : String :=
  let r := (x * 10.0).round / 10.0
  s!"{r}"

/-- Render benchmark results as JSON for plotting and web app display. -/
def rowsToJson (rows : Array BenchRow) : String :=
  let items := rows.toList.map fun row =>
    let spJson := match row.sparseUs with | some v => s!"{v}" | none => "null"
    "{" ++
    s!"\"category\":\"{row.category}\"," ++
    s!"\"size\":{row.size}," ++
    s!"\"iters\":{row.iters}," ++
    s!"\"naive_us\":{row.naiveUs}," ++
    s!"\"sparse_us\":{spJson}," ++
    s!"\"fast_us\":{row.fastUs}," ++
    s!"\"speedup\":{row.speedup}," ++
    s!"\"verified\":{if row.verified then "true" else "false"}" ++
    "}"
  "{\"benchmarks\":[" ++ String.intercalate "," items ++ "]}"

/-- Print a clean human-readable benchmark report. -/
def runAndPrint (asJson : Bool := false) : IO Unit := do
  let rows ← runAllBenchmarks
  if asJson then
    IO.println (rowsToJson rows)
  else
    IO.println "=== lean-inf Verified Refactor Benchmarks (Original Naive HashMap vs Verified FastLC) ==="
    IO.println "Category     | Size | Naive (us) | SparseTree (us) | FastLC (us) | Speedup | Verified"
    IO.println "-------------|------|------------|-----------------|-------------|---------|---------"
    for row in rows do
      let spStr := match row.sparseUs with | some v => fmt1 v | none => "-"
      let vStr := if row.verified then "PASS" else "FAIL"
      IO.println s!"{row.category} | {row.size} | {fmt1 row.naiveUs} | {spStr} | {fmt1 row.fastUs} | {fmt1 row.speedup}x | {vStr}"

end LeanInf.Bench
