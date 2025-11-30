-- This module serves as the root of the `LeanInf` library.
-- Import modules here that should be built as part of the library.
import LeanInf.Basic
import LeanInf.CoeffLike
-- import LeanInf.SignLemmas -- proofs deferred
import LeanInf.PolyGeneric
-- import LeanInf.LCBuilders   -- proofs deferred; keep out of root build
-- import LeanInf.Expect       -- demo/checks; keep out of root build
import LeanInf.WF
-- import LeanInf.LCGeneric -- generic LC structure WIP

namespace LeanInf

abbrev Polynomial := PolynomialG Rat

end LeanInf
