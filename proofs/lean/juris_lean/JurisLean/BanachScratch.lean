import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib

open Real

/-! B0: Mathlib Banach API verification scratch file.
All #check commands must compile with 0 errors.
-/

-- ContractingWith API
#check ContractingWith
#check LipschitzWith
#check efixedPoint
#check efixedPoint_isFixedPt
#check fixedPoint
#check fixedPoint_isFixedPt
#check tendsto_iterate_efixedPoint
#check apriori_edist_iterate_efixedPoint_le

-- CompleteSpace on Pi types
#check Pi.complete

-- NNReal contraction constant
#check (0.5 : NNReal)