import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Lp.PiLp

open Real

/-! B0: Mathlib Banach API verification scratch file.
All #check commands must compile with 0 errors.
-/

-- ContractingWith API
#check ContractingWith
#check LipschitzWith
#check ContractingWith.efixedPoint
#check ContractingWith.efixedPoint_isFixedPt
#check ContractingWith.fixedPoint
#check ContractingWith.fixedPoint_isFixedPt
#check ContractingWith.tendsto_iterate_efixedPoint
#check ContractingWith.apriori_edist_iterate_efixedPoint_le

-- CompleteSpace on Pi types
#check Pi.complete

-- NNReal contraction constant
#check (0.5 : NNReal)
