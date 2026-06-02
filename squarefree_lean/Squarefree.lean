-- Root aggregator for the Squarefree formalization (attempt 2, clean-room).
-- See ../formalization_plan.md §2 for the module DAG and ../CLAUDE.md for working rules.

-- L0 Foundation
import Squarefree.Asymp
import Squarefree.Params
import Squarefree.Budget
import Squarefree.FiniteDiff

-- L1 Analytic engine
import Squarefree.Counting.PopularDiff
import Squarefree.Counting.Preimage

-- §3 structural layer and §2 short-Δ regime (Prop 2.4)
import Squarefree.Structure.DaSpacing
import Squarefree.ShortDelta

-- §7 bracket layer
import Squarefree.Bracket.Admissible
import Squarefree.Bracket.BoxSum

-- §5/§6 lower- and upper-bound inputs
import Squarefree.Lower.Prop51
import Squarefree.Upper.Regime

-- §8/§9 optimization layer
import Squarefree.Opt.Strip
import Squarefree.Opt.Global

-- Top of proof spine
import Squarefree.Main
