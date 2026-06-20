-- Root aggregator for the Squarefree formalization (attempt 2, clean-room).
-- See ../formalization_plan.md §2 for the module DAG and ../CLAUDE.md for working rules.

-- L0 Foundation
import Squarefree.Asymp
import Squarefree.Params
import Squarefree.Budget
import Squarefree.FiniteDiff
import Squarefree.DCard

-- L1 Analytic engine
import Squarefree.Counting.PopularDiff
import Squarefree.Counting.Preimage
import Squarefree.Counting.FourthDeriv
import Squarefree.Counting.Bands
import Squarefree.Geometry.NearCurve
import Squarefree.Geometry.NearCurveAux
import Squarefree.Geometry.NearCurveSpacing
import Squarefree.Geometry.NearCurveProof
import Squarefree.Geometry.NearCurveResidual

-- §3 structural layer and §2 short-Δ regime (Prop 2.4)
import Squarefree.Structure.DaSpacing
import Squarefree.Structure.Fiber
import Squarefree.Structure.ADecomp
import Squarefree.Structure.NearCurveBridge
import Squarefree.Structure.PhaseDeriv
import Squarefree.Structure.FfunHighDeriv
import Squarefree.Structure.PhaseCurv
import Squarefree.ShortDelta

-- §7 bracket layer
import Squarefree.Bracket.Admissible
import Squarefree.Bracket.Sec7Defs
import Squarefree.Bracket.Sec7PhaseExp
import Squarefree.Bracket.Sec7MonExpBuild
import Squarefree.Bracket.Sec7ErrBound
import Squarefree.Bracket.Sec7PhiDeriv
import Squarefree.Bracket.Sec7ZeroScale
import Squarefree.Bracket.Sec7Cube
import Squarefree.Bracket.Sec7Branch
import Squarefree.Bracket.Sec7BoxSums
import Squarefree.Bracket.Sec7Nonzero
import Squarefree.Bracket.Sec7Harvest
import Squarefree.Bracket.BoxSum

-- §5/§6 lower- and upper-bound inputs
import Squarefree.Lower.Prop51
import Squarefree.Upper.Regime

-- §8/§9 optimization layer
import Squarefree.Opt.Strip
import Squarefree.Opt.Global

-- §1 dyadic assembly
import Squarefree.DyadicAssembly

-- Top of proof spine
import Squarefree.Main

-- Explicit/effective restatements (explicit constants + threshold)
import Squarefree.Explicit
