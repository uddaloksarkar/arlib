/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# KR probability additions

Aggregate entry point for the measure-theoretic probability modules merged from
`kr-25-ssm`. It is separate from the upstream finite/discrete probability
aggregate so downstream projects can select the compatible dependency graph.
-/

import Arlib.Probability.TV
import Arlib.Probability.Rejection
import Arlib.Probability.SubgaussianTail
import Arlib.Probability.UniformOn
import Arlib.Probability.RunPlumbing
import Arlib.Probability.Geometric
import Arlib.Probability.RejectionRounds
import Arlib.Probability.TVTensor
import Arlib.Probability.TVKernel
import Arlib.Probability.DeltaIndependence
import Arlib.Probability.DependenceCovariance
import Arlib.Probability.InhomogeneousMarkov
import Arlib.Probability.AccuracyRecursion
import Arlib.Probability.AccuracySecondMoment
import Arlib.Probability.AccuracyLowerRecursion
import Arlib.Probability.TVKernelHeterogeneous
import Arlib.Probability.TVTimeout
import Arlib.Probability.AdaptiveTVTelescope
import Arlib.Probability.AdaptiveTVTelescopeMixture
import Arlib.Probability.NuIndepTensor
