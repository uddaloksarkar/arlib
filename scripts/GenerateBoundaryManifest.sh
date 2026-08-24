#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

classify() {
  local path="$1"
  case "$path" in
    Arlib/Algorithms.lean|Arlib/Algorithms/*)
      printf 'community\tnamed algorithm\n' ;;
    Arlib/Approximation/MulError.lean)
      printf 'core\tgeneric approximation relation\n' ;;
    Arlib/Approximation/Coresets/Basic.lean|\
    Arlib/Approximation/Coresets/Embedding.lean|\
    Arlib/Approximation/Coresets/Linear.lean|\
    Arlib/Approximation/Coresets/RegionTree.lean|\
    Arlib/Approximation/Coresets/Tensor.lean)
      printf 'core\treusable weighted-set and embedding infrastructure\n' ;;
    Arlib/Approximation.lean)
      printf 'core\tcore area root\n' ;;
    Arlib/Approximation/*)
      printf 'community\talgorithm, reduction, coreset, or sampling analysis\n' ;;
    Arlib/Automata/Basic.lean|Arlib/Automata/TreeAutomaton.lean)
      printf 'core\treusable representation and semantics\n' ;;
    Arlib/Automata.lean)
      printf 'core\tcore area root\n' ;;
    Arlib/Automata/*)
      printf 'community\ttransformation, procedure, or state lower bound\n' ;;
    Arlib/Communication/BooleanFunction.lean|Arlib/Communication/Rectangle.lean)
      printf 'core\treusable communication representation\n' ;;
    Arlib/Communication.lean)
      printf 'core\tcore area root\n' ;;
    Arlib/Communication/*)
      printf 'community\tlower-bound method or gadget application\n' ;;
    Arlib/InformationTheory/QueryLowerBound.lean)
      printf 'community\tquery lower-bound application\n' ;;
    Arlib/InformationTheory.lean|Arlib/InformationTheory/*)
      printf 'core\tgeneric information theory\n' ;;
    Arlib/KnowledgeCompilation/Circuits/Arithmetic.lean|\
    Arlib/KnowledgeCompilation/Circuits/DNF.lean|\
    Arlib/KnowledgeCompilation/Circuits/NNF.lean|\
    Arlib/KnowledgeCompilation/Circuits/SDD.lean|\
    Arlib/KnowledgeCompilation/Circuits/VTree.lean|\
    Arlib/KnowledgeCompilation/Probabilistic/CircuitPair.lean|\
    Arlib/KnowledgeCompilation/Probabilistic/StructuredCircuit.lean)
      printf 'core\treusable circuit representation and semantics\n' ;;
    Arlib/KnowledgeCompilation.lean)
      printf 'core\tcore area root\n' ;;
    Arlib/KnowledgeCompilation/*)
      printf 'community\tcompilation, transformation, or representation lower bound\n' ;;
    Arlib/MDP/Basic.lean)
      printf 'core\treusable MDP representation\n' ;;
    Arlib/MDP.lean)
      printf 'core\tcore area root\n' ;;
    Arlib/MDP/*)
      printf 'community\tMDP algorithm and convergence analysis\n' ;;
    Arlib/MarkovChains/Techniques/Adjoint.lean|\
    Arlib/MarkovChains/Techniques/Comparison.lean|\
    Arlib/MarkovChains/Techniques/Conductance.lean|\
    Arlib/MarkovChains/Techniques/Dirichlet.lean|\
    Arlib/MarkovChains/Techniques/Entropy.lean|\
    Arlib/MarkovChains/Techniques/EntropyDecay.lean|\
    Arlib/MarkovChains/Techniques/EntropyMixing.lean|\
    Arlib/MarkovChains/Techniques/EntropyVariational.lean|\
    Arlib/MarkovChains/Techniques/Lazy.lean|\
    Arlib/MarkovChains/Techniques/MixingTime.lean|\
    Arlib/MarkovChains/Techniques/Mixture.lean|\
    Arlib/MarkovChains/Techniques/Pinsker.lean|\
    Arlib/MarkovChains/Techniques/PsdOrder.lean|\
    Arlib/MarkovChains/Techniques/SpectralGap.lean|\
    Arlib/MarkovChains/Techniques/TotalVariation.lean|\
    Arlib/MarkovChains/Techniques/Transport.lean|\
    Arlib/MarkovChains/Continuous/Cheeger.lean|\
    Arlib/MarkovChains/Continuous/Conductance.lean|\
    Arlib/MarkovChains/Continuous/L2Mixing.lean|\
    Arlib/MarkovChains/Continuous/MixingFromConductance.lean|\
    Arlib/MarkovChains/Continuous/PointwiseMixing.lean|\
    Arlib/MarkovChains/Continuous/Warmness.lean)
      printf 'core\tgeneric Markov-chain theory\n' ;;
    Arlib/MarkovChains.lean)
      printf 'core\tcore area root\n' ;;
    Arlib/MarkovChains/*)
      printf 'community\tconcrete chain or specialized analysis\n' ;;
    Arlib/Probability/ContCoinProto.lean|\
    Arlib/Probability/EmpiricalFrequency.lean|\
    Arlib/Probability/FailureAmplification.lean|\
    Arlib/Probability/FirstBad.lean|\
    Arlib/Probability/InverseCDF.lean|\
    Arlib/Probability/Median.lean|\
    Arlib/Probability/MixedCoinSpace.lean|\
    Arlib/Probability/MixedCondCELinear.lean|\
    Arlib/Probability/MixedCondProd.lean|\
    Arlib/Probability/MixedCoordIndep.lean|\
    Arlib/Probability/MixedRunProduct.lean|\
    Arlib/Probability/PoissonSplitting.lean|\
    Arlib/Probability/PolyHash.lean|\
    Arlib/Probability/Reduce.lean|\
    Arlib/Probability/RobbinsMonro.lean|\
    Arlib/Probability/RunProduct.lean|\
    Arlib/Probability/SequentialDominate.lean|\
    Arlib/Probability/StochasticApproximation.lean|\
    Arlib/Probability/UniformCoin.lean)
      printf 'community\trandomized procedure or procedure-specific analysis\n' ;;
    Arlib/Probability/DeltaIndependence.lean|\
    Arlib/Probability/DependenceCovariance.lean|\
    Arlib/Probability/NuIndepTensor.lean)
      printf 'community\tGaussian-cooling dependence analysis\n' ;;
    Arlib/Probability.lean|Arlib/Probability/*)
      printf 'core\tgeneric probability foundation\n' ;;
    Arlib/Convexity/GaussianCooling/Estimator.lean|\
    Arlib/Convexity/HitAndRunStep.lean|\
    Arlib/Convexity/StepLength.lean)
      printf 'community\twalk or estimator analysis\n' ;;
    Arlib/Convexity/*)
      printf 'core\tgeneric convex geometry\n' ;;
    Arlib/Lattice/KV97/Defs.lean)
      printf 'core\treusable lattice representation\n' ;;
    Arlib/Lattice/*)
      printf 'community\trounding procedure or KV97 analysis\n' ;;
    Arlib/GameTheory.lean|Arlib/GameTheory/*)
      printf 'core\tgeneric minimax theory\n' ;;
    Arlib/Prelude.lean|Arlib/Combinatorics.lean|Arlib/Combinatorics/*)
      printf 'core\tgeneric shared foundation\n' ;;
    *)
      printf 'unclassified\trequires review\n' ;;
  esac
}

printf 'module\towner\treason\n'
while IFS= read -r path; do
  printf '%s\t' "$path"
  classify "$path"
done < <(find Arlib -type f -name '*.lean' | sort)
