# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BinarySequenceWeight | definition | definition | closed | - | - | Preamble |
| BinarySequenceWeightFiberCard | helper | proof | closed | - | - | BinarySequenceWeight |
| BinarySequenceWeightSnoc | helper | proof | closed | - | - | BinarySequenceWeight |
| CloseToDiagonalExponentComparison | helper | proof | closed | - | - | Preamble |
| CloseToDiagonalLossFactorChoice | helper | proof | closed | - | - | Preamble |
| CloseToDiagonalPositiveSamplingLowerBound | helper | proof | closed | - | - | CloseToDiagonalExponentComparison |
| CloseToDiagonalSamplingAlgebra | helper | proof | closed | - | - | Preamble |
| CloseToDiagonalTargetScaleLarge | helper | proof | closed | - | - | Preamble |
| CloseToDiagonalTheorem | theorem | proof | closed | - | - | CloseToDiagonalExponentComparison, CloseToDiagonalLossFactorChoice, CloseToDiagonalPositiveSamplingLowerBound, CloseToDiagonalSamplingAlgebra, CloseToDiagonalTargetScaleLarge, CloseToDiagonalVertexCountLowerBound, CloseToDiagonalZeroCountLowerBound, DigraphToGraphIndependentSetBound, F2ForwardIndependentNearDiagonalBound, SamplingKsFreeRamseyBound, SimpleGraphNoIndependentSetFromCountZero |
| CloseToDiagonalVertexCountLowerBound | helper | proof | closed | - | - | Preamble |
| CloseToDiagonalZeroCountLowerBound | helper | proof | closed | - | - | CloseToDiagonalVertexCountLowerBound |
| ComplementPolarityPairHsFree | lemma | proof | closed | - | - | HsFreePair, LoopGraphComplement, PolarityGraphSkewFree |
| Digraph | definition | definition | closed | - | - | Preamble |
| DigraphLoopless | definition | definition | closed | - | - | Digraph |
| DigraphOrderedGraph | definition | definition | closed | - | - | Digraph |
| DigraphOrderedGraphCliqueFree | helper | proof | closed | - | - | DigraphOrderedGraph, TransitiveTournamentFree |
| DigraphOrderedGraphIndependentSetBound | helper | proof | closed | - | - | DigraphOrderedGraph, DigraphOrderedGraphIndependentSetFactorialBound, DigraphOrderedGraphIndependentSetToForwardTuple, ForwardIndependentTupleCount, SimpleGraphIndependentSetCount, TupleIncreasingPermutationFiberCount |
| DigraphOrderedGraphIndependentSetFactorialBound | helper | proof | closed | - | - | DigraphOrderedGraph, ForwardIndependentTupleCount, SimpleGraphIndependentSetCount, TupleIncreasingPermutationFiberCount |
| DigraphOrderedGraphIndependentSetToForwardTuple | helper | proof | closed | - | - | DigraphOrderedGraph, ForwardIndependentTuple |
| DigraphToGraphIndependentSetBound | lemma | proof | closed | - | - | DigraphOrderedGraphCliqueFree, DigraphOrderedGraphIndependentSetBound |
| ExpanderMixingLemma | lemma | proof | closed | - | - | FinsetCenteredIndicatorNormSqLeCard, FinsetCenteredIndicatorSumZero, LoopGraphEdgeCountBetween, LoopGraphEdgeCountBetweenAdjacencyIndicator, LoopGraphNdLambda, LoopGraphNdLambdaAdjacencyIndicatorSum, LoopGraphNdLambdaAdjacencyOne, LoopGraphZeroSumAdjacencyBilinearBound |
| F2BadTuple | definition | definition | closed | - | - | Preamble |
| F2BadTupleAmbientStepProductBound | helper | proof | closed | - | - | F2BadTuplePrefixFiberBound |
| F2BadTupleCountBoundNat | helper | proof | closed | - | - | F2BadTupleFinalRankFiberBound, F2BadTupleRankIncreaseSetCard |
| F2BadTupleFinalRankFiberBound | helper | proof | closed | - | - | BinarySequenceWeightFiberCard, F2BadTupleFixedIncreaseCount, F2BadTupleFixedIncreaseCountBound, F2BadTupleRankIncreaseSetCard |
| F2BadTupleFixedIncreaseCount | definition | definition | closed | - | - | BinarySequenceWeight, F2BadTupleRank |
| F2BadTupleFixedIncreaseCountBound | helper | proof | closed | - | - | F2BadTupleFixedIncreaseFalseExponentBound, F2BadTupleFixedIncreaseFalseLastBound, F2BadTupleFixedIncreaseTrueExponentBound, F2BadTupleFixedIncreaseTrueLastBound |
| F2BadTupleFixedIncreaseFalseExponentBound | helper | proof | closed | - | - | Preamble |
| F2BadTupleFixedIncreaseFalseLastBound | helper | proof | closed | - | - | BinarySequenceWeightSnoc, F2BadTupleFixedIncreasePrefixRestriction, F2BadTupleLastPairSpanFiberBound, F2BadTupleRankIncreaseSetCard, F2BadTupleRankSnocPrefixLast, F2BadTupleRankZero |
| F2BadTupleFixedIncreasePrefixRestriction | helper | proof | closed | - | - | F2BadTupleFixedIncreaseCount, F2BadTuplePrefixRestriction, F2BadTupleRankPrefixRestriction |
| F2BadTupleFixedIncreaseTrueExponentBound | helper | proof | closed | - | - | F2BadTupleFixedIncreaseFalseExponentBound |
| F2BadTupleFixedIncreaseTrueLastBound | helper | proof | closed | - | - | F2BadTupleFixedIncreasePrefixRestriction, F2BadTupleLastPairAmbientFiberBound, F2BadTupleRankIncreaseSetCard, F2BadTupleRankSnocPrefixLast |
| F2BadTupleLastBChoicesBound | helper | proof | closed | - | - | F2BadTuplePrefixFiberBound |
| F2BadTupleLastPairAmbientFiberBound | helper | proof | closed | - | - | F2BadTupleLastBChoicesBound |
| F2BadTupleLastPairSpanFiberBound | helper | proof | closed | - | - | F2BadTupleLastBChoicesBound, F2BadTupleNonincreaseStepProductBound, F2BadTuplePrefixSpanCard, F2BadTupleRankPrefixRestriction |
| F2BadTupleNonincreaseStepProductBound | helper | proof | closed | - | - | F2BadTuplePrefixFiberBound, F2BadTuplePrefixSpanCard, F2BadTupleRankStep |
| F2BadTuplePrefixFiberBound | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTuplePrefixRestriction | helper | proof | closed | - | - | F2BadTuple |
| F2BadTuplePrefixSpanCard | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTupleRank | definition | definition | closed | - | - | F2BadTuple |
| F2BadTupleRankAmbientBound | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTupleRankIncreaseSet | definition | definition | closed | - | - | F2BadTupleRank |
| F2BadTupleRankIncreaseSetCard | helper | proof | closed | - | - | F2BadTupleRankAmbientBound, F2BadTupleRankIncreaseSet, F2BadTupleRankOne, F2BadTupleRankStep, F2BadTupleRankZero |
| F2BadTupleRankOne | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTupleRankPrefixRestriction | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTupleRankSnocPrefixLast | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTupleRankStep | helper | proof | closed | - | - | F2BadTupleRank |
| F2BadTupleRankZero | helper | proof | closed | - | - | F2BadTupleRank |
| F2CoordinateDigraphLoopless | helper | proof | closed | - | - | DigraphLoopless |
| F2CoordinateDigraphTransitiveFree | helper | proof | closed | - | - | TransitiveTournamentFree |
| F2DotOnePairCard | helper | proof | closed | - | - | Preamble |
| F2DotOnePairEmbedding | helper | proof | closed | - | - | F2DotOnePairCard |
| F2ForwardIndependentLinearBound | lemma | proof | closed | - | - | F2ForwardIndependentSumBound, F2ForwardIndependentTuples |
| F2ForwardIndependentNearDiagonalBound | lemma | proof | closed | - | - | F2ForwardIndependentTuples, F2NearDiagonalChooseSymmetry, F2NearDiagonalExponentIdentity, F2NearDiagonalLargeSPowerBound, F2NearDiagonalLogControlBundle, F2NearDiagonalQuadraticMaxBound, F2NearDiagonalSummandFromLogControls, F2NearDiagonalSummationAbsorptionBound |
| F2ForwardIndependentSumBound | helper | proof | closed | - | - | Preamble |
| F2ForwardIndependentTuples | lemma | proof | closed | - | - | BinarySequenceWeightFiberCard, DigraphLoopless, F2BadTuple, F2BadTupleAmbientStepProductBound, F2BadTupleCountBoundNat, F2BadTupleFinalRankFiberBound, F2BadTupleFixedIncreaseCount, F2BadTupleFixedIncreaseCountBound, F2BadTupleFixedIncreaseFalseLastBound, F2BadTupleFixedIncreasePrefixRestriction, F2BadTupleFixedIncreaseTrueLastBound, F2BadTupleLastPairAmbientFiberBound, F2BadTupleLastPairSpanFiberBound, F2BadTupleNonincreaseStepProductBound, F2BadTuplePrefixFiberBound, F2BadTuplePrefixSpanCard, F2BadTupleRankAmbientBound, F2BadTupleRankIncreaseSetCard, F2BadTupleRankOne, F2BadTupleRankStep, F2BadTupleRankZero, F2CoordinateDigraphLoopless, F2CoordinateDigraphTransitiveFree, F2DotOnePairEmbedding, ForwardIndependentTupleCount, TransitiveTournamentFree |
| F2NearDiagonalBinomialLogBound | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalChooseSymmetry | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalExponentIdentity | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalLargeSPowerBound | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalLogControlBundle | helper | proof | closed | - | - | F2NearDiagonalBinomialLogBound, F2NearDiagonalChooseSymmetry, F2NearDiagonalLogSquareBound, F2NearDiagonalQuadraticMaxBound, F2NearDiagonalSmallXLogBound |
| F2NearDiagonalLogSquareBound | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalQuadraticMaxBound | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalSmallXLogBound | helper | proof | closed | - | - | Preamble |
| F2NearDiagonalSummandFromLogControls | helper | proof | closed | - | - | F2NearDiagonalExponentIdentity |
| F2NearDiagonalSummationAbsorptionBound | helper | proof | closed | - | - | Preamble |
| FinsetCenteredIndicatorNormSqLeCard | helper | proof | closed | - | - | Preamble |
| FinsetCenteredIndicatorSumZero | helper | proof | closed | - | - | Preamble |
| ForwardIndependentTuple | definition | definition | closed | - | - | Digraph |
| ForwardIndependentTupleCount | definition | definition | closed | - | - | ForwardIndependentTuple |
| HsFreePair | definition | definition | closed | - | - | LoopGraph |
| LinearOffDiagonalTheorem | theorem | proof | open | - | - | DigraphToGraphIndependentSetBound, F2ForwardIndependentLinearBound, SamplingKsFreeRamseyBound |
| LoopGraph | definition | definition | closed | - | - | Preamble |
| LoopGraphAdjacencyAction | definition | definition | closed | - | - | LoopGraph |
| LoopGraphAdjacencyActionSelfAdjoint | helper | proof | closed | - | - | LoopGraphAdjacencyAction, LoopGraphSymmetric |
| LoopGraphAdjacencyEuclideanInner | helper | proof | closed | - | - | LoopGraphAdjacencyEuclideanOperator |
| LoopGraphAdjacencyEuclideanOperator | definition | definition | closed | - | - | LoopGraphAdjacencyAction |
| LoopGraphAdjacencyEuclideanOperatorMapsZeroSum | helper | proof | closed | - | - | LoopGraphEuclideanZeroSumSubmodule, LoopGraphNdLambdaAdjacencyActionZeroSum |
| LoopGraphAdjacencyEuclideanOperatorSymmetric | helper | proof | closed | - | - | LoopGraphAdjacencyActionSelfAdjoint, LoopGraphAdjacencyEuclideanInner |
| LoopGraphComplement | definition | definition | closed | - | - | LoopGraph |
| LoopGraphDegree | definition | definition | closed | - | - | LoopGraph |
| LoopGraphEdgeCountBetween | definition | definition | closed | - | - | LoopGraph |
| LoopGraphEdgeCountBetweenAdjacencyIndicator | helper | proof | closed | - | - | LoopGraphAdjacencyAction, LoopGraphEdgeCountBetween |
| LoopGraphEuclideanZeroSumSubmodule | definition | definition | closed | - | - | LoopGraphAdjacencyEuclideanOperator |
| LoopGraphNdLambda | definition | definition | closed | - | - | LoopGraphDegree, LoopGraphNonprincipalEigenvalue, LoopGraphSymmetric |
| LoopGraphNdLambdaAdjacencyActionZeroSum | helper | proof | closed | - | - | LoopGraphAdjacencyActionSelfAdjoint, LoopGraphNdLambdaAdjacencyOne |
| LoopGraphNdLambdaAdjacencyIndicatorSum | helper | proof | closed | - | - | LoopGraphNdLambda |
| LoopGraphNdLambdaAdjacencyOne | helper | proof | closed | - | - | LoopGraphAdjacencyAction, LoopGraphNdLambda |
| LoopGraphNonprincipalEigenvalue | definition | definition | closed | - | - | LoopGraphAdjacencyAction |
| LoopGraphSymmetric | definition | definition | closed | - | - | LoopGraph |
| LoopGraphZeroSumAdjacencyBilinearBound | helper | proof | closed | - | - | LoopGraphAdjacencyActionSelfAdjoint, LoopGraphAdjacencyEuclideanInner, LoopGraphAdjacencyEuclideanOperatorSymmetric, LoopGraphNdLambda, LoopGraphNdLambdaAdjacencyActionZeroSum, LoopGraphZeroSumAdjacencyEuclideanOperator, LoopGraphZeroSumEuclideanEigenvalueBound |
| LoopGraphZeroSumAdjacencyEuclideanOperator | definition | definition | closed | - | - | LoopGraphAdjacencyEuclideanOperatorMapsZeroSum, LoopGraphEuclideanZeroSumSubmodule, LoopGraphNdLambda |
| LoopGraphZeroSumEuclideanEigenpairNonprincipal | helper | proof | closed | - | - | LoopGraphEuclideanZeroSumSubmodule, LoopGraphNonprincipalEigenvalue |
| LoopGraphZeroSumEuclideanEigenvalueBound | helper | proof | closed | - | - | LoopGraphNdLambda, LoopGraphZeroSumEuclideanEigenpairNonprincipal |
| MainTheorem | theorem | proof | open | - | - | ComplementPolarityPairHsFree, PolarityGraphParameters, RamseyFromGraphPair |
| MulticolorRamseyNumber | definition | definition | closed | - | - | MulticolorRamseyProperty |
| MulticolorRamseyProperty | definition | definition | closed | - | - | Preamble |
| MulticolorTheorem | theorem | proof | open | - | - | MulticolorRamseyNumber, RandomHomomorphismColoringBound |
| NoMonochromaticCliqueColoring | definition | definition | closed | - | - | Preamble |
| NoSkewBipartiteConfiguration | definition | definition | closed | - | - | LoopGraph |
| OffDiagonalGeneralTheorem | theorem | proof | open | - | - | ComplementPolarityPairHsFree, PolarityGraphParameters, RamseyFromGraphPair |
| PolarityGraph | definition | definition | closed | - | - | LoopGraph |
| PolarityGraphParameters | lemma | proof | closed | - | - | LoopGraphNdLambda, PolarityGraph |
| PolarityGraphSkewFree | lemma | proof | closed | - | - | NoSkewBipartiteConfiguration, PolarityGraph |
| Preamble | preamble | preamble | closed | - | - | - |
| ProductDigraph | definition | definition | closed | - | - | Digraph, ProductDigraphVertex |
| ProductDigraphFixedSequenceTupleCount | definition | definition | closed | - | - | ProductDigraphTupleHasShrinkingSequence |
| ProductDigraphFixedSequenceTupleCountLastVertexBound | helper | proof | closed | - | - | ProductDigraphFixedSequenceTupleCount, ProductDigraphVertexCard |
| ProductDigraphFixedSequenceTupleCountZeroBitBound | helper | proof | closed | - | - | ProductDigraphFixedSequenceTupleCount, ProductDigraphSparseEdgeChoiceBound |
| ProductDigraphForwardIndependentBound | lemma | proof | closed | - | - | ForwardIndependentTupleCount, HsFreePair, LoopGraphDegree, ProductDigraph, ProductDigraphShrinkingSequenceBound, ProductDigraphTransitiveFree, ProductDigraphTupleHasShrinkingSequence, ProductDigraphVertex, ProductDigraphVertexCard, TransitiveTournamentFree |
| ProductDigraphShrinkingSequenceBound | lemma | proof | closed | - | - | BinarySequenceWeight, BinarySequenceWeightSnoc, ProductDigraphFixedSequenceTupleCount, ProductDigraphFixedSequenceTupleCountLastVertexBound, ProductDigraphFixedSequenceTupleCountZeroBitBound, ProductDigraphSparseEdgeChoiceBound, ProductDigraphVertexCard, SparseNeighborhoodSetBound |
| ProductDigraphSparseEdgeChoiceBound | helper | proof | closed | - | - | SparseNeighborhoodSetBound |
| ProductDigraphTransitiveFree | lemma | proof | closed | - | - | HsFreePair, ProductDigraph, TransitiveTournamentFree |
| ProductDigraphTupleHasShrinkingSequence | definition | definition | closed | - | - | ForwardIndependentTuple, LoopGraphEdgeCountBetween, ProductDigraph |
| ProductDigraphVertex | definition | definition | closed | - | - | LoopGraph |
| ProductDigraphVertexCard | helper | proof | closed | - | - | LoopGraphNdLambda, ProductDigraphVertex |
| RamseyFromGraphPair | theorem | proof | closed | - | - | DigraphToGraphIndependentSetBound, ProductDigraphForwardIndependentBound, SamplingKsFreeRamseyBound |
| RamseyNumber | definition | definition | closed | - | - | RamseyProperty |
| RamseyNumberLowerBoundFromCounterexample | helper | proof | closed | - | - | RamseyNumber, RamseyPropertyCounterexampleTransport, RamseyPropertyMonotone, RamseyPropertyNonempty |
| RamseyProperty | definition | definition | closed | - | - | Preamble |
| RamseyPropertyCounterexampleTransport | helper | proof | closed | - | - | RamseyProperty |
| RamseyPropertyMonotone | helper | proof | closed | - | - | RamseyProperty |
| RamseyPropertyNonempty | helper | proof | closed | - | - | RamseyPropertyStep |
| RamseyPropertyStep | helper | proof | closed | - | - | RamseyProperty |
| RandomHomomorphismColoringBound | lemma | proof | open | - | - | F2ForwardIndependentNearDiagonalBound, NoMonochromaticCliqueColoring |
| SamplingKsFreeRamseyBound | lemma | proof | closed | - | - | RamseyNumber, RamseyNumberLowerBoundFromCounterexample, RamseyPropertyCounterexampleTransport, RamseyPropertyMonotone, RamseyPropertyNonempty, SimpleGraphIndependentSetCount |
| SimpleGraphIndependentSetCount | definition | definition | closed | - | - | Preamble |
| SimpleGraphNoIndependentSetFromCountZero | helper | proof | closed | - | - | SimpleGraphIndependentSetCount |
| SparseNeighborhoodSetBound | lemma | proof | closed | - | - | ExpanderMixingLemma |
| TransitiveTournamentFree | definition | definition | closed | - | - | Digraph |
| TupleIncreasingPermutationFiberCount | helper | proof | closed | - | - | Preamble |

**Total:** 130 nodes | **Closed:** 125 | **Open:** 5
