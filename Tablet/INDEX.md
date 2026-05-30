# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BinarySequenceWeight | definition | definition | closed | - | - | Preamble |
| BinarySequenceWeightSnoc | helper | proof | closed | - | - | BinarySequenceWeight |
| CloseToDiagonalTheorem | theorem | proof | open | - | - | DigraphToGraphIndependentSetBound, F2ForwardIndependentNearDiagonalBound, SamplingKsFreeRamseyBound |
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
| F2CoordinateDigraphLoopless | helper | proof | closed | - | - | DigraphLoopless |
| F2CoordinateDigraphTransitiveFree | helper | proof | closed | - | - | TransitiveTournamentFree |
| F2ForwardIndependentLinearBound | lemma | proof | open | - | - | F2ForwardIndependentTuples |
| F2ForwardIndependentNearDiagonalBound | lemma | proof | open | - | - | F2ForwardIndependentTuples |
| F2ForwardIndependentTuples | lemma | proof | open | - | - | DigraphLoopless, F2CoordinateDigraphLoopless, F2CoordinateDigraphTransitiveFree, ForwardIndependentTupleCount, TransitiveTournamentFree |
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
| SparseNeighborhoodSetBound | lemma | proof | closed | - | - | ExpanderMixingLemma |
| TransitiveTournamentFree | definition | definition | closed | - | - | Digraph |
| TupleIncreasingPermutationFiberCount | helper | proof | closed | - | - | Preamble |

**Total:** 81 nodes | **Closed:** 72 | **Open:** 9
