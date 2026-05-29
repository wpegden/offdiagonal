# Tablet Index

| Name | Env | Kind | Status | Labels | Title | Imports |
|------|-----|------|--------|--------|-------|---------|
| BinarySequenceWeight | definition | definition | closed | - | - | Preamble |
| CloseToDiagonalTheorem | theorem | proof | open | - | - | DigraphToGraphIndependentSetBound, F2ForwardIndependentNearDiagonalBound, SamplingKsFreeRamseyBound |
| ComplementPolarityPairHsFree | lemma | proof | closed | - | - | HsFreePair, LoopGraphComplement, PolarityGraphSkewFree |
| Digraph | definition | definition | closed | - | - | Preamble |
| DigraphLoopless | definition | definition | closed | - | - | Digraph |
| DigraphOrderedGraph | definition | definition | closed | - | - | Digraph |
| DigraphOrderedGraphCliqueFree | helper | proof | closed | - | - | DigraphOrderedGraph, TransitiveTournamentFree |
| DigraphOrderedGraphIndependentSetBound | helper | proof | open | - | - | DigraphOrderedGraph, ForwardIndependentTupleCount, SimpleGraphIndependentSetCount |
| DigraphToGraphIndependentSetBound | lemma | proof | closed | - | - | DigraphOrderedGraphCliqueFree, DigraphOrderedGraphIndependentSetBound |
| ExpanderMixingLemma | lemma | proof | open | - | - | LoopGraphEdgeCountBetween, LoopGraphNdLambda |
| F2ForwardIndependentLinearBound | lemma | proof | open | - | - | F2ForwardIndependentTuples |
| F2ForwardIndependentNearDiagonalBound | lemma | proof | open | - | - | F2ForwardIndependentTuples |
| F2ForwardIndependentTuples | lemma | proof | open | - | - | DigraphLoopless, ForwardIndependentTupleCount, TransitiveTournamentFree |
| ForwardIndependentTuple | definition | definition | closed | - | - | Digraph |
| ForwardIndependentTupleCount | definition | definition | closed | - | - | ForwardIndependentTuple |
| HsFreePair | definition | definition | closed | - | - | LoopGraph |
| LinearOffDiagonalTheorem | theorem | proof | open | - | - | DigraphToGraphIndependentSetBound, F2ForwardIndependentLinearBound, SamplingKsFreeRamseyBound |
| LoopGraph | definition | definition | closed | - | - | Preamble |
| LoopGraphAdjacencyAction | definition | definition | closed | - | - | LoopGraph |
| LoopGraphComplement | definition | definition | closed | - | - | LoopGraph |
| LoopGraphDegree | definition | definition | closed | - | - | LoopGraph |
| LoopGraphEdgeCountBetween | definition | definition | closed | - | - | LoopGraph |
| LoopGraphNdLambda | definition | definition | closed | - | - | LoopGraphDegree, LoopGraphNonprincipalEigenvalue, LoopGraphSymmetric |
| LoopGraphNonprincipalEigenvalue | definition | definition | closed | - | - | LoopGraphAdjacencyAction |
| LoopGraphSymmetric | definition | definition | closed | - | - | LoopGraph |
| MainTheorem | theorem | proof | open | - | - | ComplementPolarityPairHsFree, PolarityGraphParameters, RamseyFromGraphPair |
| MulticolorRamseyNumber | definition | definition | closed | - | - | MulticolorRamseyProperty |
| MulticolorRamseyProperty | definition | definition | closed | - | - | Preamble |
| MulticolorTheorem | theorem | proof | open | - | - | MulticolorRamseyNumber, RandomHomomorphismColoringBound |
| NoMonochromaticCliqueColoring | definition | definition | closed | - | - | Preamble |
| NoSkewBipartiteConfiguration | definition | definition | closed | - | - | LoopGraph |
| OffDiagonalGeneralTheorem | theorem | proof | open | - | - | ComplementPolarityPairHsFree, PolarityGraphParameters, RamseyFromGraphPair |
| PolarityGraph | definition | definition | closed | - | - | LoopGraph |
| PolarityGraphParameters | lemma | proof | open | - | - | LoopGraphNdLambda, PolarityGraph |
| PolarityGraphSkewFree | lemma | proof | open | - | - | NoSkewBipartiteConfiguration, PolarityGraph |
| Preamble | preamble | preamble | closed | - | - | - |
| ProductDigraph | definition | definition | closed | - | - | Digraph, ProductDigraphVertex |
| ProductDigraphFixedSequenceTupleCount | definition | definition | closed | - | - | ProductDigraphTupleHasShrinkingSequence |
| ProductDigraphForwardIndependentBound | lemma | proof | open | - | - | ForwardIndependentTupleCount, HsFreePair, ProductDigraph, ProductDigraphShrinkingSequenceBound, ProductDigraphTransitiveFree, ProductDigraphVertex, TransitiveTournamentFree |
| ProductDigraphShrinkingSequenceBound | lemma | proof | open | - | - | BinarySequenceWeight, ProductDigraphFixedSequenceTupleCount, SparseNeighborhoodSetBound |
| ProductDigraphTransitiveFree | lemma | proof | open | - | - | HsFreePair, ProductDigraph, TransitiveTournamentFree |
| ProductDigraphTupleHasShrinkingSequence | definition | definition | closed | - | - | ForwardIndependentTuple, LoopGraphEdgeCountBetween, ProductDigraph |
| ProductDigraphVertex | definition | definition | closed | - | - | LoopGraph |
| RamseyFromGraphPair | theorem | proof | open | - | - | DigraphToGraphIndependentSetBound, ProductDigraphForwardIndependentBound, SamplingKsFreeRamseyBound |
| RamseyNumber | definition | definition | closed | - | - | RamseyProperty |
| RamseyProperty | definition | definition | closed | - | - | Preamble |
| RandomHomomorphismColoringBound | lemma | proof | open | - | - | F2ForwardIndependentNearDiagonalBound, NoMonochromaticCliqueColoring |
| SamplingKsFreeRamseyBound | lemma | proof | open | - | - | RamseyNumber, SimpleGraphIndependentSetCount |
| SimpleGraphIndependentSetCount | definition | definition | closed | - | - | Preamble |
| SparseNeighborhoodSetBound | lemma | proof | open | - | - | ExpanderMixingLemma |
| TransitiveTournamentFree | definition | definition | closed | - | - | Digraph |

**Total:** 50 nodes | **Closed:** 31 | **Open:** 19
