import GC.Computability.StructuralCompilers.PhaseRepair
import GC.Computability.StructuralCompilers.InteractionCover
import GC.Computability.StructuralCompilers.SegmentCuts
import GC.Computability.StructuralCompilers.PebblingBarrier
import GC.Computability.StructuralCompilers.UnionProfiles

/-!
# Structural compilers and their limits (result family 007)

* 007a `PhaseRepair`, `InteractionCover`: greedy phase repair, the unique fixed point of the
  reset-mask map, the interaction cover and its corrected residual evaluator.
* 007b `SegmentCuts`: maximal path packing, the guard–router reduction `dvd_K(R_d(H)) = dvd_k(H)`,
  rank anonymity on `𝒩_k`.
* 007c `PebblingBarrier`: pebbling projection for predecessor-preserving unfoldings and the grid
  pebbling lower bound `g + 1`.
* 007d `UnionProfiles`: absorbing elimination, the profile composition lemma, union-closure bounds.
-/
