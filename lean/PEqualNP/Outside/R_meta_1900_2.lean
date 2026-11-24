import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import PEqualNP.Defs

open PEqualNP.BicliqueBlockCost PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- The first child is the regular case. The second preserves the additive size deficit.
theorem PEqualNP.Outside.R_meta_1900_2
    (regular : ∀ (n t d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      4 ≤ d → Even d → G.Connected → (∀ v, (G.neighborSet v).ncard = d) →
      (∃ u v, G.Adj u v) → NoFourCycle G →
      (∀ S, IsVertexCover G S → t ≤ S.card) →
      Monotone2 C → circuitFun n C = graphFun G ∅ →
      G.edgeSet.ncard + t ≤ C.size + 1 + Nat.sqrt n)
    (pad : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v, G.Adj u v) → NoFourCycle G →
      (∀ S, IsVertexCover G S → t ≤ S.card) →
      Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ (m r d k : ℕ) (K : SimpleGraph (Fin m)) (decK : DecidableRel K.Adj) (D : Circuit),
        Nat.sqrt m < k ∧ 4 ≤ d ∧ Even d ∧ K.Connected ∧ (∀ v, (K.neighborSet v).ncard = d) ∧
        (∃ u v, K.Adj u v) ∧ @NoFourCycle m K decK ∧
        (∀ S, IsVertexCover K S → r ≤ S.card) ∧
        Monotone2 D ∧ circuitFun m D = @graphFun m K decK ∅ ∧
        k * (G.edgeSet.ncard + t) + (D.size + 1) ≤ K.edgeSet.ncard + r + k * (C.size + 1)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  intro n G C hEdge hFour hMono hEval
  classical
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  have noC4 : NoFourCycle G := by
    intro a b hab
    by_contra h
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge h)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
    exact hFour a c b d hc.1.ne hab hd.1.ne hc.2.symm.ne hcd hd.2.ne
      hc.1 hc.2.symm hd.2 hd.1.symm
  have computes : circuitFun n C = graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    apply Bool.eq_iff_iff.mpr
    simpa using hEval x
  have existsCover : ∃ t : ℕ, ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card = t :=
    ⟨n, Finset.univ, (fun _ _ _ => Or.inl (Finset.mem_univ _)), by simp⟩
  let t := Nat.find existsCover
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec existsCover
  have minCover (S : Finset (Fin n)) (hS : IsVertexCover G S) : t ≤ S.card :=
    Nat.find_min' existsCover ⟨S, hS, rfl⟩
  obtain ⟨m, r, d, k, K, decK, D, hk, hd, hEven, hConnected, hReg, hEdgeK, hFourK, hCoverK, hMonoK, hCompK, hPad⟩ :=
    pad n t G C hEdge noC4 minCover hMono computes
  have hLower := @regular m r d K decK D hd hEven hConnected hReg hEdgeK hFourK hCoverK hMonoK hCompK
  have hBudget : G.edgeSet.ncard + T.card ≤ C.size + 1 := by
    change T.card = t at hcard
    rw [hcard]
    by_contra h
    have hStrict := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    have hScale := Nat.mul_le_mul_left k hStrict
    rw [Nat.mul_succ] at hScale
    omega
  have cardinality : G.edgeFinset.card = G.edgeSet.ncard := by
    exact Set.ncard_coe_finset G.edgeFinset |>.symm.trans (congrArg Set.ncard G.coe_edgeFinset)
  have mkBlocks {T : Finset (Fin n)} (hT : IsVertexCover G T)
      (hcost : G.edgeFinset.card + T.card ≤ C.size + 1)
      (hedge : ∃ u v, G.Adj u v) : HasBlockCost G C.size := by
    let cost := C.size
    change G.edgeFinset.card + T.card ≤ cost + 1 at hcost
    classical
    let L (c : Fin n) : Finset (Fin n) :=
      Finset.univ.filter fun v => G.Adj c v ∧ (v ∉ T ∨ c < v)
    let S := T.filter fun c => (L c).Nonempty
    let P (c : Fin n) : Block n := ({c}, L c)
    let E (c : Fin n) : Finset (Sym2 (Fin n)) := (L c).image fun v => s(c,v)
    have hL (c v : Fin n) : v ∈ L c ↔ G.Adj c v ∧ (v ∉ T ∨ c < v) := by
      simp [L]
    have hP : Function.Injective P := by
      intro c d h
      have e := congrArg Prod.fst h
      simpa [P] using e
    have hE (c : Fin n) : Function.Injective (fun v : Fin n => s(c,v)) := by
      intro u v h
      rcases Sym2.eq_iff.mp h with h | h
      · exact h.2
      · exact h.2.trans h.1
    have hT' {c : Fin n} (hc : c ∈ S) : c ∈ T := (Finset.mem_filter.mp hc).1
    have hpart : (S : Set (Fin n)).PairwiseDisjoint E := by
      intro c hc d hd hcd
      apply Finset.disjoint_left.mpr
      intro e hec hed
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hec
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hed
      rcases Sym2.eq_iff.mp hab with ⟨hdc, _⟩ | ⟨hda, hbc⟩
      · exact hcd hdc.symm
      · rw [← hda] at ha
        rw [hbc] at hb
        have hlt := ((hL _ _).mp ha).2.resolve_left (fun h => h (hT' hd))
        have hgt := ((hL _ _).mp hb).2.resolve_left (fun h => h (hT' hc))
        exact lt_asymm hlt hgt
    have hsub : S.biUnion E ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨c, _, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
      exact G.mem_edgeFinset.mpr ((hL _ _).mp hv).1
    have hS : ∀ u v, G.Adj u v → (u ∈ S ∧ v ∈ L u) ∨ (v ∈ S ∧ u ∈ L v) := by
      intro u v h
      have fromLeaf (c w : Fin n) (hc : c ∈ T) (hw : w ∈ L c) : c ∈ S ∧ w ∈ L c :=
        ⟨Finset.mem_filter.mpr ⟨hc, ⟨w, hw⟩⟩, hw⟩
      by_cases hu : u ∈ T
      · by_cases hv : v ∈ T
        · rcases lt_or_gt_of_ne h.ne with huv | hvu
          · exact Or.inl (fromLeaf u v hu ((hL u v).mpr ⟨h, Or.inr huv⟩))
          · exact Or.inr (fromLeaf v u hv ((hL v u).mpr ⟨h.symm, Or.inr hvu⟩))
        · exact Or.inl (fromLeaf u v hu ((hL u v).mpr ⟨h, Or.inl hv⟩))
      · have hv := (hT u v h).resolve_left hu
        exact Or.inr (fromLeaf v u hv ((hL v u).mpr ⟨h.symm, Or.inl hu⟩))
    have hne : S.Nonempty := by
      obtain ⟨u, v, h⟩ := hedge
      rcases hS u v h with h | h
      · exact ⟨u, h.1⟩
      · exact ⟨v, h.1⟩
    refine ⟨S.image P, ⟨?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
      refine ⟨?_, by simp [P], (Finset.mem_filter.mp hc).2, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro a ha hb
        have e : a = c := by simpa [P] using ha
        subst a
        exact G.loopless.irrefl c ((hL c c).mp hb).1
      · intro a ha b hb
        have e : a = c := by simpa [P] using ha
        subst a
        exact ((hL c b).mp hb).1
    · intro u v h
      rcases hS u v h with h | h
      · exact ⟨P u, Finset.mem_image_of_mem P h.1,
          Or.inl ⟨by simp [P], h.2⟩⟩
      · exact ⟨P v, Finset.mem_image_of_mem P h.1,
          Or.inr ⟨by simp [P], h.2⟩⟩
    · have hweight : (∑ c ∈ S, (L c).card) ≤ G.edgeFinset.card := by
        calc
          _ = ∑ c ∈ S, (E c).card := by
            apply Finset.sum_congr rfl
            intro c _
            exact (Finset.card_image_of_injective _ (hE c)).symm
          _ = (S.biUnion E).card := (Finset.card_biUnion hpart).symm
          _ ≤ _ := Finset.card_le_card hsub
      have hs : S.card ≤ T.card := Finset.card_le_card (fun _ h => hT' h)
      have hpos : 0 < S.card := Finset.card_pos.mpr hne
      have blockCostEq (c : Fin n) : blockCost (P c) = (L c).card := by
        change 1 + (L c).card - 1 = _
        exact Nat.one_add_sub_one _
      change (∑ p ∈ S.image P, blockCost p) + ((S.image P).card - 1) ≤ cost
      rw [Finset.card_image_of_injective _ hP]
      rw [Finset.sum_image (fun _ _ _ _ h => hP h)]
      simp only [blockCostEq]
      omega
  exact mkBlocks hT (cardinality.symm ▸ hBudget) hEdge
