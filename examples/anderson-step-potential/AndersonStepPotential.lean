import OAI.MathematicalPhysics.PlanarAnderson.Spectrum

set_option warningAsError true

namespace TheoremOS.AndersonReuse

open OAI.PlanarAnderson

/-- A deterministic potential with values -height and height on the two half-planes. -/
def stepPotential (height : ℝ) : Configuration :=
  fun x => if 0 ≤ x.1 then height else -height

/-- Arbitrarily large constant squares at a level give the corresponding spectral band. -/
private theorem mem_spectrum_of_constant_squares
    {v : Configuration} {H : Hilbert →L[ℂ] Hilbert} (hop : IsAndersonOperator v H)
    {level energy : ℝ} (hEnergy : energy ∈ Set.Icc (-4 + level) (4 + level))
    (squares : ∀ radius : ℕ, ∃ center : Site, ∀ x : Site,
      (x.1 - center.1).natAbs ≤ radius → (x.2 - center.2).natAbs ≤ radius → v x = level) :
    (energy : ℂ) ∈ spectrum ℂ H := by
  apply cps_mem_spectrum_of_approx
  intro ε hε
  obtain ⟨radius, approx⟩ := finite_box_approx_eigenvector hop level energy hEnergy ε hε
  obtain ⟨center, constantOnSquare⟩ := squares radius
  obtain ⟨u, hu, hResidual⟩ := approx center radius le_rfl (by
    intro x hx hy
    rw [constantOnSquare x hx hy, sub_self, abs_zero]
    exact half_pos hε)
  refine ⟨u, hu, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, ← neg_sub H ((energy : ℂ) • 1),
    neg_apply, norm_neg]
  exact hResidual

/-- Each half-plane forces a whole real interval into the spectrum. -/
theorem stepPotential_spectrum_bands {height energy : ℝ} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator (stepPotential height) H)
    (hEnergy : energy ∈ Set.Icc (-4 - height) (4 - height) ∪
      Set.Icc (-4 + height) (4 + height)) :
    (energy : ℂ) ∈ spectrum ℂ H := by
  rcases hEnergy with hLeft | hRight
  · apply mem_spectrum_of_constant_squares hop (level := -height)
      (by simpa only [sub_eq_add_neg] using hLeft)
    intro radius
    refine ⟨(-(radius : ℤ) - 1, 0), ?_⟩
    intro x hx _
    have hxUpper := (Finset.mem_Icc.mp ((natAbs_le_iff _ _).mp hx)).2
    exact ite_eq_right (by omega)
  · apply mem_spectrum_of_constant_squares hop hRight
    intro radius
    refine ⟨((radius : ℤ), 0), ?_⟩
    intro x hx _
    have hxLower := (Finset.mem_Icc.mp ((natAbs_le_iff _ _).mp hx)).1
    exact ite_eq_left (by omega)

/-- When the bands overlap, they exhaust the spectrum of the step-potential operator. -/
theorem stepPotential_spectrum {height : ℝ} (hNonneg : 0 ≤ height) (hOverlap : height ≤ 4) :
    ∃ H : Hilbert →L[ℂ] Hilbert, IsAndersonOperator (stepPotential height) H ∧
      IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval height := by
  have hBound (x : Site) : |stepPotential height x| ≤ height := by
    unfold stepPotential
    split <;> simp [abs_of_nonneg hNonneg]
  obtain ⟨H, hop, hSelfAdjoint, hNorm⟩ :=
    anderson_operator_exists_selfAdjoint (stepPotential height) hBound
  refine ⟨H, hop, hSelfAdjoint, Set.Subset.antisymm
    (spectrum_subset_spectralInterval_of_norm_le hSelfAdjoint hNorm) ?_⟩
  intro z hz
  obtain ⟨hIm, hLower, hUpper⟩ := hz
  have hReal : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hIm)
  rw [hReal]
  apply stepPotential_spectrum_bands hop
  rcases le_or_gt z.re (4 - height) with hLeft | hRight
  · exact Or.inl ⟨hLower, hLeft⟩
  · exact Or.inr ⟨by linarith, hUpper⟩

#print axioms stepPotential_spectrum_bands
#print axioms stepPotential_spectrum

end TheoremOS.AndersonReuse
