import Mathlib

set_option autoImplicit false

namespace Aqarion.P2Cone

/-- The ten facet forms: a_0..a_3, then a_i + a_j - k for i < j. -/
def facet (j : Fin 10) (x : Fin 5 → ℝ) : ℝ :=
  ![x 0, x 1, x 2, x 3,
    x 0 + x 1 - x 4, x 0 + x 2 - x 4, x 0 + x 3 - x 4,
    x 1 + x 2 - x 4, x 1 + x 3 - x 4, x 2 + x 3 - x 4] j

def cone : Set (Fin 5 → ℝ) := {x | ∀ j, 0 ≤ facet j x}

def strictCone : Set (Fin 5 → ℝ) := {x | ∀ j, 0 < facet j x}

def kappa : Fin 5 → ℝ := fun _ => 1

theorem facet_kappa (j : Fin 10) : facet j kappa = 1 := by
  fin_cases j <;> simp [facet, kappa]

theorem facet_sub_kappa (j : Fin 10) (x : Fin 5 → ℝ) (c : ℝ) :
    facet j (x - c • kappa) = facet j x - c := by
  fin_cases j <;> simp [facet, kappa] <;> ring

theorem facet_continuous (j : Fin 10) : Continuous (facet j) := by
  fin_cases j <;> simp [facet] <;> fun_prop

theorem strictCone_isOpen : IsOpen strictCone := by
  have h : strictCone = ⋂ j : Fin 10, {x | 0 < facet j x} := by
    ext x
    simp [strictCone]
  rw [h]
  exact isOpen_iInter_of_finite (fun j => isOpen_lt continuous_const (facet_continuous j))

theorem strictCone_subset_cone : strictCone ⊆ cone := fun _ hx j => le_of_lt (hx j)

theorem interior_cone : interior cone = strictCone := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxc : x ∈ cone := interior_subset hx
    have hn : cone ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
    have hcont : Continuous fun t : ℝ => x - t • kappa := by
      first
        | fun_prop
        | exact continuous_const.sub (continuous_id.smul continuous_const)
    have hat : Filter.Tendsto (fun t : ℝ => x - t • kappa) (nhds 0) (nhds x) := by
      have h0 := hcont.tendsto 0
      simpa using h0
    have hev : ∀ᶠ t in nhds (0 : ℝ), x - t • kappa ∈ cone := hat.eventually_mem hn
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hev
    have hd : dist (δ / 2) (0 : ℝ) < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith
    have hmem := h hd
    show ∀ j : Fin 10, 0 < facet j x
    intro j
    have h1 := hmem j
    rw [facet_sub_kappa] at h1
    have h2 := hxc j
    linarith
  · exact interior_maximal strictCone_subset_cone strictCone_isOpen

end Aqarion.P2Cone

#print axioms Aqarion.P2Cone.facet_kappa
#print axioms Aqarion.P2Cone.interior_cone
