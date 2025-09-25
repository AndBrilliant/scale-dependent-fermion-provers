-- Example: Basic fermion mass hierarchy proof in Lean
import FermionProvers.Basic

-- Define three fermion masses representing a generation
def first_generation : FermionMass := ⟨0.001, 1, "light", by norm_num⟩
def second_generation : FermionMass := ⟨0.1, 2, "medium", by norm_num⟩  
def third_generation : FermionMass := ⟨1.0, 3, "heavy", by norm_num⟩

-- Prove that this forms a proper mass hierarchy
example : mass_hierarchy first_generation second_generation third_generation := by
  constructor
  · -- Prove first < second
    simp [first_generation, second_generation]
    norm_num
  · -- Prove second < third  
    simp [second_generation, third_generation]
    norm_num

-- Prove transitivity of mass ordering
theorem mass_hierarchy_transitive (m1 m2 m3 : FermionMass) :
  mass_hierarchy m1 m2 m3 → m1.value < m3.value := by
  intro h
  cases h with
  | mk h1 h2 =>
    calc m1.value
      < m2.value := h1
      _ < m3.value := h2

-- Example: All fermion masses in a hierarchy are positive
theorem hierarchy_all_positive (m1 m2 m3 : FermionMass) :
  mass_hierarchy m1 m2 m3 → 
  0 < m1.value ∧ 0 < m2.value ∧ 0 < m3.value := by
  intro _
  constructor
  · exact m1.pos
  constructor  
  · exact m2.pos
  · exact m3.pos