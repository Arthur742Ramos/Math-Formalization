module
/-
Coverage preservation for the row gauges, common units, and permutations used
by the explicit triangle-to-representative certificates.  This is a generic
soundness theorem; it does not assert completeness of the archived graph.
-/
public import Std
public section

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace CoveringTransforms

/-- A named bound keeps the elaborated definition independent of proof-cache context. -/
theorem difference_lt (a b : Fin 9) : (b.val + 9 - a.val) % 9 < 9 :=
  Nat.mod_lt _ (by decide)

@[expose] def difference (a b : Fin 9) : Fin 9 :=
  ⟨(b.val + 9 - a.val) % 9, difference_lt a b⟩

@[expose] def unitValue (u : Fin 6) : Nat := [1,2,4,5,7,8].getD u.val 1
@[expose] def inverseValue (u : Fin 6) : Nat := [1,5,7,2,4,8].getD u.val 1
@[expose] def scale (u : Fin 6) (a : Fin 9) : Fin 9 :=
  ⟨(unitValue u * a.val) % 9, Nat.mod_lt _ (by decide)⟩
@[expose] def inverseScale (u : Fin 6) (a : Fin 9) : Fin 9 :=
  ⟨(inverseValue u * a.val) % 9, Nat.mod_lt _ (by decide)⟩
@[expose] def gauge (u : Fin 6) (base a : Fin 9) : Fin 9 := scale u (difference base a)

theorem differenceGauge : ∀ u : Fin 6, ∀ base a b : Fin 9,
    difference (gauge u base a) (gauge u base b) = scale u (difference a b) := by decide

theorem scaleInverse : ∀ u : Fin 6, ∀ a : Fin 9,
    scale u (inverseScale u a) = a := by decide

theorem inverseScaleScale : ∀ u : Fin 6, ∀ a : Fin 9,
    inverseScale u (scale u a) = a := by decide

@[expose] def ungauge (u : Fin 6) (base a : Fin 9) : Fin 9 :=
  ⟨(base.val + (inverseScale u a).val) % 9, Nat.mod_lt _ (by decide)⟩

theorem differenceUngauge : ∀ u : Fin 6, ∀ base a x : Fin 9,
    difference a (ungauge u base x) =
      inverseScale u (difference (gauge u base a) x) := by decide

@[expose] def Covers {R C : Type} (array : R → C → Fin 9) : Prop :=
  ∀ i j, i ≠ j → ∀ d, ∃ r, difference (array r i) (array r j) = d

/-- Any surjective row map, injective column map, row gauge, and unit preserve coverage. -/
theorem transformPreservesCoverage {R C S D : Type} (array : R → C → Fin 9)
    (covered : Covers array) (rows : S → R) (columns : D → C)
    (rowsSurjective : ∀ r, ∃ s, rows s = r)
    (columnsInjective : ∀ i j, columns i = columns j → i = j)
    (base : S → Fin 9) (unit : Fin 6) :
    Covers (fun s j => gauge unit (base s) (array (rows s) (columns j))) := by
  intro i j different d
  have sourceDifferent : columns i ≠ columns j := by
    intro same
    exact different (columnsInjective i j same)
  obtain ⟨r, hr⟩ := covered (columns i) (columns j) sourceDifferent (inverseScale unit d)
  obtain ⟨s, hs⟩ := rowsSurjective r
  refine ⟨s, ?_⟩
  rw [differenceGauge, hs, hr, scaleInverse]

@[expose] def Extends {R C : Type} (array : R → C → Fin 9) (newColumn : R → Fin 9) : Prop :=
  ∀ j d, ∃ r, difference (array r j) (newColumn r) = d

/-- An extension of a transformed array pulls back to an extension of its representative. -/
theorem pullbackExtension {R C S D : Type} (array : R → C → Fin 9)
    (rows : S → R) (inverseRows : R → S) (columns : D → C)
    (inverseAfterRows : ∀ s, inverseRows (rows s) = s)
    (columnsSurjective : ∀ j, ∃ d, columns d = j)
    (base : S → Fin 9) (unit : Fin 6) (newColumn : S → Fin 9)
    (extension : Extends (fun s j => gauge unit (base s) (array (rows s) (columns j))) newColumn) :
    Extends array (fun r => ungauge unit (base (inverseRows r)) (newColumn (inverseRows r))) := by
  intro j d
  obtain ⟨index, hindex⟩ := columnsSurjective j
  obtain ⟨s, hs⟩ := extension index (scale unit d)
  refine ⟨rows s, ?_⟩
  change difference (array (rows s) j)
    (ungauge unit (base (inverseRows (rows s))) (newColumn (inverseRows (rows s)))) = d
  rw [inverseAfterRows, differenceUngauge]
  have htarget : difference (gauge unit (base s) (array (rows s) j)) (newColumn s) =
      scale unit d := by
    rw [← hindex]
    exact hs
  rw [htarget, inverseScaleScale]

#print axioms differenceGauge
#print axioms scaleInverse
#print axioms inverseScaleScale
#print axioms differenceUngauge
#print axioms transformPreservesCoverage
#print axioms pullbackExtension

end CoveringTransforms
