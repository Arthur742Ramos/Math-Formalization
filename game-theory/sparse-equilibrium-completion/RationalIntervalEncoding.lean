/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalLinearForms
public import RationalIntervalForms
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev RationalIntervalTailRows (m H : ℕ) :=
  Fin m ⊕ (Fin m ⊕ ((Fin 2 × (Fin H × Fin m)) ⊕ Fin H))
abbrev RationalIntervalRows (k m H : ℕ) :=
  Fin m ⊕ (Fin 2 ⊕ ((Fin 2 × (Fin m × Fin k)) ⊕
    ((Fin 4 × (Fin k × Fin k)) ⊕ (Fin k ⊕ RationalIntervalTailRows m H))))

def intervalQForm (k m H : ℕ) (i : Fin m) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inl i)
def intervalVForm (k m H : ℕ) (i : Fin m) (a : Fin k) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inr (.inl (i,a)))
def intervalKForm (k m H : ℕ) (a b : Fin k) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inr (.inr (.inl (a,b))))
def intervalAuxForm (k m H : ℕ) (l : Fin H) (i : Fin m) : Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  intervalBasis (k := k) (m := m) (H := H) (.inr (.inr (.inr (l,i))))

def rationalIntervalCoefficient {k m : ℕ} (H : ℕ)
    (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalIntervalRows k m H → Fin (m+(m*k+(k*k+H*m))) → ℚ :=
  let Q := intervalQForm k m H
  let V := intervalVForm k m H
  let K := intervalKForm k m H
  let A := intervalAuxForm k m H
  let scoreV := fun i => rationalFormSum (fun a => rationalFormScale (p a) (V i a))
  Sum.elim (fun i => rationalFormScale (-1) (Q i))
    (Sum.elim (fun s => rationalFormScale (if s.val=0 then 1 else -1) (rationalFormSum Q))
      (Sum.elim (fun row =>
        if row.1.val=0 then
          rationalFormAdd (rationalFormScale (lo row.2.1 row.2.2) (Q row.2.1))
            (rationalFormScale (-1) (V row.2.1 row.2.2))
        else rationalFormAdd (V row.2.1 row.2.2)
          (rationalFormScale (-hi row.2.1 row.2.2) (Q row.2.1)))
        (Sum.elim (fun row =>
          if row.1.val=0 then rationalFormAdd (K row.2.1 row.2.2) (K row.2.2 row.2.1)
          else if row.1.val=1 then rationalFormScale (-1)
            (rationalFormAdd (K row.2.1 row.2.2) (K row.2.2 row.2.1))
          else if row.1.val=2 then rationalFormScale (-1) (K row.2.1 row.2.2)
          else K row.2.1 row.2.2)
          (Sum.elim (fun a =>
            rationalFormAdd (rationalFormSum (fun b => rationalFormScale (p b) (K a b)))
              (rationalFormScale (-1) (rationalFormSum (fun i => V i a))))
            (Sum.elim (fun _ => fun _ => 0)
              (Sum.elim (fun i => rationalFormAdd (scoreV i) (rationalFormScale (-(ρ+M*r)) (Q i)))
                (Sum.elim (fun row =>
                  if row.1.val=0 then rationalFormScale (-1) (A row.2.1 row.2.2)
                  else rationalFormAdd
                    (rationalFormAdd (scoreV row.2.2)
                      (rationalFormScale (-(ρ+(M*r-rationalGridNode M r η (row.2.1.val+1))))
                        (Q row.2.2)))
                    (rationalFormScale (-1) (A row.2.1 row.2.2)))
                  (fun l => rationalFormSum (A l)))))))))

def rationalIntervalRightSide {k m : ℕ} (H : ℕ)
    (loK hiK : Fin k → Fin k → ℚ) (lo : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) : RationalIntervalRows k m H → ℚ :=
  Sum.elim (fun _ => 0)
    (Sum.elim (fun s => if s.val=0 then r else -r)
      (Sum.elim (fun _ => 0)
        (Sum.elim (fun row =>
          if row.1.val=0 then 0 else if row.1.val=1 then 0
          else if row.1.val=2 then -loK row.2.1 row.2.2 else hiK row.2.1 row.2.2)
          (Sum.elim (fun _ => ρ)
            (Sum.elim (fun i => ρ+M*r-rationalScore lo p i)
              (Sum.elim (fun _ => 0)
                (Sum.elim (fun _ => 0) (fun l =>
                  rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))))))))))

def rationalIntervalSystem {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) :
    RationalLinearSystem (RationalIntervalRows k m (rationalGridSize M r η))
      (m+(m*k+(k*k+rationalGridSize M r η*m))) :=
  ⟨rationalIntervalCoefficient (rationalGridSize M r η) lo hi p M r ρ η,
    rationalIntervalRightSide (rationalGridSize M r η) loK hiK lo p M r ρ η⟩

theorem rational_interval_row_count (k m H : ℕ) :
    Fintype.card (RationalIntervalRows k m H)=
      3*m+2+2*m*k+4*k*k+k+2*H*m+H := by
  simp only [RationalIntervalRows,RationalIntervalTailRows,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin]
  ring

end SparseCompletion
