/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeBridge
public meta import LambdaTuring.ListCodeBridge

@[expose] public section

namespace LambdaTuring

/-- Evaluate both unary codes strictly, retaining their two numerical results. -/
def listCodeTuple (F G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code := .cons F G

theorem listCodeTuple_eval {F G : Turing.ToPartrec.Code} {f g : Nat →. Nat}
    (hf : ListCodeRepresents F f) (hg : ListCodeRepresents G g) (n : Nat) :
    (listCodeTuple F G).eval [n] =
      (f n).bind (fun a => (g n).map (fun b => [a,b])) := by
  apply Part.ext
  intro out
  change out ∈ (F.eval [n]).bind (fun x => (G.eval [n]).bind
    (fun y => Part.some (x.headI :: y))) ↔ _
  rw [hf n, hg n]
  constructor
  · intro hout
    obtain ⟨x, hx, hout⟩ := Part.mem_bind_iff.1 hout
    obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).1 hx
    obtain ⟨y, hy, hout⟩ := Part.mem_bind_iff.1 hout
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hy
    have heq : [a,b] = out := by simpa using (Part.mem_some_iff.1 hout).symm
    exact Part.mem_bind_iff.2 ⟨a, ha, (Part.mem_map_iff _).2 ⟨b, hb, heq⟩⟩
  · intro hout
    obtain ⟨a, ha, hout⟩ := Part.mem_bind_iff.1 hout
    obtain ⟨b, hb, heq⟩ := (Part.mem_map_iff _).1 hout
    apply Part.mem_bind_iff.2
    refine ⟨[a], (Part.mem_map_iff _).2 ⟨a, ha, rfl⟩, ?_⟩
    refine Part.mem_bind_iff.2 ⟨[b], (Part.mem_map_iff _).2 ⟨b, hb, rfl⟩, ?_⟩
    apply Part.mem_some_iff.2
    simpa using heq.symm

/-- Composing a verified two-argument numeric encoder with strict tuple
    evaluation preserves both undefined arguments. This lemma is conditional:
    the concrete `Nat.pair` encoder still has to be implemented. -/
theorem listCode_pair_of_encoder {F G P : Turing.ToPartrec.Code} {f g : Nat →. Nat}
    (hf : ListCodeRepresents F f) (hg : ListCodeRepresents G g)
    (hp : ∀ a b, P.eval [a,b] = Part.some [Nat.pair a b]) :
    ListCodeRepresents (.comp P (listCodeTuple F G))
      (fun n => (f n).bind (fun a => (g n).map (Nat.pair a))) := by
  intro n
  apply Part.ext
  intro out
  change out ∈ ((listCodeTuple F G).eval [n]).bind P.eval ↔ _
  rw [listCodeTuple_eval hf hg]
  constructor
  · intro hout
    obtain ⟨xs, hxs, hout⟩ := Part.mem_bind_iff.1 hout
    obtain ⟨a, ha, hxs⟩ := Part.mem_bind_iff.1 hxs
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hxs
    rw [hp a b] at hout
    have heq := Part.mem_some_iff.1 hout
    refine (Part.mem_map_iff _).2 ⟨Nat.pair a b, ?_, ?_⟩
    · exact Part.mem_bind_iff.2 ⟨a, ha, (Part.mem_map_iff _).2 ⟨b, hb, rfl⟩⟩
    · simpa using heq.symm
  · intro hout
    obtain ⟨v, hv, heq⟩ := (Part.mem_map_iff _).1 hout
    obtain ⟨a, ha, hv⟩ := Part.mem_bind_iff.1 hv
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hv
    refine Part.mem_bind_iff.2 ⟨[a,b], ?_, ?_⟩
    · exact Part.mem_bind_iff.2 ⟨a, ha, (Part.mem_map_iff _).2 ⟨b, hb, rfl⟩⟩
    · rw [hp a b]
      exact Part.mem_some_iff.2 heq.symm

#print axioms listCodeTuple_eval
#print axioms listCode_pair_of_encoder
end LambdaTuring
