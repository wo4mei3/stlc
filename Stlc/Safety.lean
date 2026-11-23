import Stlc.EvalCtx

namespace Stlc

/-- Typing decomposition and replacement lemma for evaluation contexts:
    if `Γ ⊢ E[e] : τ`, then `e` has some type `σ` under `Γ`, and plugging any
    term `e'` of type `σ` back into `E` yields a term of type `τ`. -/
theorem EvalCtx.typing_decompose (E : EvalCtx) {Γ : Ctx} {e : Term} {τ : Ty}
    (h : HasType Γ (E.plug e) τ) :
    ∃ σ, HasType Γ e σ ∧ ∀ e', HasType Γ e' σ → HasType Γ (E.plug e') τ := by
  induction E generalizing τ with
  | hole =>
    exact ⟨τ, h, fun _ h' => h'⟩
  | appL E e₂ ih =>
    cases h with
    | app h₁ h₂ =>
      obtain ⟨σ, he, hrep⟩ := ih h₁
      exact ⟨σ, he, fun e' he' => .app (hrep e' he') h₂⟩
  | appR v hv E ih =>
    cases h with
    | app h₁ h₂ =>
      obtain ⟨σ, he, hrep⟩ := ih h₂
      exact ⟨σ, he, fun e' he' => .app h₁ (hrep e' he')⟩

/-- Top-level β-reduction preserves typing. -/
theorem BetaStep.preservation {Γ : Ctx} {r r' : Term} {τ : Ty}
    (hty : HasType Γ r τ) (hstep : BetaStep r r') :
    HasType Γ r' τ := by
  cases hstep with
  | beta _ _ =>
    cases hty with
    | app hlam hv =>
      exact hlam.openTerm hv

/-- Preservation (Subject Reduction) for one-step evaluation-context reduction. -/
theorem Step.preservation {Γ : Ctx} {e e' : Term} {τ : Ty}
    (hty : HasType Γ e τ) (hstep : Step e e') :
    HasType Γ e' τ := by
  cases hstep with
  | ctx E hbeta =>
    obtain ⟨_, hr, hrep⟩ := E.typing_decompose hty
    exact hrep _ (hbeta.preservation hr)

/-- Preservation for multi-step reduction. -/
theorem Steps.preservation {Γ : Ctx} {e e' : Term} {τ : Ty}
    (hty : HasType Γ e τ) (hsteps : Steps e e') :
    HasType Γ e' τ := by
  induction hsteps with
  | refl => exact hty
  | head hstep _ ih => exact ih (hstep.preservation hty)

/-- Canonical forms lemma for function types. -/
theorem canonical_arrow {v : Term} {τ₁ τ₂ : Ty}
    (hty : HasType [] v (.arrow τ₁ τ₂)) (hv : IsValue v) :
    ∃ e, v = .lam τ₁ e := by
  cases hv with
  | unit => cases hty
  | lam _ =>
    cases hty
    exact ⟨_, rfl⟩

/-- Decomposition lemma: every closed well-typed term is either a value or
    decomposes into an evaluation context `E` and a β-redex `r`. -/
theorem decomposition {e : Term} {τ : Ty}
    (hty : HasType [] e τ) :
    IsValue e ∨ ∃ E : EvalCtx, ∃ r r', e = E.plug r ∧ BetaStep r r' := by
  generalize hΓ : ([] : Ctx) = Γ at hty
  induction hty with
  | unit _ =>
    exact Or.inl .unit
  | fvar _ hmem =>
    subst hΓ
    cases hmem
  | lam L hbody _ =>
    exact Or.inl (.lam (.lam L _ _ fun x hx => (hbody x hx).lc))
  | app h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ hΓ with hv₁ | ⟨E, r, r', rfl, hbeta⟩
    · rcases ih₂ hΓ with hv₂ | ⟨E, r, r', rfl, hbeta⟩
      · subst hΓ
        obtain ⟨body, rfl⟩ := canonical_arrow h₁ hv₁
        exact Or.inr ⟨.hole, _, _, rfl, .beta hv₁.lc hv₂⟩
      · exact Or.inr ⟨.appR _ hv₁ E, r, r', rfl, hbeta⟩
    · exact Or.inr ⟨.appL E _, r, r', rfl, hbeta⟩

/-- Progress: every closed well-typed term is either a value or can take a step. -/
theorem progress {e : Term} {τ : Ty}
    (hty : HasType [] e τ) :
    IsValue e ∨ ∃ e', Step e e' := by
  rcases decomposition hty with hv | ⟨E, r, r', rfl, hbeta⟩
  · exact Or.inl hv
  · exact Or.inr ⟨E.plug r', .ctx E hbeta⟩

/-- A term is not stuck if it is a value or can take a reduction step. -/
def NotStuck (e : Term) : Prop :=
  IsValue e ∨ ∃ e', Step e e'

/-- Type Safety: a closed well-typed term never gets stuck during evaluation. -/
theorem type_safety {e e' : Term} {τ : Ty}
    (hty : HasType [] e τ) (hsteps : Steps e e') :
    NotStuck e' :=
  progress (hsteps.preservation hty)

end Stlc
