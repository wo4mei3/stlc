namespace Stlc

/-- Free variable identifiers. -/
abbrev Var := Nat

/-- Types of the Simply Typed Lambda Calculus (with a unit base type). -/
inductive Ty where
  | unit : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Locally nameless terms:
    bound variables use de Bruijn indices (`bvar`),
    free variables use names (`fvar`). -/
inductive Term where
  | unit : Term
  | bvar : Nat → Term
  | fvar : Var → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Free variables occurring in a term. -/
def fv : Term → List Var
  | .unit => []
  | .bvar _ => []
  | .fvar x => [x]
  | .lam _ e => fv e
  | .app e₁ e₂ => fv e₁ ++ fv e₂

/-- Variable opening at depth `k`: replaces `bvar k` with `u`. -/
def openRec (k : Nat) (u : Term) : Term → Term
  | .unit => .unit
  | .bvar n => if k == n then u else .bvar n
  | .fvar x => .fvar x
  | .lam τ e => .lam τ (openRec (k + 1) u e)
  | .app e₁ e₂ => .app (openRec k u e₁) (openRec k u e₂)

/-- Open the outermost binder of `e` with term `u`. -/
def openTerm (e u : Term) : Term :=
  openRec 0 u e

/-- Open the outermost binder of `e` with free variable `x`. -/
def openVar (e : Term) (x : Var) : Term :=
  openRec 0 (.fvar x) e

/-- Capture-avoiding substitution for a free variable `x`. -/
def subst (x : Var) (u : Term) : Term → Term
  | .unit => .unit
  | .bvar n => .bvar n
  | .fvar y => if x == y then u else .fvar y
  | .lam τ e => .lam τ (subst x u e)
  | .app e₁ e₂ => .app (subst x u e₁) (subst x u e₂)

/-- Produce a variable name fresh for a finite list `L`. -/
def fresh (L : List Var) : Var :=
  L.foldr max 0 + 1

private theorem lt_fresh_of_mem {L : List Var} {y : Var} (hy : y ∈ L) : y < fresh L := by
  induction L with
  | nil => cases hy
  | cons a t ih =>
    simp only [fresh, List.foldr_cons]
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt_succ (ih hmem)) (Nat.le_max_right _ _))

theorem exists_fresh (L : List Var) : ∃ x : Var, x ∉ L :=
  ⟨fresh L, fun hmem => Nat.lt_irrefl _ (lt_fresh_of_mem hmem)⟩

/-- Locally closed terms (cofinite quantification). -/
inductive LC : Term → Prop where
  | unit : LC .unit
  | fvar (x : Var) : LC (.fvar x)
  | lam (L : List Var) (τ : Ty) (e : Term) :
      (∀ x, x ∉ L → LC (openVar e x)) → LC (.lam τ e)
  | app : LC e₁ → LC e₂ → LC (.app e₁ e₂)

/-- Call-by-value values (must be locally closed). -/
inductive IsValue : Term → Prop where
  | unit : IsValue .unit
  | lam : LC (.lam τ e) → IsValue (.lam τ e)

theorem IsValue.lc {v : Term} (hv : IsValue v) : LC v := by
  cases hv with
  | unit => exact .unit
  | lam hlc => exact hlc

private theorem openRec_lc_aux {e u v : Term} {i j : Nat}
    (hij : i ≠ j) (h : openRec j v (openRec i u e) = openRec i u e) :
    openRec j v e = e := by
  induction e generalizing i j with
  | unit => rfl
  | fvar _ => rfl
  | bvar n =>
    simp only [openRec] at h ⊢
    by_cases hjn : j = n
    · subst hjn
      have hin : (i == j) = false := beq_false_of_ne hij
      simp only [hin, Bool.false_eq_true, ↓reduceIte, openRec, beq_self_eq_true] at h ⊢
      exact h
    · have hjnb : (j == n) = false := beq_false_of_ne hjn
      simp [hjnb]
  | lam τ e ih =>
    simp only [openRec, Term.lam.injEq, true_and] at h ⊢
    exact ih (by omega) h
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [openRec, Term.app.injEq] at h ⊢
    exact ⟨ih₁ hij h.1, ih₂ hij h.2⟩

/-- Opening has no effect on a locally closed term. -/
theorem openRec_lc {e : Term} (hlc : LC e) (k : Nat) (u : Term) :
    openRec k u e = e := by
  induction hlc generalizing k u with
  | unit => rfl
  | fvar _ => rfl
  | lam L τ e _ ih =>
    simp only [openRec, Term.lam.injEq, true_and]
    obtain ⟨x, hx⟩ := exists_fresh L
    exact openRec_lc_aux (Nat.zero_ne_add_one k) (ih x hx (k + 1) u)
  | app _ _ ih₁ ih₂ =>
    simp only [openRec, Term.app.injEq]
    exact ⟨ih₁ k u, ih₂ k u⟩

/-- Substitution distributes over opening when the substituted term is locally closed. -/
theorem subst_openRec {e u v : Term} {x : Var} {k : Nat} (hlc : LC u) :
    subst x u (openRec k v e) = openRec k (subst x u v) (subst x u e) := by
  induction e generalizing k with
  | unit => rfl
  | bvar n =>
    simp only [openRec, subst]
    by_cases hkn : k = n
    · subst hkn; simp
    · have hknb : (k == n) = false := beq_false_of_ne hkn
      simp [hknb, subst]
  | fvar y =>
    simp only [openRec, subst]
    by_cases hxy : x = y
    · subst hxy
      simp [openRec_lc hlc]
    · have hxyb : (x == y) = false := beq_false_of_ne hxy
      simp [hxyb, openRec]
  | lam τ e ih =>
    simp only [openRec, subst, Term.lam.injEq, true_and]
    exact ih
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [openRec, subst, Term.app.injEq]
    exact ⟨ih₁, ih₂⟩

theorem subst_openVar {e u : Term} {x y : Var} (hxy : x ≠ y) (hlc : LC u) :
    subst x u (openVar e y) = openVar (subst x u e) y := by
  have h := subst_openRec (e := e) (u := u) (v := .fvar y) (x := x) (k := 0) hlc
  have hxyb : (x == y) = false := beq_false_of_ne hxy
  simpa [openVar, subst, hxyb] using h

/-- Substituting a variable that does not occur free does nothing. -/
theorem subst_fresh {e u : Term} {x : Var} (h : x ∉ fv e) :
    subst x u e = e := by
  induction e with
  | unit => rfl
  | bvar _ => rfl
  | fvar y =>
    simp only [fv, List.mem_singleton] at h
    have hxyb : (x == y) = false := beq_false_of_ne h
    simp [subst, hxyb]
  | lam τ e ih =>
    simp only [fv] at h
    simp [subst, ih h]
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [fv, List.mem_append, not_or] at h
    simp [subst, ih₁ h.1, ih₂ h.2]

/-- Expressing term opening via variable opening and substitution. -/
theorem subst_intro {e u : Term} {x : Var} (h : x ∉ fv e) (hlc : LC u) :
    openTerm e u = subst x u (openVar e x) := by
  have h1 := subst_openRec (e := e) (u := u) (v := .fvar x) (x := x) (k := 0) hlc
  simp only [subst, beq_self_eq_true, ↓reduceIte, subst_fresh h] at h1
  exact h1.symm

theorem LC.subst {e u : Term} {x : Var} (he : LC e) (hu : LC u) :
    LC (Stlc.subst x u e) := by
  induction he with
  | unit => exact .unit
  | fvar y =>
    simp only [Stlc.subst]
    by_cases hxy : x = y
    · subst hxy; simp [hu]
    · have hxyb : (x == y) = false := beq_false_of_ne hxy
      simp [hxyb, LC.fvar]
  | lam L τ e _ ih =>
    refine .lam (x :: L) τ (Stlc.subst x u e) fun y hy => ?_
    simp only [List.mem_cons, not_or] at hy
    rw [← subst_openVar (Ne.symm hy.1) hu]
    exact ih y hy.2
  | app _ _ ih₁ ih₂ =>
    exact .app ih₁ ih₂

/-- Typing context: association list of free variables to types. -/
abbrev Ctx := List (Var × Ty)

/-- Domain (bound free-variable names) of a typing context. -/
def dom (Γ : Ctx) : List Var :=
  Γ.map Prod.fst

/-- Well-formed typing context (no duplicate variable bindings). -/
inductive CtxOk : Ctx → Prop where
  | nil : CtxOk []
  | cons : CtxOk Γ → x ∉ dom Γ → CtxOk ((x, τ) :: Γ)

theorem mem_dom_of_mem {Γ : Ctx} {x : Var} {τ : Ty} (h : (x, τ) ∈ Γ) : x ∈ dom Γ :=
  List.mem_map.mpr ⟨(x, τ), h, rfl⟩

theorem CtxOk.unique {Γ : Ctx} {x : Var} {τ₁ τ₂ : Ty}
    (hok : CtxOk Γ) (h₁ : (x, τ₁) ∈ Γ) (h₂ : (x, τ₂) ∈ Γ) : τ₁ = τ₂ := by
  induction hok with
  | nil => cases h₁
  | @cons Γ y σ _ hfresh ih =>
    rcases List.mem_cons.mp h₁ with h1 | h1 <;> rcases List.mem_cons.mp h₂ with h2 | h2
    · cases h1; cases h2; rfl
    · cases h1; exact False.elim (hfresh (mem_dom_of_mem h2))
    · cases h2; exact False.elim (hfresh (mem_dom_of_mem h1))
    · exact ih h1 h2

theorem CtxOk.remove {Γ₁ Γ₂ : Ctx} {x : Var} {σ : Ty}
    (hok : CtxOk (Γ₁ ++ (x, σ) :: Γ₂)) : CtxOk (Γ₁ ++ Γ₂) := by
  induction Γ₁ with
  | nil =>
    cases hok with
    | cons h _ => exact h
  | cons p Γ₁ ih =>
    simp only [List.cons_append] at hok ⊢
    cases hok with
    | cons h hfresh =>
      refine .cons (ih h) fun hmem => hfresh ?_
      simp only [dom, List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hmem ⊢
      rcases hmem with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)

/-- Typing relation `Γ ⊢ e : τ` (with cofinite quantification in `lam`). -/
inductive HasType : Ctx → Term → Ty → Prop where
  | unit : CtxOk Γ → HasType Γ .unit .unit
  | fvar : CtxOk Γ → (x, τ) ∈ Γ → HasType Γ (.fvar x) τ
  | lam (L : List Var) :
      (∀ x, x ∉ L → HasType ((x, τ₁) :: Γ) (openVar e x) τ₂) →
      HasType Γ (.lam τ₁ e) (.arrow τ₁ τ₂)
  | app : HasType Γ e₁ (.arrow τ₁ τ₂) → HasType Γ e₂ τ₁ → HasType Γ (.app e₁ e₂) τ₂

theorem HasType.ctxOk {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) : CtxOk Γ := by
  induction h with
  | unit hok => exact hok
  | fvar hok _ => exact hok
  | lam L _ ih =>
    obtain ⟨x, hx⟩ := exists_fresh L
    cases ih x hx with
    | cons hok _ => exact hok
  | app _ _ ih₁ _ => exact ih₁

theorem HasType.lc {Γ : Ctx} {e : Term} {τ : Ty} (h : HasType Γ e τ) : LC e := by
  induction h with
  | unit _ => exact .unit
  | fvar _ _ => exact .fvar _
  | lam L _ ih => exact .lam L _ _ ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂

/-- General weakening: inserting a context `Γ₂` preserves typing as long as the
    resulting context remains well-formed. -/
theorem HasType.weaken_mid {Γ₁ Γ₂ Γ₃ : Ctx} {e : Term} {τ : Ty}
    (h : HasType (Γ₁ ++ Γ₃) e τ) (hok : CtxOk (Γ₁ ++ Γ₂ ++ Γ₃)) :
    HasType (Γ₁ ++ Γ₂ ++ Γ₃) e τ := by
  generalize hΓ : Γ₁ ++ Γ₃ = Γ at h
  induction h generalizing Γ₁ with
  | unit _ =>
    exact .unit hok
  | fvar _ hmem =>
    subst hΓ
    refine .fvar hok ?_
    simp only [List.mem_append] at hmem ⊢
    rcases hmem with h1 | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h3
  | lam L _ ih =>
    subst hΓ
    refine .lam (L ++ dom (Γ₁ ++ Γ₂ ++ Γ₃)) fun x hx => ?_
    simp only [List.mem_append, not_or] at hx
    exact ih x hx.1 (Γ₁ := (x, _) :: Γ₁) (.cons hok hx.2) rfl
  | app _ _ ih₁ ih₂ =>
    exact .app (ih₁ hok hΓ) (ih₂ hok hΓ)

theorem HasType.weaken_head {Γ₁ Γ₂ : Ctx} {e : Term} {τ : Ty}
    (h : HasType Γ₂ e τ) (hok : CtxOk (Γ₁ ++ Γ₂)) :
    HasType (Γ₁ ++ Γ₂) e τ :=
  HasType.weaken_mid (Γ₁ := []) (Γ₂ := Γ₁) (Γ₃ := Γ₂) h hok

/-- Substitution lemma for free variables. -/
theorem HasType.subst {Γ₁ Γ₂ : Ctx} {x : Var} {e u : Term} {σ τ : Ty}
    (he : HasType (Γ₁ ++ (x, σ) :: Γ₂) e τ) (hu : HasType Γ₂ u σ) :
    HasType (Γ₁ ++ Γ₂) (Stlc.subst x u e) τ := by
  generalize hΓ : Γ₁ ++ (x, σ) :: Γ₂ = Γ at he
  induction he generalizing Γ₁ with
  | unit hok =>
    subst hΓ
    exact .unit hok.remove
  | @fvar Γ y τ hok hmem =>
    subst hΓ
    simp only [Stlc.subst]
    by_cases hxy : x = y
    · subst hxy
      have hmemx : (x, σ) ∈ Γ₁ ++ (x, σ) :: Γ₂ := by simp
      have hτ : τ = σ := hok.unique hmem hmemx
      subst hτ
      simp only [beq_self_eq_true, ↓reduceIte]
      exact hu.weaken_head hok.remove
    · have hxyb : (x == y) = false := beq_false_of_ne hxy
      simp only [hxyb, Bool.false_eq_true, ↓reduceIte]
      refine .fvar hok.remove ?_
      simp only [List.mem_append, List.mem_cons] at hmem ⊢
      rcases hmem with h1 | h2 | h3
      · exact Or.inl h1
      · cases h2; exact False.elim (hxy rfl)
      · exact Or.inr h3
  | lam L _ ih =>
    subst hΓ
    refine .lam (x :: L) fun y hy => ?_
    simp only [List.mem_cons, not_or] at hy
    rw [← subst_openVar (Ne.symm hy.1) hu.lc]
    exact ih y hy.2 (Γ₁ := (y, _) :: Γ₁) rfl
  | app _ _ ih₁ ih₂ =>
    exact .app (ih₁ hΓ) (ih₂ hΓ)

/-- β-reduction typing lemma: opening a well-typed abstraction with a well-typed argument. -/
theorem HasType.openTerm {Γ : Ctx} {e v : Term} {τ₀ τ₁ τ₂ : Ty}
    (hlam : HasType Γ (.lam τ₀ e) (.arrow τ₁ τ₂)) (hv : HasType Γ v τ₁) :
    HasType Γ (Stlc.openTerm e v) τ₂ := by
  cases hlam with
  | lam L hbody =>
    obtain ⟨x, hx⟩ := exists_fresh (fv e ++ L)
    simp only [List.mem_append, not_or] at hx
    rw [subst_intro hx.1 hv.lc]
    exact HasType.subst (Γ₁ := []) (hbody x hx.2) hv

end Stlc
