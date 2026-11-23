import Stlc.Basic

namespace Stlc

/-- Call-by-value evaluation contexts:
    `E ::= □ | E e | v E` (where `v` is a value). -/
inductive EvalCtx where
  | hole : EvalCtx
  | appL : EvalCtx → Term → EvalCtx
  | appR : (v : Term) → IsValue v → EvalCtx → EvalCtx

/-- Plug a term into the hole of an evaluation context: `E[e]`. -/
def EvalCtx.plug : EvalCtx → Term → Term
  | .hole, e => e
  | .appL E e₂, e => .app (E.plug e) e₂
  | .appR v _ E, e => .app v (E.plug e)

/-- Top-level call-by-value β-reduction (redex contraction). -/
inductive BetaStep : Term → Term → Prop where
  | beta : LC (.lam τ e) → IsValue v → BetaStep (.app (.lam τ e) v) (openTerm e v)

/-- One-step call-by-value reduction via evaluation contexts:
    `E[r] ⟶ E[r']` whenever `r ↦_β r'`. -/
inductive Step : Term → Term → Prop where
  | ctx (E : EvalCtx) : BetaStep r r' → Step (E.plug r) (E.plug r')

/-- Multi-step reduction (reflexive transitive closure of `Step`). -/
inductive Steps : Term → Term → Prop where
  | refl : Steps e e
  | head : Step e₁ e₂ → Steps e₂ e₃ → Steps e₁ e₃

end Stlc
