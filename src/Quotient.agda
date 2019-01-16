module Quotient where

open import Cubical.Core.Everything
open import Function
open import Level

data _/_ {a r} (A : Set a) (R : A → A → Set r) : Set (a ⊔ r) where
  ⟦_⟧ : A → A / R
  equiv : ∀ a b → R a b → ⟦ a ⟧ ≡ ⟦ b ⟧
  uip : isSet (A / R)

ind : ∀
  {a r b} {A : Set a} {R : A → A → Set r}
  (B : A / R → Set b) →
  (f : ∀ a → B ⟦ a ⟧) →
  (∀ a b (r : R a b) → PathP (λ i → B (equiv a b r i)) (f a) (f b)) →
  (∀ a b (p q : a ≡ b) (fa : B a) (fb : B b)
    (r : PathP (λ i → B (p i)) fa fb)
    (s : PathP (λ i → B (q i)) fa fb) →
    PathP
      (λ i → PathP (λ j → B (uip a b p q i j)) fa fb)
      r s) →
  (x : A / R) → B x
ind B f e u ⟦ x ⟧ = f x
ind B f e u (equiv a b p i) = e a b p i
ind B f e u (uip a b p q i j) =
  u
    a b
    p q
    (ind B f e u a) (ind B f e u b)
    (cong (ind B f e u) p) (cong (ind B f e u) q)
    i j

rec : ∀
  {a b r} {A : Set a} {R : A → A → Set r} {B : Set b} →
  (f : A → B) → (∀ a b → R a b → f a ≡ f b) → isSet B →
  A / R → B
rec f e u = ind _ f e λ _ _ _ _ → u
