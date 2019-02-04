{-# OPTIONS --cubical #-}

module Quotient where

import Cubical.Foundations.Equiv as ≃
open import Cubical.Foundations.NTypes
open import Cubical.Core.Everything hiding (module Σ)
open import Data.Product as Σ using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Pointwise.NonDependent
open import Function
open import Level
open import Relation.Binary

→-isSet : ∀ {a b} {A : Set a} {B : Set b} → isSet B → isSet (A → B)
→-isSet u f g p q i j x = u (f x) (g x) (cong (_$ x) p) (cong (_$ x) q) i j

set-fillSquare : ∀ {a} {A : Set a} {a₀₀ a₀₁ a₁₀ a₁₁ : A} →
  isSet A →
  (w : a₀₀ ≡ a₀₁) (e : a₁₀ ≡ a₁₁)
  (s : a₀₀ ≡ a₁₀) (n : a₀₁ ≡ a₁₁) →
  PathP (λ i → s i ≡ n i) w e
set-fillSquare u _ _ _ _ = toPathP (u _ _ _ _)

isSet→≡-isSet : ∀ {ℓ} {A : Set ℓ} → isSet A → {x y : A} (p q : x ≡ y) (r s : p ≡ q) → r ≡ s
isSet→≡-isSet u _ _ = isProp→isSet (u _ _) _ _

square-isProp : ∀ {a} {A : Set a} {a₀₀ a₀₁ a₁₀ a₁₁ : A} →
  isSet A →
  (w : a₀₀ ≡ a₀₁) (e : a₁₀ ≡ a₁₁)
  (s : a₀₀ ≡ a₁₀) (n : a₀₁ ≡ a₁₁) →
  isProp (PathP (λ i → s i ≡ n i) w e)
square-isProp {A = A} {a₀₀} {a₀₁} {a₁₀} {a₁₁} u w e s n =
  J (λ a₁₀′ s′ → (e′ : a₁₀′ ≡ a₁₁) → isProp (PathP (λ i → s′ i ≡ n i) w e′))
    (J (λ a₁₁′ n′ → (e′ : a₀₀ ≡ a₁₁′) → isProp (PathP (λ i → a₀₀ ≡ n′ i) w e′))
       (λ _ → isSet→≡-isSet u _ _)
       n)
    s e

set-fillCube : ∀ {a} {A : Set a}
  {a₀₀₀ a₀₀₁ a₀₁₀ a₀₁₁ a₁₀₀ a₁₀₁ a₁₁₀ a₁₁₁ : A}
  (u : isSet A) →
  (w₀ : a₀₀₀ ≡ a₀₁₀) (e₀ : a₁₀₀ ≡ a₁₁₀) (s₀ : a₀₀₀ ≡ a₁₀₀) (n₀ : a₀₁₀ ≡ a₁₁₀)
  (w₁ : a₀₀₁ ≡ a₀₁₁) (e₁ : a₁₀₁ ≡ a₁₁₁) (s₁ : a₀₀₁ ≡ a₁₀₁) (n₁ : a₀₁₁ ≡ a₁₁₁)
  (sw : a₀₀₀ ≡ a₀₀₁) (se : a₁₀₀ ≡ a₁₀₁) (nw : a₀₁₀ ≡ a₀₁₁) (ne : a₁₁₀ ≡ a₁₁₁)
  (bottom : PathP (λ i → s₀ i ≡ n₀ i) w₀ e₀) (top : PathP (λ i → s₁ i ≡ n₁ i) w₁ e₁)
  (left : PathP (λ i → w₀ i ≡ w₁ i) sw nw) (right : PathP (λ i → e₀ i ≡ e₁ i) se ne)
  (front : PathP (λ i → s₀ i ≡ s₁ i) sw se) (back : PathP (λ i → n₀ i ≡ n₁ i) nw ne) →
  PathP
    (λ i →
      PathP
        (λ j →
          bottom i j ≡ top i j)
        (front i)
        (back i))
    left
    right
set-fillCube {A = A}
  u
  w₀ e₀ s₀ n₀ w₁ e₁ s₁ n₁ sw se nw ne
  bottom top left right front back =
    toPathP (square-isProp u _ _ _ _ _ _)

infixl 1 _/_
data _/_ {a r} (A : Set a) (R : A → A → Set r) : Set (a ⊔ r) where
  ⟦_⟧ : A → A / R
  equiv : ∀ a b → R a b → ⟦ a ⟧ ≡ ⟦ b ⟧
  uip : isSet (A / R)

_/²_ : ∀ {a r} (A : Set a) (R : A → A → Set r) → Set _
A /² R = A × A / Pointwise R R

ind : ∀
  {a r b} {A : Set a} {R : A → A → Set r}
  (B : A / R → Set b) →
  (f : ∀ a → B ⟦ a ⟧) →
  (∀ a b (r : R a b) → PathP (λ i → B (equiv a b r i)) (f a) (f b)) →
  (∀ a b (p q : a ≡ b) (ba : B a) (bb : B b)
    (r : PathP (λ i → B (p i)) ba bb)
    (s : PathP (λ i → B (q i)) ba bb) →
    PathP (λ i → PathP (λ j → B (uip a b p q i j)) ba bb) r s) →
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
  {a b r} {A : Set a} {B : Set b} {R : A → A → Set r} →
  isSet B → (f : A → B) → (∀ a b → R a b → f a ≡ f b) →
  A / R → B
rec u f e = ind _ f e λ _ _ _ _ → u

map : ∀
  {a b r s} {A : Set a} {B : Set b} {R : A → A → Set r} {S : B → B → Set s} →
  (f : A → B) → (∀ x y → R x y → S (f x) (f y)) →
  A / R → B / S
map f e = rec uip (⟦_⟧ ∘ f) λ x y → equiv (f x) (f y) ∘ e x y

infixl 2 _//_
_//_ = map

map-inv : ∀
  {a b r s} {A : Set a} {B : Set b} {R : A → A → Set r} {S : B → B → Set s} →
  (f : A → B) (g : B → A) →
  (d : ∀ x y → R x y → S (f x) (f y)) (e : ∀ x y → S x y → R (g x) (g y))
  (p : ∀ x → R (g (f x)) x)
  (x : A / R) → map g e (map f d x) ≡ x
map-inv f g d e p ⟦ x ⟧ = equiv _ _ (p x)
map-inv f g d e p (equiv x y r i) =
  set-fillSquare uip
    (equiv _ _ (p x))
    (equiv _ _ (p y))
    (equiv _ _ (e _ _ (d _ _ r)))
    (equiv _ _ r)
    i
map-inv {A = A} {B} {R} {S} f g d e p (uip x y r s i j) =
  {-
    i  k
    ↑ ↗
    ⋆ → j

    u = map g e ∘ map f d
    v = map-inv f g d e p


                           y ----------→ y
                         ↗ ↑           ↗ ↑
                        /  |          /  |
                       /   | v y     /   | v y
                    r /    |      s /    |
                     /     |       /     |
                    /      u y ---/----→ u y
                   /       ↗     /       ↗
                  /       /     /       /
                 x  --------→  x       /
                 ↑      /      ↑      /
                 | u r /       | u s /
                 |    /        |    /
             v x |   /     v x |   /
                 |  /          |  /
                 | /           | /
                u x --------→ u x
  -}
  set-fillCube uip _ _ _ _ _ _ _ _ _ _ _ _
    (uip _ _ _ _) (uip _ _ _ _)
    (cong (map-inv f g d e p) r) (cong (map-inv f g d e p) s)
    refl refl
    i j

isoToEquiv : ∀
  {a b r s} {A : Set a} {B : Set b} {R : A → A → Set r} {S : B → B → Set s} →
  (f : A → B) (g : B → A) →
  (d : ∀ x y → R x y → S (f x) (f y)) (e : ∀ x y → S x y → R (g x) (g y))
  (p : ∀ x → R (g (f x)) x) (q : ∀ y → S (f (g y)) y) →
  (A / R) ≃ (B / S)
isoToEquiv f g d e p q =
  ≃.isoToEquiv
    (map f d) (map g e)
    (map-inv g f e d q) (map-inv f g d e p)

zip : ∀
  {a b r s} {A : Set a} {B : Set b} {R : A → A → Set r} {S : B → B → Set s} →
  Reflexive R → Reflexive S →
  A / R → B / S → A × B / Pointwise R S
zip {A = A} {B} {R} {S} reflA reflB =
  rec (→-isSet uip)
    (λ x → map (x ,_) (λ _ _ → reflA ,_))
    λ u v r i →
      rec uip
        (λ x → equiv (u , x) (v , x) (r , reflB) i)
        λ x y s j →
          set-fillSquare uip
            (equiv (u , x) (u , y) (reflA , s))
            (equiv (v , x) (v , y) (reflA , s))
            (equiv (u , x) (v , x) (r , reflB))
            (equiv (u , y) (v , y) (r , reflB))
            i j

uncurry : ∀
  {a b c r s} {A : Set a} {B : Set b} {C : Set c} {R : A → A → Set r} {S : B → B → Set s} →
  Reflexive R → Reflexive S →
  (A × B / Pointwise R S → C) →
  A / R → B / S → C
uncurry reflA reflB f x y = f (zip reflA reflB x y)

unzip : ∀
  {a b r s} {A : Set a} {B : Set b} {R : A → A → Set r} {S : B → B → Set s} →
  A × B / Pointwise R S → (A / R) × (B / S)
unzip ⟦ x , y ⟧ = ⟦ x ⟧ , ⟦ y ⟧
unzip (equiv (u , v) (x , y) (p , q) i) =
  equiv u x p i , equiv v y q i
unzip (uip x y p q i j) =
  (uip _ _ (cong (proj₁ ∘ unzip) p) (cong (proj₁ ∘ unzip) q) i j) ,
  (uip _ _ (cong (proj₂ ∘ unzip) p) (cong (proj₂ ∘ unzip) q) i j)

curry : ∀
  {a b c r s} {A : Set a} {B : Set b} {C : Set c} {R : A → A → Set r} {S : B → B → Set s} →
  (A / R → B / S → C) →
  A × B / Pointwise R S → C
curry f x = f (proj₁ (unzip x)) (proj₂ (unzip x))
