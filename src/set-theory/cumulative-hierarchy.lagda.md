# Cumulative Hierarchy

```agda
module set-theory.cumulative-hierarchy where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.transport
open import foundation.universe-levels
open import foundation.propositional-truncations
```

## Idea

The cumulative hierarchy is a model of set theory.
Instead of introducing it as a HIT, as in the HoTT Book [1, §10.5], we introduce
it's induction principle, following [2].

## Definitions

### Equal images of functions

```agda
has-smaller-image :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} →
  (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
has-smaller-image {l1} {l2} {l3} {A} {B} {X} f g =
  (a : A) → Σ B (λ b → g b ＝ f a)

have-equal-images :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} →
  (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
have-equal-images {l1} {l2} {l3} {A} {B} {X} f g =
  has-smaller-image f g × has-smaller-image g f
```

### A type is a pseudo cumulative hierarchy if it has the structure of a cumulative hierarchy, but not necessarily its induction principle.

```agda
has-cumulative-hierarchy-structure : {l : Level} → (V : UU (lsuc l)) → UU (lsuc l)
has-cumulative-hierarchy-structure {l} V =
  ( is-set V) ×
    ( Σ ({A : UU l} → (A → V) → V)
      ( λ V-set →
        ( {A B : UU l} (f : A → V) (g : B → V) →
          have-equal-images f g → V-set f ＝ V-set g)))

pseudo-cumulative-hierarchy : (l : Level) → UU (lsuc (lsuc l))
pseudo-cumulative-hierarchy (l) = Σ (UU (lsuc l)) has-cumulative-hierarchy-structure

module _
  {l : Level} (V : pseudo-cumulative-hierarchy l)
  where

  type-pseudo-cumulative-hierarchy : UU (lsuc l)
  type-pseudo-cumulative-hierarchy = pr1 V

  is-set-pseudo-cumulative-hierarchy : is-set type-pseudo-cumulative-hierarchy
  is-set-pseudo-cumulative-hierarchy = pr1 (pr2 V)

  set-pseudo-cumulative-hierarchy :
    {A : UU l}
    → (A → type-pseudo-cumulative-hierarchy)
    → type-pseudo-cumulative-hierarchy
  set-pseudo-cumulative-hierarchy = pr1 (pr2 (pr2 V))

  set-ext-pseudo-cumulative-hierarchy :
    {A B : UU l} (f : A → pr1 V) (g : B → pr1 V)
    → have-equal-images f g → set-pseudo-cumulative-hierarchy f ＝ set-pseudo-cumulative-hierarchy g
  set-ext-pseudo-cumulative-hierarchy = pr2 (pr2 (pr2 V))
```

### The induction principle of the cumulative hierarchy together with its computation rule.

```agda
module _
  {l1 : Level} (l2 : Level) (V : pseudo-cumulative-hierarchy l1)
  where
  cumulative-hierarchy-induction-principle : UU (lsuc (l1 ⊔ l2))
  cumulative-hierarchy-induction-principle =
    ( P : type-pseudo-cumulative-hierarchy V → UU l2)
    → ( (x : type-pseudo-cumulative-hierarchy V) → is-set (P x))
    → ( ρ : {A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V )
      → ((a : A) → P (f a)) → P (set-pseudo-cumulative-hierarchy V f))
    → ( {A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
        ( g : B → type-pseudo-cumulative-hierarchy V) (e : have-equal-images f g)
        → (IH₁ : (a : A) → P (f a))
        → (IH₂ : (b : B) → P (g b))
        → ((a : A) → type-trunc-Prop ( Σ B (λ b → Σ (f a ＝ g b)
                         (λ p → tr P p (IH₁ a) ＝ IH₂ b ))))
        → ((b : B) → type-trunc-Prop ( Σ A (λ a → Σ (g b ＝ f a)
                         (λ p → tr P p (IH₂ b) ＝ IH₁ a ))))
        → tr P (set-ext-pseudo-cumulative-hierarchy V f g e) (ρ f IH₁) ＝ ρ g IH₂)
    → (x : type-pseudo-cumulative-hierarchy V) → P x

  compute-cumulative-hierarchy-induction-principle :
    cumulative-hierarchy-induction-principle → UU (lsuc (l1 ⊔ l2))
  compute-cumulative-hierarchy-induction-principle IP =
    ( P : type-pseudo-cumulative-hierarchy V → UU l2)
    → ( σ : (x : type-pseudo-cumulative-hierarchy V) → is-set (P x))
    → ( ρ : {A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V )
      → ((a : A) → P (f a)) → P (set-pseudo-cumulative-hierarchy V f))
    → ( τ : {A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
        ( g : B → type-pseudo-cumulative-hierarchy V) (e : have-equal-images f g)
        → (IH₁ : (a : A) → P (f a))
        → (IH₂ : (b : B) → P (g b))
        → ((a : A) → type-trunc-Prop ( Σ B (λ b → Σ (f a ＝ g b)
                         (λ p → tr P p (IH₁ a) ＝ IH₂ b ))))
        → ((b : B) → type-trunc-Prop ( Σ A (λ a → Σ (g b ＝ f a)
                         (λ p → tr P p (IH₂ b) ＝ IH₁ a ))))
        → tr P (set-ext-pseudo-cumulative-hierarchy V f g e) (ρ f IH₁) ＝ ρ g IH₂)
    → {A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) (IH : (a : A) → P (f a))
    → IP P σ ρ τ (set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
```

## Properties

## Examples

## References

1. Institute for Advanced Study. Homotopy Type Theory: Univalent Foundations of Mathematics.
2. Tom de Jong, in collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu. https://www.cs.bham.ac.uk/~mhe/agda/UF.CumulativeHierarchy.html
