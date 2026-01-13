# Strictly increasing endomaps on the real numbers

```agda
module real-numbers.strictly-increasing-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.strict-order-preserving-maps
open import order-theory.subtypes-strict-preorders

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.increasing-endomaps-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A function `f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves is
{{#concept "strictly increasing" Disambiguation="function from ℝ to ℝ" Agda=is-strictly-increasing-endomap-ℝ}}
if for all `x < y`, `f x < f y`.

Several arguments on this page are due to
[Mark Saving](https://math.stackexchange.com/users/798694/mark-saving) in this
Mathematics Stack Exchange answer: <https://math.stackexchange.com/q/5107860>.

## Definition

```agda
is-strictly-increasing-prop-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-strictly-increasing-prop-endomap-ℝ {l1} {l2} =
  preserves-strict-order-prop-map-Strict-Preorder
    ( strict-preorder-ℝ l1)
    ( strict-preorder-ℝ l2)

is-strictly-increasing-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-strictly-increasing-endomap-ℝ f =
  type-Prop (is-strictly-increasing-prop-endomap-ℝ f)

is-strictly-increasing-on-subset-endomap-ℝ :
  {l1 l2 l3 : Level} → (ℝ l1 → ℝ l2) → subset-ℝ l3 l1 → UU (lsuc l1 ⊔ l2 ⊔ l3)
is-strictly-increasing-on-subset-endomap-ℝ {l1} {l2} f S =
  preserves-strict-order-map-Strict-Preorder
    ( strict-preorder-subtype-Strict-Preorder (strict-preorder-ℝ l1) S)
    ( strict-preorder-ℝ l2)
    ( f ∘ inclusion-subset-ℝ S)
```

## Properties

### A strictly increasing function is increasing

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  abstract
    is-increasing-is-strictly-increasing-endomap-ℝ :
      is-strictly-increasing-endomap-ℝ f → is-increasing-endomap-ℝ f
    is-increasing-is-strictly-increasing-endomap-ℝ H =
      is-increasing-is-increasing-on-strict-inequalities-endomap-ℝ
        ( f)
        ( λ x y x<y → leq-le-ℝ (H x y x<y))
```

### Strictly increasing maps reflect inequality

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (H : is-strictly-increasing-endomap-ℝ f)
  where

  abstract
    reflects-leq-is-strictly-increasing-endomap-ℝ :
      (x y : ℝ l1) →
      leq-ℝ (f x) (f y) →
      leq-ℝ x y
    reflects-leq-is-strictly-increasing-endomap-ℝ x y fx≤fy =
      leq-not-le-ℝ y x
        ( λ x<y → not-le-leq-ℝ _ _ fx≤fy (H y x x<y))
```

### Strictly increasing maps are embeddings

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (H : is-strictly-increasing-endomap-ℝ f)
  where

  abstract
    is-injective-is-strictly-increasing-endomap-ℝ : is-injective f
    is-injective-is-strictly-increasing-endomap-ℝ {a} {b} fa=fb =
      antisymmetric-leq-ℝ a b
        ( reflects-leq-is-strictly-increasing-endomap-ℝ
          ( f)
          ( H)
          ( a)
          ( b)
          ( leq-eq-ℝ fa=fb))
        ( reflects-leq-is-strictly-increasing-endomap-ℝ
          ( f)
          ( H)
          ( b)
          ( a)
          ( leq-eq-ℝ (inv fa=fb)))

    is-emb-is-strictly-increasing-endomap-ℝ : is-emb f
    is-emb-is-strictly-increasing-endomap-ℝ =
      is-emb-is-injective
        ( is-set-ℝ l2)
        ( is-injective-is-strictly-increasing-endomap-ℝ)
```

### The composition of strictly increasing functions is strictly increasing

```agda
module _
  {l1 l2 l3 : Level}
  (f : ℝ l2 → ℝ l3)
  (g : ℝ l1 → ℝ l2)
  where

  abstract
    is-strictly-increasing-endomap-comp-ℝ :
      is-strictly-increasing-endomap-ℝ f →
      is-strictly-increasing-endomap-ℝ g →
      is-strictly-increasing-endomap-ℝ (f ∘ g)
    is-strictly-increasing-comp-is-strictly-increasing-endomap-ℝ H K x y x<y =
      H (g x) (g y) (K x y x<y)
```
