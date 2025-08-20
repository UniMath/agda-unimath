# 2-simplices

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.2-simplices
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-cones I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

### The lower simplicial triangle

```agda
subtype-lower-simplicial-triangle : subtype I2 (Δ¹ × Δ¹)
subtype-lower-simplicial-triangle (t , s) = leq-Δ¹-Prop s t

lower-simplicial-triangle = type-subtype subtype-lower-simplicial-triangle

subtype-boundary-lower-simplicial-triangle : subtype I1 (Δ¹ × Δ¹)
subtype-boundary-lower-simplicial-triangle (t , s) =
  join-Prop (Id-Δ¹-Prop 0▵ s) (join-Prop (Id-Δ¹-Prop s t) (Id-Δ¹-Prop t 1▵))
boundary-lower-simplicial-triangle =
  type-subtype subtype-boundary-lower-simplicial-triangle

◿⊆◢ :
  subtype-boundary-lower-simplicial-triangle ⊆ subtype-lower-simplicial-triangle
◿⊆◢ (x , y) =
  rec-join-Prop
    ( leq-Δ¹-Prop y x)
    ( min-leq-eq-Δ¹ ∘ inv)
    ( rec-join-Prop (leq-Δ¹-Prop y x) (leq-eq-Δ¹) (max-leq-eq-Δ¹))

inclusion-boundary-lower-simplicial-triangle :
  boundary-lower-simplicial-triangle → lower-simplicial-triangle
inclusion-boundary-lower-simplicial-triangle = tot ◿⊆◢
```

### The upper simplicial triangle

```agda
subtype-◤ : subtype I2 (Δ¹ × Δ¹)
subtype-◤ (t , s) = leq-Δ¹-Prop t s

◤ = type-subtype subtype-◤

subtype-◸ : subtype I1 (Δ¹ × Δ¹)
subtype-◸ (t , s) =
  join-Prop
    ( Id-Δ¹-Prop 0▵ t)
    ( join-Prop
      ( Id-Δ¹-Prop t s)
      ( Id-Δ¹-Prop s 1▵))

◸ = type-subtype subtype-◸

◸⊆◤ : subtype-◸ ⊆ subtype-◤
◸⊆◤ (x , y) =
  rec-join-Prop
    ( leq-Δ¹-Prop x y)
    ( min-leq-eq-Δ¹ ∘ inv)
    ( rec-join-Prop (leq-Δ¹-Prop x y) (leq-eq-Δ¹) (max-leq-eq-Δ¹))

◸→◤ : ◸ → ◤
◸→◤ = tot ◸⊆◤
```

### The standard 2-simplex

We define the standard 2-simplex as the lower simplicial triangle.

```agda
subtype-Δ² = subtype-lower-simplicial-triangle
Δ² = lower-simplicial-triangle
```

### The boundary of the standard 2-simplex

<!-- TODO remove this lemma -->

```agda
eq-image-eq-point-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
  (f : A → B) → (b : B) (x : A) → b ＝ f x → {y : A} → b ＝ f y
eq-image-eq-point-is-prop is-prop-A f b x p = p ∙ ap f (eq-is-prop is-prop-A)
```

```agda
subtype-∂Δ² : subtype I1 (Δ¹ × Δ¹)
subtype-∂Δ² = subtype-boundary-lower-simplicial-triangle

∂Δ² : UU I1
∂Δ² = boundary-lower-simplicial-triangle

∂Δ²⊆Δ² = ◿⊆◢
inclusion-∂Δ² = inclusion-boundary-lower-simplicial-triangle

rec-arrow▵-∂Δ² :
  {l : Level} {A : UU l}
  (f g h : arrow▵ A) →
  f 0▵ ＝ h 0▵ →
  f 1▵ ＝ g 0▵ →
  g 1▵ ＝ h 1▵ →
  ∂Δ² → A
rec-arrow▵-∂Δ² {A = A} f g h f0=h0 f1=g0 g1=h1 ((t , s) , u) =
  cogap-join A
    ( ( λ _ → f t) ,
      ( C) ,
      ( λ (0=s , vw) →
        cogap-join _
          ( ( λ s=t →
              eq-image-eq-point-is-prop
                ( is-prop-join-is-prop (is-set-Δ¹ s t) (is-set-Δ¹ t 1▵))
                ( C)
                ( f t)
                ( inl-join s=t)
                ( ( ap f (inv (0=s ∙ s=t)) ∙ f0=h0 ∙ ap h (0=s ∙ s=t)) ∙
                  ( inv (compute-inl-cogap-join _ s=t)))) ,
            ( ( λ t=1 →
                eq-image-eq-point-is-prop
                  ( is-prop-join-is-prop (is-set-Δ¹ s t) (is-set-Δ¹ t 1▵))
                  ( C)
                  ( f t)
                  ( inr-join t=1)
                  ( ( ap f t=1 ∙ f1=g0 ∙ ap g 0=s) ∙
                    ( inv (compute-inr-cogap-join _ t=1))))) ,
            ( λ (s=t , t=1) → ex-falso (is-nontrivial-Δ¹ (0=s ∙ s=t ∙ t=1))))
          ( vw)))
      ( u)
    where
      C =
        cogap-join A
          ( ( λ _ → h t) ,
            ( λ _ → g s) ,
            ( λ (s=t , t=1) → ap h t=1 ∙ inv (ap g (s=t ∙ t=1) ∙ g1=h1)))

rec-hom▵-∂Δ² :
  {l : Level} {A : UU l}
  {x y z : A} →
  hom▵ x y → hom▵ y z → hom▵ x z →
  ∂Δ² → A
rec-hom▵-∂Δ² f g h =
  rec-arrow▵-∂Δ²
    ( arrow-hom▵ f)
    ( arrow-hom▵ g)
    ( arrow-hom▵ h)
    ( eq-source-source-hom▵ f h)
    ( eq-source-target-hom▵ f g)
    ( eq-target-target-hom▵ g h)
```

### The 2-simplex as a directed cone

```agda
directed-cone-Δ² : UU I1
directed-cone-Δ² = directed-cone Δ¹
```
