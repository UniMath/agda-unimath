# 2-simplices

```agda
module simplicial-type-theory.2-simplices where
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

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-cones

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

<!-- TODO remove this -->

```agda
eq-image-eq-point-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
  (f : A → B) → (b : B) (x : A) → b ＝ f x → {y : A} → b ＝ f y
eq-image-eq-point-is-prop is-prop-A f b x p = p ∙ ap f (eq-is-prop is-prop-A)
```

### The lower simplicial triangle

```agda
subtype-lower-simplicial-triangle : subtype lzero (𝟚 × 𝟚)
subtype-lower-simplicial-triangle (t , s) = leq-𝟚-Prop s t

lower-simplicial-triangle = type-subtype subtype-lower-simplicial-triangle

subtype-boundary-lower-simplicial-triangle : subtype lzero (𝟚 × 𝟚)
subtype-boundary-lower-simplicial-triangle (t , s) =
  join-Prop (Id-𝟚-Prop 0₂ s) (join-Prop (Id-𝟚-Prop s t) (Id-𝟚-Prop t 1₂))
boundary-lower-simplicial-triangle =
  type-subtype subtype-boundary-lower-simplicial-triangle

◿⊆◢ :
  subtype-boundary-lower-simplicial-triangle ⊆ subtype-lower-simplicial-triangle
◿⊆◢ (x , y) =
  rec-join-Prop
    ( leq-𝟚-Prop y x)
    ( min-leq-eq-𝟚 ∘ inv)
    ( rec-join-Prop (leq-𝟚-Prop y x) (leq-eq-𝟚) (max-leq-eq-𝟚))

inclusion-boundary-lower-simplicial-triangle :
  boundary-lower-simplicial-triangle → lower-simplicial-triangle
inclusion-boundary-lower-simplicial-triangle = tot ◿⊆◢
```

### The upper simplicial triangle

```agda
subtype-◤ : subtype lzero (𝟚 × 𝟚)
subtype-◤ (t , s) = leq-𝟚-Prop t s

◤ = type-subtype subtype-◤

subtype-◸ : subtype lzero (𝟚 × 𝟚)
subtype-◸ (t , s) =
  join-Prop
    ( Id-𝟚-Prop 0₂ t)
    ( join-Prop
      ( Id-𝟚-Prop t s)
      ( Id-𝟚-Prop s 1₂))

◸ = type-subtype subtype-◸

◸⊆◤ : subtype-◸ ⊆ subtype-◤
◸⊆◤ (x , y) =
  rec-join-Prop
    ( leq-𝟚-Prop x y)
    ( min-leq-eq-𝟚 ∘ inv)
    ( rec-join-Prop (leq-𝟚-Prop x y) (leq-eq-𝟚) (max-leq-eq-𝟚))

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

```agda
subtype-∂Δ² : subtype lzero (𝟚 × 𝟚)
subtype-∂Δ² = subtype-boundary-lower-simplicial-triangle

∂Δ² : UU lzero
∂Δ² = boundary-lower-simplicial-triangle

∂Δ²⊆Δ² = ◿⊆◢
inclusion-∂Δ² = inclusion-boundary-lower-simplicial-triangle

rec-simplicial-arrow-∂Δ² :
  {l : Level} {A : UU l}
  (f g h : simplicial-arrow A) →
  f 0₂ ＝ h 0₂ →
  f 1₂ ＝ g 0₂ →
  g 1₂ ＝ h 1₂ →
  ∂Δ² → A
rec-simplicial-arrow-∂Δ² {A = A} f g h f0=h0 f1=g0 g1=h1 ((t , s) , u) =
  cogap-join A
    ( ( λ _ → f t) ,
      ( C) ,
      ( λ (0=s , vw) →
        cogap-join _
          ( ( λ s=t →
              eq-image-eq-point-is-prop
                ( is-prop-join-is-prop (is-set-𝟚 s t) (is-set-𝟚 t 1₂))
                ( C)
                ( f t)
                ( inl-join s=t)
                ( ( ap f (inv (0=s ∙ s=t)) ∙ f0=h0 ∙ ap h (0=s ∙ s=t)) ∙
                  ( inv (compute-inl-cogap-join _ s=t)))) ,
            ( ( λ t=1 →
                eq-image-eq-point-is-prop
                  ( is-prop-join-is-prop (is-set-𝟚 s t) (is-set-𝟚 t 1₂))
                  ( C)
                  ( f t)
                  ( inr-join t=1)
                  ( ( ap f t=1 ∙ f1=g0 ∙ ap g 0=s) ∙
                    ( inv (compute-inr-cogap-join _ t=1))))) ,
            ( λ (s=t , t=1) → ex-falso (is-nontrivial-𝟚 (0=s ∙ s=t ∙ t=1))))
          ( vw)))
      ( u)
    where
      C =
        cogap-join A
          ( ( λ _ → h t) ,
            ( λ _ → g s) ,
            ( λ (s=t , t=1) → ap h t=1 ∙ inv (ap g (s=t ∙ t=1) ∙ g1=h1)))

rec-simplicial-hom-∂Δ² :
  {l : Level} {A : UU l}
  {x y z : A} →
  simplicial-hom x y → simplicial-hom y z → simplicial-hom x z →
  ∂Δ² → A
rec-simplicial-hom-∂Δ² f g h =
  rec-simplicial-arrow-∂Δ²
    ( simplicial-arrow-simplicial-hom f)
    ( simplicial-arrow-simplicial-hom g)
    ( simplicial-arrow-simplicial-hom h)
    ( eq-source-source-simplicial-hom f h)
    ( eq-source-target-simplicial-hom f g)
    ( eq-target-target-simplicial-hom g h)
```

### The 2-simplex as a simplicial cone

```agda
simplicial-cone-Δ² : UU lzero
simplicial-cone-Δ² = simplicial-cone 𝟚
```
