# The inner 2-horn

```agda
module simplicial-type-theory.inner-2-horn where
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
open import foundation.retractions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.2-simplices
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-spines
open import simplicial-type-theory.standard-simplices

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The {{#concept "inner 2-horn" Disambiguation="simplicial type"}} $Λ²₁$, also
called the _2-1-horn_, is the universal type generated from the data of two
directed edges such that the source of the first is the target of the second,
pictorially:

```text
  0 ----> 1 ----> 2.
```

The inner 2-horn has multiple defining properties:

1. The inner 2-horn is the subtype of the standard
   [2-simplex](simplicial-type-theory.2-simplices.md) defined by

   ```text
   Λ²₁ = {(x , y) ∈ Δ¹ × Δ¹ | (y ＝ 0₂) ∨ (x ＝ 1₂)} ⊆ Δ².
   ```

2. The inner 2-horn is the pushout

   ```text
            0₂
        1 -----> Δ¹
        |        |
     1₂ |        |
        ∨      ⌜ ∨
        Δ¹ -----> Λ²₁.
   ```

3. The inner 2-horn is the 2-[spine](simplicial-type-theory.spines.md).

## Definitions

### The inner 2-horn as a subtype of the lower simplicial triangle

> TODO: replace with `subtype-spine 2`

```agda
subtype-inner-two-horn : subtype lzero (Δ¹ × Δ¹)
subtype-inner-two-horn (x , y) =
  join-Prop (Id-Prop Δ¹-Set y 0₂) (Id-Prop Δ¹-Set x 1₂)

inner-two-horn : UU
inner-two-horn = type-subtype subtype-inner-two-horn

inl-inner-two-horn : Δ¹ → inner-two-horn
inl-inner-two-horn t = ((t , 0₂) , inl-join refl)

inr-inner-two-horn : Δ¹ → inner-two-horn
inr-inner-two-horn s = ((1₂ , s) , inr-join refl)
```

```agda
Λ²₁ : UU
Λ²₁ = inner-two-horn
```

### The cogap map of the inner 2-horn as a subtype of the lower simplicial triangle

```agda
module _
  {l : Level} {A : UU l} (f g : Δ¹ → A) (p : f 1₂ ＝ g 0₂)
  where

  cogap-inner-two-horn : inner-two-horn → A
  cogap-inner-two-horn ((x , y) , H) =
    cogap-join A
      ( ( λ y=0 → f x) ,
        ( λ x=1 → g y) ,
        ( λ (y=0 , x=1) → ap f x=1 ∙ p ∙ ap g (inv y=0)))
      ( H)
```

### The inner 2-horn as a pushout

```text
         0₂
     1 -----> Δ¹
     |        |
  1₂ |        |
     ∨      ⌜ ∨
     Δ¹ -----> Λ²₁.
```

```agda
pushout-inner-two-horn : UU
pushout-inner-two-horn = pushout (point 1₂) (point 0₂)

inl-pushout-inner-two-horn : Δ¹ → pushout-inner-two-horn
inl-pushout-inner-two-horn = inl-pushout (point 1₂) (point 0₂)

inr-pushout-inner-two-horn : Δ¹ → pushout-inner-two-horn
inr-pushout-inner-two-horn = inr-pushout (point 1₂) (point 0₂)
```

## Properties

### The inner 2-horn is a set

```agda
is-set-inner-two-horn : is-set inner-two-horn
is-set-inner-two-horn =
  is-set-type-subtype subtype-inner-two-horn (is-set-product is-set-Δ¹ is-set-Δ¹)
```

### The canonical map from the inner 2-horn as a pushout to the inner 2-horn as a subtype of the square

```agda
map-inner-two-horn-pushout-inner-two-horn :
  pushout-inner-two-horn → inner-two-horn
map-inner-two-horn-pushout-inner-two-horn =
  cogap
    ( point 1₂)
    ( point 0₂)
    ( inl-inner-two-horn ,
      inr-inner-two-horn ,
      λ _ → eq-type-subtype subtype-inner-two-horn refl)

map-pushout-inner-two-horn-inner-two-horn :
  inner-two-horn → pushout-inner-two-horn
map-pushout-inner-two-horn-inner-two-horn =
  cogap-inner-two-horn
    ( inl-pushout-inner-two-horn)
    ( inr-pushout-inner-two-horn)
    ( glue-pushout (point 1₂) (point 0₂) star)
```

### The inclusion of the 2-horn into the 2-simplex

```agda
leq-subtype-two-simplex-inner-two-horn :
  subtype-inner-two-horn ⊆ subtype-lower-simplicial-triangle
leq-subtype-two-simplex-inner-two-horn (x , y) =
  cogap-join
    ( y ≤-Δ¹ x)
    ( min-leq-eq-Δ¹ , max-leq-eq-Δ¹ , λ _ → eq-is-prop is-prop-leq-Δ¹)

inclusion-Δ²-Λ²₁ : Λ²₁ → Δ²
inclusion-Δ²-Λ²₁ = tot leq-subtype-two-simplex-inner-two-horn
```
