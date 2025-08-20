# The inner 2-horn

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.inner-2-horn
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
open import foundation.retractions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.2-simplices I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I
open import simplicial-type-theory.standard-simplices I
open import simplicial-type-theory.standard-spines I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The {{#concept "inner 2-horn" Disambiguation="simplicial type" Agda=Λ²₁}} $Λ²₁$,
also called the _2-1-horn_, is the universal type generated from the data of two
directed edges such that the source of the first is the target of the second,
pictorially:

```text
  0 ----> 1 ----> 2.
```

The inner 2-horn has multiple defining properties:

1. The inner 2-horn is the subtype of the standard
   [2-simplex](simplicial-type-theory.2-simplices.md) defined by

   ```text
   Λ²₁ = {(x , y) ∈ Δ¹ × Δ¹ | (y ＝ 0▵) ∨ (x ＝ 1▵)} ⊆ Δ².
   ```

2. The inner 2-horn is the pushout

   ```text
            0▵
        1 -----> Δ¹
        |        |
     1▵ |        |
        ∨      ⌜ ∨
        Δ¹ ----> Λ²₁.
   ```

3. The inner 2-horn is the 2-[spine](simplicial-type-theory.standard-spines.md).

## Definitions

### The inner 2-horn as a subtype of the directed square

```agda
subtype-Λ²₁ : subtype I1 (Δ¹ × Δ¹)
subtype-Λ²₁ (x , y) =
  join-Prop (Id-Prop Δ¹-Set y 0▵) (Id-Prop Δ¹-Set x 1▵)

inner-two-horn : UU I1
inner-two-horn = type-subtype subtype-Λ²₁

Λ²₁ : UU I1
Λ²₁ = inner-two-horn

inl-Λ²₁ : Δ¹ → Λ²₁
inl-Λ²₁ t = ((t , 0▵) , inl-join refl)

inr-Λ²₁ : Δ¹ → Λ²₁
inr-Λ²₁ s = ((1▵ , s) , inr-join refl)
```

### The cogap map of the inner 2-horn as a subtype of the directed square

```agda
module _
  {l : Level} {A : UU l} (f g : Δ¹ → A) (p : f 1▵ ＝ g 0▵)
  where

  cogap-Λ²₁ : inner-two-horn → A
  cogap-Λ²₁ ((x , y) , H) =
    cogap-join A
      ( ( λ y=0 → f x) ,
        ( λ x=1 → g y) ,
        ( λ (y=0 , x=1) → ap f x=1 ∙ p ∙ ap g (inv y=0)))
      ( H)
```

### The inner 2-horn as a pushout

```text
         0▵
     1 -----> Δ¹
     |        |
  1▵ |        |
     ∨      ⌜ ∨
     Δ¹ ----> Λ²₁.
```

```agda
pushout-Λ²₁ : UU I1
pushout-Λ²₁ = pushout (point 1▵) (point 0▵)

inl-pushout-Λ²₁ : Δ¹ → pushout-Λ²₁
inl-pushout-Λ²₁ = inl-pushout (point 1▵) (point 0▵)

inr-pushout-Λ²₁ : Δ¹ → pushout-Λ²₁
inr-pushout-Λ²₁ = inr-pushout (point 1▵) (point 0▵)
```

## Properties

### The inner 2-horn is a set

```agda
is-set-Λ²₁ : is-set Λ²₁
is-set-Λ²₁ =
  is-set-type-subtype subtype-Λ²₁ (is-set-product is-set-Δ¹ is-set-Δ¹)
```

### The canonical map from the inner 2-horn as a pushout to the inner 2-horn as a subtype of the directed square

```agda
map-inner-two-horn-pushout-Λ²₁ : pushout-Λ²₁ → Λ²₁
map-inner-two-horn-pushout-Λ²₁ =
  cogap
    ( point 1▵)
    ( point 0▵)
    ( inl-Λ²₁ , inr-Λ²₁ , λ _ → eq-type-subtype subtype-Λ²₁ refl)

map-pushout-inner-two-horn-Λ²₁ : Λ²₁ → pushout-Λ²₁
map-pushout-inner-two-horn-Λ²₁ =
  cogap-Λ²₁
    ( inl-pushout-Λ²₁)
    ( inr-pushout-Λ²₁)
    ( glue-pushout (point 1▵) (point 0▵) star)
```

### The inclusion of the 2-horn into the 2-simplex

```agda
leq-subtype-two-simplex-Λ²₁ : subtype-Λ²₁ ⊆ subtype-Δ²
leq-subtype-two-simplex-Λ²₁ (x , y) =
  cogap-join
    ( y ≤-Δ¹ x)
    ( min-leq-eq-Δ¹ , max-leq-eq-Δ¹ , λ _ → eq-is-prop is-prop-leq-Δ¹)

inclusion-Δ²-Λ²₁ : Λ²₁ → Δ²
inclusion-Δ²-Λ²₁ = tot leq-subtype-two-simplex-Λ²₁
```
