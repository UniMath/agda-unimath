# Enumerations by fixed points of the maybe-monad

```agda
module set-theory.enumerations-fixed-points-maybe where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.type-arithmetic-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coalgebras-maybe
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import set-theory.decidable-subprojections
open import set-theory.enumerations

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a type `α`, recall that an `α`-[enumeration](set-theory.enumerations.md)
on another type `X` is a [surjection](foundation.surjective-maps.md)
`α ↠ Maybe X`. When `α` is a
[fixed point](foundation.fixed-points-endofunctions.md), then this condition is
equivalent to the following

1. There is a surjection `α ↠ X` or `X` is [empty](foundation.empty-types.md).
2. There is a [decidable subtype](foundation.decidable-subtypes.md) `β` of `α`
   and a surjection `β ↠ X`.

## Definitions

### Enumerability as decidable subprojection

```agda
module _
  {l1 l2 : Level} (l3 : Level) (α : UU l1) (X : UU l2)
  where

  is-enumerable-Prop' : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-enumerable-Prop' = is-decidable-subprojection-Prop l3 α X

  is-enumerable' : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-enumerable' = type-Prop is-enumerable-Prop'

  is-prop-is-enumerable' : is-prop is-enumerable'
  is-prop-is-enumerable' = is-prop-type-Prop is-enumerable-Prop'
```

## Properties

### Directly α-enumerable types are α-enumerable

```agda
module _
  {l1 l2 : Level} {α : UU l1} {X : UU l2}
  where

  abstract
    is-enumerable-is-directly-enumerable :
      (α ↠ Maybe α) → is-directly-enumerable α X → is-enumerable α X
    is-enumerable-is-directly-enumerable μ H =
      apply-universal-property-trunc-Prop H
        ( is-enumerable-Prop α X)
        ( λ (f , F) →
          unit-trunc-Prop
            ( comp-surjection
              ( surjection-map-surjection-Maybe (f , F))
              ( μ)))
```

### The two definitions of α-enumeration are equivalent

First, we will prove `enumeration α X → decidable-subprojection l2 α X`.

```agda
module _
  {l1 l2 : Level} {α : UU l1} {X : UU l2}
  where

  is-enumerable'-is-enumerable :
    is-enumerable α X → is-enumerable' l2 α X
  is-enumerable'-is-enumerable H =
    apply-universal-property-trunc-Prop H
      ( is-enumerable-Prop' l2 α X)
      ( unit-trunc-Prop ∘ decidable-subprojection-enumeration)
```

Second, we prove `decidable-subprojection l2 α X → enumeration α X`, assuming
that α is a fixed point of the `Maybe` monad.

```agda
cases-map-decidable-subtype :
  {l1 l2 : Level} (α : UU l1) (X : UU l2) →
  ( P : decidable-subtype l2 α) →
  ( f : type-decidable-subtype P → X) →
  ( (n : α) → is-decidable (pr1 (P n)) → Maybe X)
cases-map-decidable-subtype α X P f n (inl x) = inl (f (n , x))
cases-map-decidable-subtype α X P f n (inr x) = inr star

map-Maybe-decidable-subprojection :
  {l1 l2 : Level} {α : UU l1} {X : UU l2} →
  ( P : decidable-subtype l2 α) →
  ( f : type-decidable-subtype P → X) →
  Maybe α → Maybe X
map-Maybe-decidable-subprojection {α = α} {X = X} P f (inl n) =
  cases-map-decidable-subtype α X P f n (pr2 (pr2 (P n)))
map-Maybe-decidable-subprojection P f (inr star) = inr star

module _
  {l1 l2 : Level} (α : UU l1)
  (μ : Maybe α retract-of α)
  (X : UU l2)
  (P : decidable-subtype l2 α)
  (f : type-decidable-subtype P → X)
  where

  map-enumeration-decidable-subprojection : α → Maybe X
  map-enumeration-decidable-subprojection =
    map-Maybe-decidable-subprojection P f ∘ map-retraction-retract μ

  abstract
    is-surjective-map-enumeration-decidable-subprojection :
      ( is-surjective f) →
      ( is-surjective map-enumeration-decidable-subprojection)
    is-surjective-map-enumeration-decidable-subprojection H (inl x) =
      apply-universal-property-trunc-Prop (H x)
        ( trunc-Prop (fiber map-enumeration-decidable-subprojection (inl x)))
        ( λ where
          ( ( n , s) , refl) →
            unit-trunc-Prop
              ( inclusion-retract μ (inl n) ,
                ( ap
                  ( map-Maybe-decidable-subprojection P f)
                  ( is-retraction-map-retraction-retract μ (inl n))) ∙
                ( ap
                  ( cases-map-decidable-subtype α X P f n)
                  ( pr1
                    ( is-prop-is-decidable (pr1 (pr2 (P n)))
                      ( pr2 (pr2 (P n)))
                      ( inl s))))))
    is-surjective-map-enumeration-decidable-subprojection H (inr star) =
      unit-trunc-Prop
        ( inclusion-retract μ (inr star) ,
          ap
            ( map-Maybe-decidable-subprojection P f)
            ( is-retraction-map-retraction-retract μ (inr star)))

module _
  {l1 l2 : Level} (α : UU l1)
  ( μ : Maybe α retract-of α)
  (X : UU l2)
  where

  enumeration-decidable-subprojection :
    decidable-subprojection l2 α X → enumeration α X
  enumeration-decidable-subprojection (P , (f , H)) =
    ( map-enumeration-decidable-subprojection α μ X P f) ,
    ( is-surjective-map-enumeration-decidable-subprojection α μ X P f H)

  is-enumerable-is-enumerable' :
    is-enumerable' l2 α X → is-enumerable α X
  is-enumerable-is-enumerable' H =
    apply-universal-property-trunc-Prop H
      ( is-enumerable-Prop α X)
      ( λ D → unit-trunc-Prop (enumeration-decidable-subprojection D))
```

### The type α is α-enumerable when α is a `Maybe`-fixed point

```agda
module _
  {l1 : Level} (α : UU l1) (μ : α ↠ Maybe α)
  where

  abstract
    is-enumerable-fixed-point-Maybe : is-enumerable α α
    is-enumerable-fixed-point-Maybe = unit-trunc-Prop μ
```

### The canonical map `ℕ → α` at a `Maybe`-fixed point

```agda
module _
  {l1 : Level} (α : UU l1) (μ : α ≃ Maybe α)
  where

  zero-fixed-point-Maybe-equiv : α
  zero-fixed-point-Maybe-equiv = map-inv-equiv μ (inr star)

  succ-fixed-point-Maybe-equiv : α → α
  succ-fixed-point-Maybe-equiv = map-inv-equiv μ ∘ inl

  map-ℕ-fixed-point-Maybe-equiv : ℕ → α
  map-ℕ-fixed-point-Maybe-equiv zero-ℕ = zero-fixed-point-Maybe-equiv
  map-ℕ-fixed-point-Maybe-equiv (succ-ℕ n) =
    succ-fixed-point-Maybe-equiv (map-ℕ-fixed-point-Maybe-equiv n)

  abstract
    is-injective-succ-fixed-point-Maybe-equiv :
      is-injective succ-fixed-point-Maybe-equiv
    is-injective-succ-fixed-point-Maybe-equiv {x} {y} p =
      is-injective-inl
        ( ( inv (is-section-map-inv-equiv μ (inl x))) ∙
          ( ap (map-equiv μ) p) ∙
          ( is-section-map-inv-equiv μ (inl y)))

    neq-zero-succ-fixed-point-Maybe-equiv :
      (x : α) → succ-fixed-point-Maybe-equiv x ≠ zero-fixed-point-Maybe-equiv
    neq-zero-succ-fixed-point-Maybe-equiv x p =
      is-empty-eq-coproduct-inl-inr
        x
        star
        ( ( inv (is-section-map-inv-equiv μ (inl x))) ∙
          ( ap (map-equiv μ) p) ∙
          ( is-section-map-inv-equiv μ (inr star)))

  is-injective-map-ℕ-fixed-point-Maybe-equiv :
    is-injective map-ℕ-fixed-point-Maybe-equiv
  is-injective-map-ℕ-fixed-point-Maybe-equiv {zero-ℕ} {zero-ℕ} p = refl
  is-injective-map-ℕ-fixed-point-Maybe-equiv {zero-ℕ} {succ-ℕ y} p =
    ex-falso
      ( neq-zero-succ-fixed-point-Maybe-equiv
        ( map-ℕ-fixed-point-Maybe-equiv y)
        ( inv p))
  is-injective-map-ℕ-fixed-point-Maybe-equiv {succ-ℕ x} {zero-ℕ} p =
    ex-falso
      ( neq-zero-succ-fixed-point-Maybe-equiv
        ( map-ℕ-fixed-point-Maybe-equiv x)
        ( p))
  is-injective-map-ℕ-fixed-point-Maybe-equiv {succ-ℕ x} {succ-ℕ y} p =
    ap succ-ℕ
      ( is-injective-map-ℕ-fixed-point-Maybe-equiv
        ( is-injective-succ-fixed-point-Maybe-equiv p))
```

### Enumerable types are closed under coproducts

```agda
module _
  {l1 l2 l3 : Level}
  (α : UU l1) (e : α ↠ (α + α)) (X : UU l2) (Y : UU l3)
  where

  is-enumerable-coproduct :
    is-enumerable α X → is-enumerable α Y → is-enumerable α (X + Y)
  is-enumerable-coproduct H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-enumerable-Prop α (X + Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( comp-surjection
            ( surjection-maybe-coproduct)
            ( comp-surjection
              ( surjection-coproduct h h')
              ( e)))))
```

### Enumerable types are closed under products

```agda
module _
  {l1 l2 l3 : Level}
  (α : UU l1) (e : α ↠ (α × α)) (X : UU l2) (Y : UU l3)
  where

  is-enumerable-product :
    is-enumerable α X → is-enumerable α Y → is-enumerable α (X × Y)
  is-enumerable-product H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-enumerable-Prop α (X × Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( comp-surjection
            ( surjection-maybe-product)
            ( comp-surjection
              ( surjection-product h h')
              ( e)))))
```
