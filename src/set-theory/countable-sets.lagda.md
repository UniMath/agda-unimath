# Countable sets

```agda
module set-theory.countable-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-subtypes
open import foundation.equality-coproduct-types
open import foundation.existential-quantification
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.shifting-sequences
open import foundation.surjective-maps
open import foundation.type-arithmetic-natural-numbers
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-pair-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.identity-types
open import foundation-core.negation
```

</details>

## Idea

A set `X` is said to be countable if there is a surjective map `f : ℕ → X + 1`.
Equivalently, a set `X` is countable if there is a surjective map
`f : type-decidable-subset P → X` for some decidable subset `P` of `X`.

## Definition

### First definition of countable types

```agda
is-countable-Prop : {l : Level} → Set l → Prop l
is-countable-Prop X = ∃-Prop (ℕ → Maybe (type-Set X)) is-surjective

is-countable : {l : Level} → Set l → UU l
is-countable X = type-Prop (is-countable-Prop X)

is-prop-is-countable :
  {l : Level} (X : Set l) → is-prop (is-countable X)
is-prop-is-countable X = is-prop-type-Prop (is-countable-Prop X)
```

### Second definition of countable types

```agda
is-countable-Prop' : {l : Level} → Set l → Prop (lsuc lzero ⊔ l)
is-countable-Prop' X =
  ∃-Prop
    ( decidable-subtype lzero ℕ)
    ( λ P → type-decidable-subtype P ↠ type-Set X)

is-countable' : {l : Level} → Set l → UU (lsuc lzero ⊔ l)
is-countable' X = type-Prop (is-countable-Prop' X)

is-prop-is-countable' :
  {l : Level} (X : Set l) → is-prop (is-countable' X)
is-prop-is-countable' X = is-prop-type-Prop (is-countable-Prop' X)
```

### Third definition of countable types

If a set `X` is inhabited, then it is countable if and only if there is a
surjective map `f : ℕ → X`. Let us call the latter as "directly countable".

```agda
is-directly-countable-Prop : {l : Level} → Set l → Prop l
is-directly-countable-Prop X =
  ∃-Prop (ℕ → type-Set X) is-surjective

is-directly-countable : {l : Level} → Set l → UU l
is-directly-countable X = type-Prop (is-directly-countable-Prop X)

is-prop-is-directly-countable :
  {l : Level} (X : Set l) → is-prop (is-directly-countable X)
is-prop-is-directly-countable X = is-prop-type-Prop
  (is-directly-countable-Prop X)

module _
  {l : Level} (X : Set l) (a : type-Set X)
  where

  is-directly-countable-is-countable :
    is-countable X → is-directly-countable X
  is-directly-countable-is-countable H =
    apply-universal-property-trunc-Prop H
      ( is-directly-countable-Prop X)
      ( λ P →
        unit-trunc-Prop
          ( pair
            ( f ∘ (pr1 P))
            ( is-surjective-comp is-surjective-f (pr2 P))))
    where
     f : Maybe (type-Set X) → type-Set X
     f (inl x) = x
     f (inr star) = a

     is-surjective-f : is-surjective f
     is-surjective-f x = unit-trunc-Prop (pair (inl x) refl)

  is-countable-is-directly-countable :
    is-directly-countable X → is-countable X
  is-countable-is-directly-countable H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop X)
      ( λ P →
        unit-trunc-Prop
          ( pair
            ( λ {
              zero-ℕ → inr star ;
              (succ-ℕ n) → inl ((shift-ℕ a (pr1 P)) n)})
            ( λ {
              (inl x) →
                apply-universal-property-trunc-Prop (pr2 P x)
                  ( trunc-Prop (fib _ (inl x)))
                  ( λ { (pair n p) →
                    unit-trunc-Prop
                      ( pair (succ-ℕ (succ-ℕ n)) (ap inl p))}) ;
              (inr star) → unit-trunc-Prop (pair zero-ℕ refl)})))
```

## Properties

### The two definitions of countability are equivalent

## Useful Lemmas

There is a surjection from `(Maybe A + Maybe B)` to `Maybe (A + B)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-maybe-coprod : (Maybe A + Maybe B) → Maybe (A + B)
  map-maybe-coprod (inl (inl x)) = inl (inl x)
  map-maybe-coprod (inl (inr star)) = inr star
  map-maybe-coprod (inr (inl x)) = inl (inr x)
  map-maybe-coprod (inr (inr star)) = inr star

  is-surjective-map-maybe-coprod : is-surjective map-maybe-coprod
  is-surjective-map-maybe-coprod (inl (inl x)) =
    unit-trunc-Prop ((inl (inl x)) , refl)
  is-surjective-map-maybe-coprod (inl (inr x)) =
    unit-trunc-Prop ((inr (inl x)) , refl)
  is-surjective-map-maybe-coprod (inr star) =
    unit-trunc-Prop ((inl (inr star)) , refl)
```

There is a surjection from `(Maybe A × Maybe B)` to `Maybe (A × B)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-maybe-prod : (Maybe A × Maybe B) → Maybe (A × B)
  map-maybe-prod (inl a , inl b) = inl (a , b)
  map-maybe-prod (inl a , inr star) = inr star
  map-maybe-prod (inr star , inl b) = inr star
  map-maybe-prod (inr star , inr star) = inr star

  is-surjective-map-maybe-prod : is-surjective map-maybe-prod
  is-surjective-map-maybe-prod (inl (a , b)) =
    unit-trunc-Prop ((inl a , inl b) , refl)
  is-surjective-map-maybe-prod (inr star) =
    unit-trunc-Prop ((inr star , inr star) , refl)
```

## Examples

The set of natural numbers ℕ is itself countable.

```agda
is-countable-ℕ : is-countable ℕ-Set
is-countable-ℕ =
  unit-trunc-Prop
    ( pair
      ( λ { zero-ℕ → inr star ; (succ-ℕ n) → inl n})
      ( λ {
        (inl n) → unit-trunc-Prop (pair (succ-ℕ n) refl) ;
        (inr star) → unit-trunc-Prop (pair zero-ℕ refl)}))
```

The coproduct ℕ + ℕ is countable.

```agda
is-countable-ℕ+ℕ : is-countable (coprod-Set ℕ-Set ℕ-Set)
is-countable-ℕ+ℕ =
  is-countable-is-directly-countable
    ( coprod-Set ℕ-Set ℕ-Set)
    ( inl zero-ℕ)
    ( unit-trunc-Prop
      ( map-ℕ-to-ℕ+ℕ ,
      ( is-surjective-is-equiv
        ( is-equiv-map-ℕ-to-ℕ+ℕ))))
```

The integers type `ℤ` is countable.

```agda
is-countable-ℤ : is-countable (ℤ-Set)
is-countable-ℤ =
  is-countable-is-directly-countable
    ( ℤ-Set)
    ( zero-ℤ)
    ( unit-trunc-Prop
      ( map-ℕ-to-ℤ , is-surjective-is-equiv (is-equiv-map-ℕ-to-ℤ)))
```

If `X` and `Y` are countable sets, then so is their coproduct `X + Y`.

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-countable-coprod :
    is-countable X → is-countable Y → is-countable (coprod-Set X Y)
  is-countable-coprod H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-countable-Prop (coprod-Set X Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( pair
            ( map-maybe-coprod ∘
              ( map-coprod (pr1 h) (pr1 h') ∘ map-ℕ-to-ℕ+ℕ))
            ( is-surjective-comp
              ( is-surjective-map-maybe-coprod)
              ( is-surjective-comp
                ( is-surjective-map-coprod (pr2 h) (pr2 h'))
                ( is-surjective-is-equiv (is-equiv-map-ℕ-to-ℕ+ℕ)))))))
```

The coproduct ℕ + ℕ is countable.

```agda
is-countable-ℕ×ℕ : is-countable (prod-Set ℕ-Set ℕ-Set)
is-countable-ℕ×ℕ =
  is-countable-is-directly-countable
    ( prod-Set ℕ-Set ℕ-Set)
    ( (0 , 0))
    ( unit-trunc-Prop
      ( map-ℕ-to-ℕ×ℕ ,
      ( is-surjective-is-equiv
        ( is-equiv-map-ℕ-to-ℕ×ℕ))))
```

If `X` and `Y` are countable sets, then so is their coproduct `X × Y`.

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-countable-prod :
    is-countable X → is-countable Y → is-countable (prod-Set X Y)
  is-countable-prod H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-countable-Prop (prod-Set X Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( pair
            ( map-maybe-prod ∘
              ( map-prod (pr1 h) (pr1 h') ∘ map-ℕ-to-ℕ×ℕ))
            ( is-surjective-comp
              ( is-surjective-map-maybe-prod)
              ( is-surjective-comp
                ( is-surjective-map-prod (pr2 h) (pr2 h'))
                ( is-surjective-is-equiv (is-equiv-map-ℕ-to-ℕ×ℕ)))))))
```
