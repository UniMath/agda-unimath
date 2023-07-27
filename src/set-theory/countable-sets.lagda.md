# Countable sets

```agda
module set-theory.countable-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.type-arithmetic-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.maybe
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.shifting-sequences
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A set `X` is said to be countable if there is a surjective map `f : ℕ → X + 1`.
Equivalently, a set `X` is countable if there is a surjective map
`f : type-decidable-subset P → X` for some decidable subset `P` of `X`.

## Definition

### First definition of countable types

```agda
module _
  {l : Level} (X : Set l)
  where

  enumeration : UU l
  enumeration = Σ (ℕ → Maybe (type-Set X)) is-surjective

  map-enumeration : enumeration → (ℕ → Maybe (type-Set X))
  map-enumeration E = pr1 E

  is-surjective-map-enumeration :
    (E : enumeration) → is-surjective (map-enumeration E)
  is-surjective-map-enumeration E = pr2 E

  is-countable-Prop : Prop l
  is-countable-Prop = ∃-Prop (ℕ → Maybe (type-Set X)) is-surjective

  is-countable : UU l
  is-countable = type-Prop (is-countable-Prop)

  is-prop-is-countable : is-prop is-countable
  is-prop-is-countable = is-prop-type-Prop is-countable-Prop
```

### Second definition of countable types

```agda
module _
  {l : Level} (X : Set l)
  where

  decidable-subprojection-ℕ : UU (lsuc l ⊔ l)
  decidable-subprojection-ℕ =
    Σ ( decidable-subtype l ℕ)
      ( λ P → type-decidable-subtype P ↠ type-Set X)

  is-countable-Prop' : Prop (lsuc l ⊔ l)
  is-countable-Prop' =
    ∃-Prop
      ( decidable-subtype l ℕ)
      ( λ P → type-decidable-subtype P ↠ type-Set X)

  is-countable' : UU (lsuc l ⊔ l)
  is-countable' = type-Prop is-countable-Prop'

  is-prop-is-countable' : is-prop is-countable'
  is-prop-is-countable' = is-prop-type-Prop is-countable-Prop'
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

First, we will prove `is-countable X → is-countable' X`.

```agda
module _
  {l : Level} (X : Set l)
  where

  decidable-subprojection-ℕ-enumeration :
    enumeration X → decidable-subprojection-ℕ X
  decidable-subprojection-ℕ-enumeration (f , H) =
    pair
      ( λ n →
        ( ¬ ((f n) ＝ (inr star))) ,
        ( ( is-prop-neg) ,
          ( is-decidable-is-not-exception-Maybe (f n))))
      ( pair
        ( λ {(n , p) → value-is-not-exception-Maybe (f n) p})
        ( λ x →
          ( apply-universal-property-trunc-Prop (H (inl x))
            ( trunc-Prop (fib _ x))
            ( λ (n , p) →
                ( unit-trunc-Prop
                  ( pair
                    ( pair n
                      ( is-not-exception-is-value-Maybe
                        ( f n) (x , inv p)))
                    ( is-injective-inl
                      ( ( eq-is-not-exception-Maybe
                        ( f n)
                        ( is-not-exception-is-value-Maybe
                          ( f n) (x , inv p))) ∙
                      ( p)))))))))

  is-countable'-is-countable :
    is-countable X → is-countable' X
  is-countable'-is-countable H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop' X)
      ( λ E →
        ( unit-trunc-Prop (decidable-subprojection-ℕ-enumeration E)))
```

Second, we will prove `is-countable' X → is-countable X`.

```agda
cases-map-decidable-subtype-ℕ :
  {l : Level} (X : Set l) →
  ( P : decidable-subtype l ℕ) →
  ( f : type-decidable-subtype P → type-Set X) →
  ( (n : ℕ) → is-decidable (pr1 (P n)) -> Maybe (type-Set X))
cases-map-decidable-subtype-ℕ X P f n (inl x) = inl (f (n , x))
cases-map-decidable-subtype-ℕ X P f n (inr x) = inr star

module _
  {l : Level} (X : Set l)
  ( P : decidable-subtype l ℕ)
  ( f : type-decidable-subtype P → type-Set X)
  where

  shift-decidable-subtype-ℕ : decidable-subtype l ℕ
  shift-decidable-subtype-ℕ zero-ℕ =
    ( raise-empty l) ,
    ( is-prop-raise-empty ,
      ( inr (is-empty-raise-empty)))
  shift-decidable-subtype-ℕ (succ-ℕ n) = P n

  map-shift-decidable-subtype-ℕ :
    type-decidable-subtype shift-decidable-subtype-ℕ → type-Set X
  map-shift-decidable-subtype-ℕ (zero-ℕ , map-raise ())
  map-shift-decidable-subtype-ℕ (succ-ℕ n , p) = f (n , p)

  map-enumeration-decidable-subprojection-ℕ : ℕ → Maybe (type-Set X)
  map-enumeration-decidable-subprojection-ℕ n =
    cases-map-decidable-subtype-ℕ
      ( X)
      ( shift-decidable-subtype-ℕ)
      ( map-shift-decidable-subtype-ℕ)
      ( n)
      (pr2 (pr2 (shift-decidable-subtype-ℕ n)))

  is-surjective-map-enumeration-decidable-subprojection-ℕ :
    ( is-surjective f) →
    ( is-surjective map-enumeration-decidable-subprojection-ℕ)
  is-surjective-map-enumeration-decidable-subprojection-ℕ H (inl x) =
    ( apply-universal-property-trunc-Prop (H x)
      (trunc-Prop (fib map-enumeration-decidable-subprojection-ℕ (inl x)))
      ( λ { ((n , s) , refl) →
        ( unit-trunc-Prop
          ( succ-ℕ n ,
          ( ap
            ( cases-map-decidable-subtype-ℕ X
              ( shift-decidable-subtype-ℕ)
              ( map-shift-decidable-subtype-ℕ)
              (succ-ℕ n))
            ( pr1
              ( is-prop-is-decidable (pr1 (pr2 (P n)))
                ( pr2 (pr2 (P n)))
                ( inl s))))))}))
  is-surjective-map-enumeration-decidable-subprojection-ℕ H (inr star) =
    ( unit-trunc-Prop (0 , refl))

module _
  {l : Level} (X : Set l)
  where

  enumeration-decidable-subprojection-ℕ :
    decidable-subprojection-ℕ X → enumeration X
  enumeration-decidable-subprojection-ℕ (P , (f , H)) =
    ( map-enumeration-decidable-subprojection-ℕ X P f) ,
    ( is-surjective-map-enumeration-decidable-subprojection-ℕ X P f H)

  is-countable-is-countable' :
    is-countable' X → is-countable X
  is-countable-is-countable' H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop X)
      ( λ D →
        ( unit-trunc-Prop (enumeration-decidable-subprojection-ℕ D)))
```

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

The empty set is countable.

```agda
is-countable-empty : is-countable empty-Set
is-countable-empty =
  is-countable-is-countable' empty-Set
    (unit-trunc-Prop
      ( ( λ x → empty-Decidable-Prop) ,
        ( λ {()}) , λ {()}))
```

The unit set is countable.

```agda
is-countable-unit : is-countable unit-Set
is-countable-unit =
  unit-trunc-Prop
    ( ( λ { zero-ℕ → inl star ; (succ-ℕ x) → inr star}) ,
      ( λ {
        ( inl star) → unit-trunc-Prop (0 , refl) ;
        ( inr star) → unit-trunc-Prop (1 , refl)}))
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

In particular, the sets ℕ + ℕ, ℕ × ℕ, and ℤ are countable.

```agda
is-countable-ℕ+ℕ : is-countable (coprod-Set ℕ-Set ℕ-Set)
is-countable-ℕ+ℕ =
  is-countable-coprod ℕ-Set ℕ-Set is-countable-ℕ is-countable-ℕ

is-countable-ℕ×ℕ : is-countable (prod-Set ℕ-Set ℕ-Set)
is-countable-ℕ×ℕ =
  is-countable-prod ℕ-Set ℕ-Set is-countable-ℕ is-countable-ℕ

is-countable-ℤ : is-countable (ℤ-Set)
is-countable-ℤ =
  is-countable-coprod (ℕ-Set) (coprod-Set unit-Set ℕ-Set)
    ( is-countable-ℕ)
    ( is-countable-coprod (unit-Set) (ℕ-Set)
      ( is-countable-unit) (is-countable-ℕ))
```

All standart finite sets are countable.

```agda
is-countable-Fin-Set : (n : ℕ) → is-countable (Fin-Set n)
is-countable-Fin-Set zero-ℕ = is-countable-empty
is-countable-Fin-Set (succ-ℕ n) =
  is-countable-coprod (Fin-Set n) (unit-Set)
    ( is-countable-Fin-Set n) (is-countable-unit)
```
