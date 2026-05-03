# Transpositions at isolated elements

```agda
module foundation.transpositions-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.involutions
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.transposition-identifications-along-equivalences
open import foundation.transposition-identifications-along-involutions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

Consider a type `A` equipped with two
[isolated elements](foundation.isolated-elements.md) `a` and `b`. Then we define
an [equivalence](foundation-core.equivalences.md) `A ≃ A` which swaps `a` and
`b` and leaves all the other elements fixed. This equivalence is called the
{{#concept "transposition" Disambiguation="isolated elements" Agda=transposition-isolated-elements}}
at `a` and `b`. Since the transposition at `a` and `b` swaps `a` and `b` and
leaves all the other elements fixed, it is an
[involution](foundation.involutions.md).

## Definitions

### Any two distinct isolated elements in a type determine a transposition

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) (b , e) : isolated-element A)
  (H : a ≠ b)
  where

  is-in-split-full-subtype-distinct-isolated-elements : A → UU l1
  is-in-split-full-subtype-distinct-isolated-elements x =
    (a ＝ x) + (b ＝ x) + (a ≠ x) × (b ≠ x)

  abstract
    is-prop-is-in-split-full-subtype-distinct-isolated-elements :
      (x : A) → is-prop (is-in-split-full-subtype-distinct-isolated-elements x)
    is-prop-is-in-split-full-subtype-distinct-isolated-elements x =
      is-prop-coproduct
        ( λ p →
          rec-coproduct
            ( λ q → H (p ∙ inv q))
            ( λ (f , g) → f p))
        ( is-prop-eq-isolated-element a d x)
        ( is-prop-coproduct
          ( λ q (f , g) → g q)
          ( is-prop-eq-isolated-element b e x)
          ( is-prop-product is-prop-neg is-prop-neg))

  split-full-subtype-distinct-isolated-elements : subtype l1 A
  pr1 (split-full-subtype-distinct-isolated-elements x) =
    is-in-split-full-subtype-distinct-isolated-elements x
  pr2 (split-full-subtype-distinct-isolated-elements x) =
    is-prop-is-in-split-full-subtype-distinct-isolated-elements x

  is-full-split-full-subtype-distinct-isolated-elements :
    is-full-subtype split-full-subtype-distinct-isolated-elements
  is-full-split-full-subtype-distinct-isolated-elements x =
    rec-coproduct
      ( λ p → inl p)
      ( λ f →
        rec-coproduct
          ( λ q → inr (inl q))
          ( λ g → inr (inr (f , g)))
          ( e x))
      ( d x)

  compute-type-split-full-subtype-distinct-isolated-elements :
    type-subtype split-full-subtype-distinct-isolated-elements ≃ A
  compute-type-split-full-subtype-distinct-isolated-elements =
    equiv-inclusion-is-full-subtype
      split-full-subtype-distinct-isolated-elements
      is-full-split-full-subtype-distinct-isolated-elements

  inv-compute-type-split-full-subtype-distinct-isolated-elements :
    A ≃ type-subtype split-full-subtype-distinct-isolated-elements
  inv-compute-type-split-full-subtype-distinct-isolated-elements =
    inv-equiv-inclusion-is-full-subtype
      split-full-subtype-distinct-isolated-elements
      is-full-split-full-subtype-distinct-isolated-elements

  map-transposition-distinct-isolated-elements' :
    type-subtype split-full-subtype-distinct-isolated-elements →
    type-subtype split-full-subtype-distinct-isolated-elements
  pr1 (map-transposition-distinct-isolated-elements' (x , inl p)) =
    b
  pr2 (map-transposition-distinct-isolated-elements' (x , inl p)) =
    inr (inl refl)
  pr1 (map-transposition-distinct-isolated-elements' (x , inr (inl q))) =
    a
  pr2 (map-transposition-distinct-isolated-elements' (x , inr (inl q))) =
    inl refl
  pr1 (map-transposition-distinct-isolated-elements' (x , inr (inr H))) =
    x
  pr2 (map-transposition-distinct-isolated-elements' (x , inr (inr H))) =
    inr (inr H)

  is-involution-transposition-distinct-isolated-elements' :
    is-involution map-transposition-distinct-isolated-elements'
  is-involution-transposition-distinct-isolated-elements' (x , inl refl) =
    eq-type-subtype split-full-subtype-distinct-isolated-elements refl
  is-involution-transposition-distinct-isolated-elements' (x , inr (inl refl)) =
    eq-type-subtype split-full-subtype-distinct-isolated-elements refl
  is-involution-transposition-distinct-isolated-elements' (x , inr (inr H)) =
    eq-type-subtype split-full-subtype-distinct-isolated-elements refl

  is-equiv-transposition-distinct-isolated-elements' :
    is-equiv map-transposition-distinct-isolated-elements'
  is-equiv-transposition-distinct-isolated-elements' =
    is-equiv-is-involution
      is-involution-transposition-distinct-isolated-elements'

  transposition-distinct-isolated-elements' :
    type-subtype split-full-subtype-distinct-isolated-elements ≃
    type-subtype split-full-subtype-distinct-isolated-elements
  pr1 transposition-distinct-isolated-elements' =
    map-transposition-distinct-isolated-elements'
  pr2 transposition-distinct-isolated-elements' =
    is-equiv-transposition-distinct-isolated-elements'

  transposition-distinct-isolated-elements : A ≃ A
  transposition-distinct-isolated-elements =
    compute-type-split-full-subtype-distinct-isolated-elements ∘e
    transposition-distinct-isolated-elements' ∘e
    inv-compute-type-split-full-subtype-distinct-isolated-elements

  map-transposition-distinct-isolated-elements : A → A
  map-transposition-distinct-isolated-elements =
    map-equiv transposition-distinct-isolated-elements

  is-involution-transposition-distinct-isolated-elements :
    is-involution map-transposition-distinct-isolated-elements
  is-involution-transposition-distinct-isolated-elements =
    is-involution-conjugation
      compute-type-split-full-subtype-distinct-isolated-elements
      map-transposition-distinct-isolated-elements'
      is-involution-transposition-distinct-isolated-elements'
```

### Any two isolated elements in a type determine a transposition

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) (b , e) : isolated-element A)
  where

  cases-transposition-isolated-elements :
    is-decidable (a ＝ b) → A ≃ A
  cases-transposition-isolated-elements (inl p) = id-equiv
  cases-transposition-isolated-elements (inr f) =
    transposition-distinct-isolated-elements (a , d) (b , e) f

  transposition-isolated-elements : A ≃ A
  transposition-isolated-elements =
    cases-transposition-isolated-elements (d b)

  map-transposition-isolated-elements : A → A
  map-transposition-isolated-elements =
    map-equiv transposition-isolated-elements

  cases-is-involution-transposition-isolated-elements :
    (u : is-decidable (a ＝ b)) →
    is-involution (map-equiv (cases-transposition-isolated-elements u))
  cases-is-involution-transposition-isolated-elements (inl p) =
    is-involution-id
  cases-is-involution-transposition-isolated-elements (inr f) =
    is-involution-transposition-distinct-isolated-elements (a , d) (b , e) f

  is-involution-transposition-isolated-elements :
    is-involution map-transposition-isolated-elements
  is-involution-transposition-isolated-elements =
    cases-is-involution-transposition-isolated-elements (d b)
```
