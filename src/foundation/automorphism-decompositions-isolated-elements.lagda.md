# Automorphism decompositions with respect to isolated elements

```agda
module foundation.automorphism-decompositions-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-types-with-isolated-elements
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transpositions-isolated-elements
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
```

</details>

## Idea

Consider a type `A` equipped with an
[isolated element](foundation.isolated-elements.md) `a`, and write `C` for the
complement of `a` in `A`. Then there is an
[equivalence](foundation-core.equivalences.md)

```text
  Aut A ≃ Aut C × isolated-element A.
```

This equivalence was proven in the TypeTopology library by Martín Escardó
{{#cite Esc19CoderivedSet}}, who called the set `isolated-element A` the
_coderived set_ of `A`.

The idea behind our proof is that every automorphism `e` on A can be factored as
an equivalence that fixes the point `a` and the
[transposition](foundation.transpositions-isolated-elements.md) with the
isolated element `b := e a`. By this unique factorization result, we obtain an
equivalence

```text
  Aut A ≃ ((A , a) ≃∗ (A , a)) × isolated-element A.
```

We call the type on the right-hand side the
{{#concept "automorphism decomposition" Disambiguation="isolated element" Agda=automorphism-decomposition-isolated-element}}
with respect to the isolated element `a`. The proof of our original claim is
then finished by showing that any equivalence that fixes the isolated element
`a` is uniquely determined by an automorphism on the complement of `a`.

## Definitions

### The type of automorphism decompositions on types with isolated elements

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  automorphism-decomposition-isolated-element : UU l1
  automorphism-decomposition-isolated-element =
    ((A , a) ≃∗ (A , a)) × isolated-element A

  pointed-aut-automorphism-decomposition-isolated-element :
    automorphism-decomposition-isolated-element → (A , a) ≃∗ (A , a)
  pointed-aut-automorphism-decomposition-isolated-element = pr1

  aut-automorphism-decomposition-isolated-element :
    automorphism-decomposition-isolated-element → Aut A
  aut-automorphism-decomposition-isolated-element e =
    equiv-pointed-equiv
      ( pointed-aut-automorphism-decomposition-isolated-element e)

  isolated-element-automorphism-decomposition-isolated-element :
    automorphism-decomposition-isolated-element → isolated-element A
  isolated-element-automorphism-decomposition-isolated-element = pr2

  element-automorphism-decomposition-isolated-element :
    automorphism-decomposition-isolated-element → A
  element-automorphism-decomposition-isolated-element e =
    element-isolated-element
      ( isolated-element-automorphism-decomposition-isolated-element e)

  htpy-automorphism-decomposition-isolated-element :
    (e f : automorphism-decomposition-isolated-element) → UU l1
  htpy-automorphism-decomposition-isolated-element (e , b) (f , c) =
    ( htpy-pointed-equiv e f) ×
    ( element-isolated-element b ＝ element-isolated-element c)

  refl-htpy-automorphism-decomposition-isolated-element :
    (e : automorphism-decomposition-isolated-element) →
    htpy-automorphism-decomposition-isolated-element e e
  refl-htpy-automorphism-decomposition-isolated-element (e , b) =
    ( refl-htpy , refl)

  htpy-eq-automorphism-decomposition-isolated-element :
    (e f : automorphism-decomposition-isolated-element) →
    e ＝ f → htpy-automorphism-decomposition-isolated-element e f
  htpy-eq-automorphism-decomposition-isolated-element e f refl =
    refl-htpy-automorphism-decomposition-isolated-element e

  is-torsorial-htpy-automorphism-decomposition-isolated-element :
    (e : automorphism-decomposition-isolated-element) →
    is-torsorial (htpy-automorphism-decomposition-isolated-element e)
  is-torsorial-htpy-automorphism-decomposition-isolated-element ((e , p) , b) =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy-pointed-equiv-isolated-element
        ( a , d)
        ( a , d)
        ( e , p))
      ( (e , p) , refl-htpy)
      ( is-torsorial-Eq-subtype
        ( is-torsorial-Id _)
        ( is-prop-is-isolated)
        ( element-isolated-element b)
        ( refl)
        ( is-isolated-isolated-element b))

  is-equiv-htpy-eq-automorphism-decomposition-isolated-element :
    (e f : automorphism-decomposition-isolated-element) →
    is-equiv (htpy-eq-automorphism-decomposition-isolated-element e f)
  is-equiv-htpy-eq-automorphism-decomposition-isolated-element e =
    fundamental-theorem-id
      ( is-torsorial-htpy-automorphism-decomposition-isolated-element e)
      ( htpy-eq-automorphism-decomposition-isolated-element e)

  extensionality-automorphism-decomposition-isolated-element :
    (e f : automorphism-decomposition-isolated-element) →
    (e ＝ f) ≃ htpy-automorphism-decomposition-isolated-element e f
  pr1 (extensionality-automorphism-decomposition-isolated-element e f) =
    htpy-eq-automorphism-decomposition-isolated-element e f
  pr2 (extensionality-automorphism-decomposition-isolated-element e f) =
    is-equiv-htpy-eq-automorphism-decomposition-isolated-element e f

  eq-htpy-automorphism-decomposition-isolated-element :
    ((e , b) (f , c) : automorphism-decomposition-isolated-element) →
    htpy-pointed-equiv e f →
    element-isolated-element b ＝ element-isolated-element c →
    (e , b) ＝ (f , c)
  eq-htpy-automorphism-decomposition-isolated-element e f H p =
    map-inv-equiv
      ( extensionality-automorphism-decomposition-isolated-element e f)
      ( H , p)
```

## Properties

### Given an isolated element, the type of automorphisms on a type is equivalent to the type of automorphism decompositions

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  value-aut-isolated-element :
    Aut A → isolated-element A
  value-aut-isolated-element e = map-equiv-isolated-element e (a , d)

  transposition-value-aut-isolated-element :
    Aut A → Aut A
  transposition-value-aut-isolated-element e =
    transposition-isolated-elements (a , d) (value-aut-isolated-element e)

  aut-pointed-aut-isolated-element :
    Aut A → Aut A
  aut-pointed-aut-isolated-element e =
    transposition-value-aut-isolated-element e ∘e e

  map-pointed-aut-isolated-element :
    Aut A → A → A
  map-pointed-aut-isolated-element e =
    map-equiv (aut-pointed-aut-isolated-element e)

  preserves-point-pointed-aut-isolated-element :
    (e : Aut A) → map-pointed-aut-isolated-element e a ＝ a
  preserves-point-pointed-aut-isolated-element e =
    compute-second-value-transposition-isolated-elements
      ( a , d)
      ( value-aut-isolated-element e)

  pointed-aut-isolated-element :
    Aut A → (A , a) ≃∗ (A , a)
  pr1 (pointed-aut-isolated-element e) =
    aut-pointed-aut-isolated-element e
  pr2 (pointed-aut-isolated-element e) =
    preserves-point-pointed-aut-isolated-element e

  decomposition-aut-isolated-element :
    Aut A → ((A , a) ≃∗ (A , a)) × isolated-element A
  pr1 (decomposition-aut-isolated-element e) =
    pointed-aut-isolated-element e
  pr2 (decomposition-aut-isolated-element e) =
    value-aut-isolated-element e

  composition-aut-isolated-element :
    ((A , a) ≃∗ (A , a)) × isolated-element A → Aut A
  composition-aut-isolated-element ((h , p) , b) =
    transposition-isolated-elements (a , d) b ∘e h

  eq-isolated-element-is-section-composition-aut-isolated-element :
    (((e , p) , b) : automorphism-decomposition-isolated-element (a , d)) →
    element-automorphism-decomposition-isolated-element
      ( a , d)
      ( decomposition-aut-isolated-element
          ( composition-aut-isolated-element ((e , p) , b))) ＝
    element-isolated-element b
  eq-isolated-element-is-section-composition-aut-isolated-element
    ((e , p) , b) =
    ap (map-transposition-isolated-elements (a , d) b) p ∙
    compute-first-value-transposition-isolated-elements (a , d) b

  htpy-is-section-composition-aut-isolated-element :
    (((e , p) , b) : automorphism-decomposition-isolated-element (a , d)) →
    htpy-equiv
      ( aut-automorphism-decomposition-isolated-element
        ( a , d)
        ( decomposition-aut-isolated-element
          ( composition-aut-isolated-element ((e , p) , b))))
      ( e)
  htpy-is-section-composition-aut-isolated-element ((e , p) , b) =
    right-whisker-comp
      ( htpy-transposition-isolated-elements
        ( a , d)
        ( a , d)
        ( isolated-element-automorphism-decomposition-isolated-element
          ( a , d)
          ( decomposition-aut-isolated-element
            ( composition-aut-isolated-element ((e , p) , b))))
        ( b)
        ( refl)
        ( eq-isolated-element-is-section-composition-aut-isolated-element
          ( (e , p) , b)))
      ( map-equiv
        ( composition-aut-isolated-element ((e , p) , b))) ∙h
    right-whisker-comp
      ( is-involution-transposition-isolated-elements (a , d) b)
      ( map-equiv e)

  is-section-composition-aut-isolated-element :
    is-section
      decomposition-aut-isolated-element
      composition-aut-isolated-element
  is-section-composition-aut-isolated-element e =
    eq-htpy-automorphism-decomposition-isolated-element
      ( a , d)
      ( decomposition-aut-isolated-element
        ( composition-aut-isolated-element e))
      ( e)
      ( htpy-is-section-composition-aut-isolated-element e)
      ( eq-isolated-element-is-section-composition-aut-isolated-element e)

  is-retraction-composition-aut-isolated-element :
    is-retraction
      decomposition-aut-isolated-element
      composition-aut-isolated-element
  is-retraction-composition-aut-isolated-element e =
    eq-htpy-equiv
      ( right-whisker-comp
        ( is-involution-transposition-isolated-elements
          ( a , d)
          ( value-aut-isolated-element e))
        ( map-equiv e))

  is-equiv-decomposition-aut-isolated-element :
    is-equiv decomposition-aut-isolated-element
  is-equiv-decomposition-aut-isolated-element =
    is-equiv-is-invertible
      composition-aut-isolated-element
      is-section-composition-aut-isolated-element
      is-retraction-composition-aut-isolated-element

  equiv-decomposition-aut-isolated-element :
    Aut A ≃ automorphism-decomposition-isolated-element (a , d)
  pr1 equiv-decomposition-aut-isolated-element =
    decomposition-aut-isolated-element
  pr2 equiv-decomposition-aut-isolated-element =
    is-equiv-decomposition-aut-isolated-element
```

### The type `Aut A` is equivalent to `Aut C × isolated-element A`

```agda
module _
  {l1 : Level} {A : UU l1} (a : isolated-element A)
  where

  compute-aut-isolated-element :
    Aut A ≃ Aut (complement-isolated-element a) × isolated-element A
  compute-aut-isolated-element =
    equiv-product (compute-pointed-equiv-isolated-element a a) id-equiv ∘e
    equiv-decomposition-aut-isolated-element a
```

## References

{{#bibliography}}
