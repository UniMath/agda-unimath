# Homomorphisms of cyclic rings

```agda
module ring-theory.homomorphisms-cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.cyclic-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of cyclic rings" Agda=hom-Cyclic-Ring}}
of [cyclic rings](ring-theory.cyclic-rings.md) is a
[ring homomorphism](ring-theory.homomorphisms-rings.md) between their underlying
[rings](ring-theory.rings.md).

For any cyclic ring `R` and any ring `S`, there exists at most one homomorphism
from `R` to `S`. We will use this observation in
[`ring-theory.poset-of-cyclic-rings`](ring-theory.poset-of-cyclic-rings.md) to
construct the [large poset](order-theory.large-posets.md) of cyclic rings.

## Definitions

### Homomorphisms of cyclic rings

```agda
module _
  {l1 l2 : Level} (R : Cyclic-Ring l1) (S : Cyclic-Ring l2)
  where

  hom-set-Cyclic-Ring : Set (l1 ⊔ l2)
  hom-set-Cyclic-Ring = hom-set-Ring (ring-Cyclic-Ring R) (ring-Cyclic-Ring S)

  hom-Cyclic-Ring : UU (l1 ⊔ l2)
  hom-Cyclic-Ring = hom-Ring (ring-Cyclic-Ring R) (ring-Cyclic-Ring S)

  is-set-hom-Cyclic-Ring : is-set hom-Cyclic-Ring
  is-set-hom-Cyclic-Ring =
    is-set-hom-Ring (ring-Cyclic-Ring R) (ring-Cyclic-Ring S)
```

### The identity homomorphism of cyclic rings

```agda
module _
  {l1 : Level} (R : Cyclic-Ring l1)
  where

  id-hom-Cyclic-Ring : hom-Cyclic-Ring R R
  id-hom-Cyclic-Ring = id-hom-Ring (ring-Cyclic-Ring R)
```

### Composition of homomorphisms of cyclci rings

```agda
module _
  {l1 l2 l3 : Level}
  (R : Cyclic-Ring l1) (S : Cyclic-Ring l2) (T : Cyclic-Ring l3)
  where

  comp-hom-Cyclic-Ring :
    (g : hom-Cyclic-Ring S T) (f : hom-Cyclic-Ring R S) →
    hom-Cyclic-Ring R T
  comp-hom-Cyclic-Ring =
    comp-hom-Ring
      ( ring-Cyclic-Ring R)
      ( ring-Cyclic-Ring S)
      ( ring-Cyclic-Ring T)
```

## Properties

### Given a cyclic ring `R` and a ring `S`, there is at most one ring homomorphism from `R` to `S`

**Proof:** Consider two ring homomorphisms `f g : R → S`. To show that `f ＝ g`
it suffices to show that `f x ＝ g x` for all `x : R`. However, by the
assumption that `R` is cyclic implies that `x ＝ n1`. Furthermore, every ring
homomorphism preserves integer multiplication, so it follows that

```text
  f x ＝ f (n1) ＝ n (f 1) ＝ n 1 ＝ n (g 1) ＝ g (n1) ＝ g x.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level} (R : Cyclic-Ring l1) (S : Ring l2)
  where

  abstract
    htpy-all-elements-equal-hom-Cyclic-Ring-Ring :
      (f g : hom-Ring (ring-Cyclic-Ring R) S) →
      htpy-hom-Ring (ring-Cyclic-Ring R) S f g
    htpy-all-elements-equal-hom-Cyclic-Ring-Ring f g x =
      apply-universal-property-trunc-Prop
        ( is-surjective-initial-hom-Cyclic-Ring R x)
        ( Id-Prop
          ( set-Ring S)
          ( map-hom-Ring (ring-Cyclic-Ring R) S f x)
          ( map-hom-Ring (ring-Cyclic-Ring R) S g x))
        ( λ where
          ( n , refl) →
            ( preserves-integer-multiples-hom-Ring
              ( ring-Cyclic-Ring R)
              ( S)
              ( f)
              ( n)
              ( one-Cyclic-Ring R)) ∙
            ( ap
              ( integer-multiple-Ring S n)
              ( preserves-one-hom-Ring (ring-Cyclic-Ring R) S f)) ∙
            ( inv
              ( ap
                ( integer-multiple-Ring S n)
                ( preserves-one-hom-Ring (ring-Cyclic-Ring R) S g))) ∙
            ( inv
              ( preserves-integer-multiples-hom-Ring
                ( ring-Cyclic-Ring R)
                ( S)
                ( g)
                ( n)
                ( one-Cyclic-Ring R))))

  all-elements-equal-hom-Cyclic-Ring-Ring :
    all-elements-equal (hom-Ring (ring-Cyclic-Ring R) S)
  all-elements-equal-hom-Cyclic-Ring-Ring f g =
    eq-htpy-hom-Ring
      ( ring-Cyclic-Ring R)
      ( S)
      ( f)
      ( g)
      ( htpy-all-elements-equal-hom-Cyclic-Ring-Ring f g)

  is-prop-hom-Cyclic-Ring-Ring :
    is-prop (hom-Ring (ring-Cyclic-Ring R) S)
  is-prop-hom-Cyclic-Ring-Ring =
    is-prop-all-elements-equal all-elements-equal-hom-Cyclic-Ring-Ring

module _
  {l1 l2 : Level} (R : Cyclic-Ring l1) (S : Cyclic-Ring l2)
  where

  is-prop-hom-Cyclic-Ring :
    is-prop (hom-Cyclic-Ring R S)
  is-prop-hom-Cyclic-Ring =
    is-prop-hom-Cyclic-Ring-Ring R (ring-Cyclic-Ring S)
```

### Composition of morphisms of cyclic rings satisfies the laws of a category

```agda
module _
  {l1 l2 : Level} (R : Cyclic-Ring l1) (S : Cyclic-Ring l2)
  (f : hom-Cyclic-Ring R S)
  where

  left-unit-law-comp-hom-Cyclic-Ring :
    comp-hom-Cyclic-Ring R S S (id-hom-Cyclic-Ring S) f ＝ f
  left-unit-law-comp-hom-Cyclic-Ring =
    left-unit-law-comp-hom-Ring
      ( ring-Cyclic-Ring R)
      ( ring-Cyclic-Ring S)
      ( f)

  right-unit-law-comp-hom-Cyclic-Ring :
    comp-hom-Cyclic-Ring R R S f (id-hom-Cyclic-Ring R) ＝ f
  right-unit-law-comp-hom-Cyclic-Ring =
    right-unit-law-comp-hom-Ring
      ( ring-Cyclic-Ring R)
      ( ring-Cyclic-Ring S)
      ( f)

module _
  {l1 l2 l3 l4 : Level}
  (R : Cyclic-Ring l1) (S : Cyclic-Ring l2)
  (T : Cyclic-Ring l3) (U : Cyclic-Ring l4)
  where

  associative-comp-hom-Cyclic-Ring :
    (h : hom-Cyclic-Ring T U)
    (g : hom-Cyclic-Ring S T)
    (f : hom-Cyclic-Ring R S) →
    comp-hom-Cyclic-Ring R S U (comp-hom-Cyclic-Ring S T U h g) f ＝
    comp-hom-Cyclic-Ring R T U h (comp-hom-Cyclic-Ring R S T g f)
  associative-comp-hom-Cyclic-Ring =
    associative-comp-hom-Ring
      ( ring-Cyclic-Ring R)
      ( ring-Cyclic-Ring S)
      ( ring-Cyclic-Ring T)
      ( ring-Cyclic-Ring U)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
