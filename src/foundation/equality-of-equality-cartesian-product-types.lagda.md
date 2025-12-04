# Equality of cartesian product types

```agda
module foundation.equality-of-equality-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

[Identifications](foundation-core.identity-types.md) of identifications in a
[cartesian product](foundation-core.cartesian-product-types.md) are
[equivalently](foundation-core.equivalences.md) described as pairs of
identifications. This provides us with a characterization of the identity types
of identity types of cartesian product types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  Eq²-product : {s t : A × B} (p q : s ＝ t) → UU (l1 ⊔ l2)
  Eq²-product p q = Eq-product (pair-eq p) (pair-eq q)

  pair-eq² : {s t : A × B} {p q : s ＝ t} → p ＝ q → Eq²-product p q
  pair-eq² r = pair-eq (ap pair-eq r)
```

## Properties

### Characterizing equality of equality in cartesian products

```agda
abstract
  is-torsorial-Eq-product :
      {l1 l2 : Level} {A : UU l1} {B : UU l2} (s : A × B) →
      is-torsorial (Eq-product s)
  is-torsorial-Eq-product s =
    fundamental-theorem-id' (λ t → pair-eq) (is-equiv-pair-eq s)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-torsorial-Eq²-product :
      {s t : A × B} (p : s ＝ t) → is-torsorial (Eq²-product p)
    is-torsorial-Eq²-product {s} {t} p =
      is-contr-equiv
        ( Σ (Eq-product s t) (Eq-product (pair-eq p)))
        ( equiv-Σ-equiv-base
          ( Eq-product (pair-eq p))
          ( equiv-pair-eq s t))
        ( is-torsorial-Eq-product (pair-eq p))

  abstract
    is-equiv-pair-eq² :
      {s t : A × B} (p q : s ＝ t) → is-equiv (pair-eq² {p = p} {q = q})
    is-equiv-pair-eq² p =
      fundamental-theorem-id (is-torsorial-Eq²-product p) (λ q → pair-eq²)

  equiv-pair-eq² :
    {s t : A × B} (p q : s ＝ t) → (p ＝ q) ≃ Eq²-product p q
  pr1 (equiv-pair-eq² p q) = pair-eq²
  pr2 (equiv-pair-eq² p q) = is-equiv-pair-eq² p q

  eq-pair² : {s t : A × B} {p q : s ＝ t} → Eq²-product p q → p ＝ q
  eq-pair² {p = p} {q} = map-inv-equiv (equiv-pair-eq² p q)
```
