# Propositional extensionality

```agda
open import foundation.function-extensionality-axiom

module
  foundation.propositional-extensionality
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences funext
open import foundation.negation funext
open import foundation.postcomposition-functions funext
open import foundation.raising-universe-levels funext
open import foundation.raising-universe-levels funext-unit-type
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.univalence funext
open import foundation.univalent-type-families funext
open import foundation.universal-property-contractible-types funext
open import foundation.universal-property-empty-type funext
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

{{#concept "Propositional extensionality" Agda=propositional-extensionality}}
characterizes [identifications](foundation-core.identity-types.md) of
[propositions](foundation-core.propositions.md). It asserts that for any two
propositions `P` and `Q`, we have `(P ＝ Q) ≃ (P ⇔ Q)`.

**Note.** While we derive propositional extensionality from the
[univalence axiom](foundation-core.univalence.md), it is a strictly weaker
principle, meaning that the principle of propositional extensionality does not
imply univalence.

## Properties

### Propositional extensionality

```agda
module _
  {l1 : Level}
  where

  abstract
    is-torsorial-iff :
      (P : Prop l1) → is-torsorial (λ (Q : Prop l1) → type-Prop P ↔ type-Prop Q)
    is-torsorial-iff P =
      is-contr-equiv
        ( Σ (Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
        ( equiv-tot (equiv-equiv-iff P))
        ( is-torsorial-Eq-subtype
          ( is-torsorial-equiv (type-Prop P))
          ( is-prop-is-prop)
          ( type-Prop P)
          ( id-equiv)
          ( is-prop-type-Prop P))

  abstract
    is-equiv-iff-eq : (P Q : Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
    is-equiv-iff-eq P =
      fundamental-theorem-id (is-torsorial-iff P) (λ Q → iff-eq {P = P} {Q})

  propositional-extensionality :
    (P Q : Prop l1) → (P ＝ Q) ≃ (type-Prop P ↔ type-Prop Q)
  pr1 (propositional-extensionality P Q) = iff-eq
  pr2 (propositional-extensionality P Q) = is-equiv-iff-eq P Q

  eq-iff' : (P Q : Prop l1) → type-Prop P ↔ type-Prop Q → P ＝ Q
  eq-iff' P Q = map-inv-is-equiv (is-equiv-iff-eq P Q)

  eq-iff :
    {P Q : Prop l1} →
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → P ＝ Q
  eq-iff {P} {Q} f g = eq-iff' P Q (pair f g)

  eq-equiv-Prop :
    {P Q : Prop l1} → type-Prop P ≃ type-Prop Q → P ＝ Q
  eq-equiv-Prop e =
    eq-iff (map-equiv e) (map-inv-equiv e)

  equiv-eq-Prop :
    {P Q : Prop l1} → P ＝ Q → type-Prop P ≃ type-Prop Q
  equiv-eq-Prop {P} refl = id-equiv

  is-torsorial-equiv-Prop :
    (P : Prop l1) → is-torsorial (λ Q → type-Prop P ≃ type-Prop Q)
  is-torsorial-equiv-Prop P =
    is-contr-equiv'
      ( Σ (Prop l1) (λ Q → type-Prop P ↔ type-Prop Q))
      ( equiv-tot (equiv-equiv-iff P))
      ( is-torsorial-iff P)
```

### The type of propositions is a set

```agda
is-set-type-Prop : {l : Level} → is-set (Prop l)
is-set-type-Prop P Q =
  is-prop-equiv
    ( propositional-extensionality P Q)
    ( is-prop-iff-Prop P Q)

Prop-Set : (l : Level) → Set (lsuc l)
pr1 (Prop-Set l) = Prop l
pr2 (Prop-Set l) = is-set-type-Prop
```

### The canonical type family over `Prop` is univalent

```agda
is-univalent-type-Prop : {l : Level} → is-univalent (type-Prop {l})
is-univalent-type-Prop P =
  fundamental-theorem-id
    ( is-torsorial-equiv-Prop P)
    ( λ Q → equiv-tr type-Prop)
```

### The type of true propositions is contractible

```agda
abstract
  is-torsorial-true-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → type-Prop P)
  is-torsorial-true-Prop {l1} =
    is-contr-equiv
      ( Σ (Prop l1) (λ P → raise-unit l1 ↔ type-Prop P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( equiv-universal-property-contr
                ( raise-star)
                ( is-contr-raise-unit)
                ( type-Prop P)) ∘e
              ( right-unit-law-product-is-contr
                ( is-contr-Π
                  ( λ _ →
                    is-proof-irrelevant-is-prop
                      ( is-prop-raise-unit)
                      ( raise-star)))))))
      ( is-torsorial-iff (raise-unit-Prop l1))
```

### The type of false propositions is contractible

```agda
abstract
  is-torsorial-false-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → ¬ (type-Prop P))
  is-torsorial-false-Prop {l1} =
    is-contr-equiv
      ( Σ (Prop l1) (λ P → raise-empty l1 ↔ type-Prop P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( inv-equiv
                ( equiv-postcomp (type-Prop P) (compute-raise l1 empty))) ∘e
              ( left-unit-law-product-is-contr
                ( universal-property-empty-is-empty
                  ( raise-empty l1)
                  ( is-empty-raise-empty)
                  ( type-Prop P))))))
      ( is-torsorial-iff (raise-empty-Prop l1))
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [propositional extensionality](https://ncatlab.org/nlab/show/propositional+extensionality)
  at $n$Lab.
