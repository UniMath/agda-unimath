# Propositional extensionality

```agda
module foundation.propositional-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.postcomposition-functions
open import foundation.raising-universe-levels
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.univalent-type-families
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Propositional extensionality characterizes identifications of propositions. It
asserts that for any two propositions `P` and `Q`, we have `Id P Q ≃ (P ⇔ Q)`.

## Properties

### Propositional extensionality

```agda
module _
  {l1 : Level}
  where

  abstract
    is-torsorial-iff :
      (P : Prop l1) → is-torsorial (λ (Q : Prop l1) → P ⇔ Q)
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
      fundamental-theorem-id
        ( is-torsorial-iff P)
        ( λ Q → iff-eq {P = P} {Q})

  propositional-extensionality :
    (P Q : Prop l1) → (P ＝ Q) ≃ (P ⇔ Q)
  pr1 (propositional-extensionality P Q) = iff-eq
  pr2 (propositional-extensionality P Q) = is-equiv-iff-eq P Q

  eq-iff' : (P Q : Prop l1) → P ⇔ Q → P ＝ Q
  eq-iff' P Q = map-inv-is-equiv (is-equiv-iff-eq P Q)

  eq-iff :
    {P Q : Prop l1} →
    (type-Prop P → type-Prop Q) → (type-Prop Q → type-Prop P) → P ＝ Q
  eq-iff {P} {Q} f g = eq-iff' P Q (pair f g)

  eq-equiv-Prop :
    {P Q : Prop l1} → (type-Prop P ≃ type-Prop Q) → P ＝ Q
  eq-equiv-Prop e =
    eq-iff (map-equiv e) (map-inv-equiv e)

  equiv-eq-Prop :
    {P Q : Prop l1} → P ＝ Q → type-Prop P ≃ type-Prop Q
  equiv-eq-Prop {P} refl = id-equiv

  is-torsorial-equiv-Prop :
    (P : Prop l1) →
    is-torsorial (λ Q → type-Prop P ≃ type-Prop Q)
  is-torsorial-equiv-Prop P =
    is-contr-equiv'
      ( Σ (Prop l1) (λ Q → P ⇔ Q))
      ( equiv-tot (equiv-equiv-iff P))
      ( is-torsorial-iff P)
```

### The type of propositions is a set

```agda
is-set-type-Prop : {l : Level} → is-set (Prop l)
is-set-type-Prop {l} P Q =
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
is-univalent-type-Prop {l} P =
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
      ( Σ (Prop l1) (λ P → raise-unit-Prop l1 ⇔ P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( equiv-universal-property-contr
                ( raise-star)
                ( is-contr-raise-unit)
                ( type-Prop P)) ∘e
              ( right-unit-law-prod-is-contr
                ( is-contr-Π
                  ( λ x →
                    is-proof-irrelevant-is-prop
                      ( is-prop-raise-unit)
                      ( raise-star)))))))
      ( is-torsorial-iff (raise-unit-Prop l1))
```

### The type of false propositions is contractible

```agda
abstract
  is-torsorial-false-Prop :
    {l1 : Level} → is-torsorial (λ (P : Prop l1) → type-Prop (neg-Prop P))
  is-torsorial-false-Prop {l1} =
    is-contr-equiv
      ( Σ (Prop l1) (λ P → raise-empty-Prop l1 ⇔ P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( inv-equiv
                ( equiv-postcomp (type-Prop P) (compute-raise l1 empty))) ∘e
              ( left-unit-law-prod-is-contr
                ( universal-property-empty-is-empty
                  ( raise-empty l1)
                  ( is-empty-raise-empty)
                  ( type-Prop P))))))
      ( is-torsorial-iff (raise-empty-Prop l1))
```
