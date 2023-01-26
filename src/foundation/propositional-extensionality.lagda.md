---
title: Propositional extensionality
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-extensionality where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; equiv-universal-property-contr; is-contr-Π;
    is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( raise-empty-Prop; empty; raise-empty; is-empty-raise-empty)
open import foundation.equivalences using
  ( _≃_; id-equiv; is-equiv; map-inv-is-equiv; map-equiv; map-inv-equiv;
    inv-equiv; _∘e_)
open import foundation.functions using (id)
open import foundation.functoriality-function-types using
  ( equiv-postcomp)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (_＝_; refl; equiv-tr)
open import foundation.logical-equivalences using
  ( _⇔_; equiv-equiv-iff; iff-eq; is-prop-logical-equivalence)
open import foundation.negation using (neg-Prop)
open import foundation.propositions using
  ( Prop; type-Prop; is-prop-is-prop; is-prop-type-Prop;
    is-proof-irrelevant-is-prop; is-prop-equiv)
open import foundation.raising-universe-levels using (equiv-raise)
open import foundation.sets using (is-set; Set)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.type-arithmetic-cartesian-product-types using
  ( right-unit-law-prod-is-contr; left-unit-law-prod-is-contr)
open import foundation.unit-type using
  ( raise-unit-Prop; raise-star; is-contr-raise-unit; is-prop-raise-unit)
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.univalent-type-families using (is-univalent)
open import foundation.universal-property-empty-type using
  ( universal-property-empty-is-empty)
open import foundation.universe-levels using (Level; lsuc)
```

## Idea

Propositional extensionality characterizes identifications of propositions. It asserts that for any two propositions `P` and `Q`, we have `Id P Q ≃ (P ⇔ Q)`.

## Properties

### Propositional extensionality

```agda
module _
  {l1 : Level}
  where
  
  abstract
    is-contr-total-iff :
      (P : Prop l1) → is-contr (Σ (Prop l1) (λ Q → P ⇔ Q))
    is-contr-total-iff P =
      is-contr-equiv
        ( Σ (Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
        ( equiv-tot (equiv-equiv-iff P))
        ( is-contr-total-Eq-subtype
          ( is-contr-total-equiv (type-Prop P))
          ( is-prop-is-prop)
          ( type-Prop P)
          ( id-equiv)
          ( is-prop-type-Prop P))

  abstract
    is-equiv-iff-eq : (P Q : Prop l1) → is-equiv (iff-eq {l1} {P} {Q})
    is-equiv-iff-eq P =
      fundamental-theorem-id 
        ( is-contr-total-iff P)
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

  is-contr-total-equiv-Prop :
    (P : Prop l1) →
    is-contr (Σ (Prop l1) (λ Q → type-Prop P ≃ type-Prop Q))
  is-contr-total-equiv-Prop P =
    is-contr-equiv'
      ( Σ (Prop l1) (λ Q → P ⇔ Q))
      ( equiv-tot (equiv-equiv-iff P))
      ( is-contr-total-iff P)
```

### The type of propositions is a set

```agda
is-set-type-Prop : {l : Level} → is-set (Prop l)
is-set-type-Prop {l} P Q =
  is-prop-equiv
    ( propositional-extensionality P Q)
    ( is-prop-logical-equivalence P Q)

Prop-Set : (l : Level) → Set (lsuc l)
pr1 (Prop-Set l) = Prop l
pr2 (Prop-Set l) = is-set-type-Prop
```

### The canonical type family over `Prop` is univalent

```agda
is-univalent-type-Prop : {l : Level} → is-univalent (type-Prop {l})
is-univalent-type-Prop {l} P =
  fundamental-theorem-id
    ( is-contr-total-equiv-Prop P)
    ( λ Q → equiv-tr type-Prop)
```

### The type of true propositions is contractible

```agda
abstract
  is-contr-total-true-Prop :
    {l1 : Level} → is-contr (Σ (Prop l1) (λ P → type-Prop P))
  is-contr-total-true-Prop {l1} =
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
      ( is-contr-total-iff (raise-unit-Prop l1))
```

### The type of false propositions is contractible

```agda
abstract
  is-contr-total-false-Prop :
    {l1 : Level} → is-contr (Σ (Prop l1) (λ P → type-Prop (neg-Prop P)))
  is-contr-total-false-Prop {l1} =
    is-contr-equiv
      ( Σ (Prop l1) (λ P → raise-empty-Prop l1 ⇔ P))
      ( equiv-tot
        ( λ P →
          inv-equiv
            ( ( inv-equiv
                ( equiv-postcomp (type-Prop P) (equiv-raise l1 empty))) ∘e
              ( left-unit-law-prod-is-contr
                ( universal-property-empty-is-empty
                  ( raise-empty l1)
                  ( is-empty-raise-empty)
                  ( type-Prop P))))))
      ( is-contr-total-iff (raise-empty-Prop l1))
```
