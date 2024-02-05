# Maximal elements in posets

```agda
module order-theory.maximal-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import order-theory.chains-posets
open import order-theory.posets
open import order-theory.subposets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-maximal-element-Poset-Prop : type-Poset X → Prop (l1 ⊔ l2)
  is-maximal-element-Poset-Prop x =
    Π-Prop
      ( type-Poset X)
      ( λ y → function-Prop (leq-Poset X x y) (y ＝ x , is-set-type-Poset X y x))

  is-maximal-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-maximal-element-Poset x = type-Prop (is-maximal-element-Poset-Prop x)

  is-prop-is-maximal-element-Poset :
    (x : type-Poset X) → is-prop (is-maximal-element-Poset x)
  is-prop-is-maximal-element-Poset x =
    is-prop-type-Prop (is-maximal-element-Poset-Prop x)

  has-maximal-element-Poset : UU (l1 ⊔ l2)
  has-maximal-element-Poset = Σ (type-Poset X) is-maximal-element-Poset

module _
  (l1 l2 l3 : Level)
  where

  Zorn-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn-Prop =
    Π-Prop
      ( Poset l1 l2)
      ( λ X →
        ( function-Prop
          ( is-inhabited (type-Poset X))
          ( function-Prop
            ( (C : chain-Poset l3 X) →
              is-inhabited (type-chain-Poset X C) →
              has-chain-upper-bound X C)
            ( ∃-Prop (type-Poset X) (is-maximal-element-Poset X)))))

  Zorn : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn = type-Prop Zorn-Prop

  Zorn'-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn'-Prop =
    Π-Prop
      ( Poset l1 l2)
      ( λ X →
          ( function-Prop
            ( (C : chain-Poset l3 X) → has-chain-upper-bound X C)
            ( ∃-Prop (type-Poset X) (is-maximal-element-Poset X))))

  Zorn' : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn' = type-Prop Zorn'-Prop

  Zorn'-Zorn : Zorn → Zorn'
  Zorn'-Zorn zorn X H =
    zorn X
      ( apply-universal-property-trunc-Prop
        ( H
          ( pair
            (λ _ → raise-empty-Prop l3)
            (λ (_ , f) → raise-ex-falso l3 f)))
        ( is-inhabited-Prop (type-Poset X))
        ( λ (x , _) → unit-trunc-Prop x))
      ( λ C _ → H C)

  module _
    (lem : LEM (l1 ⊔ l3))
    where

    Zorn-Zorn' : Zorn' → Zorn
    Zorn-Zorn' zorn' X is-inhabited-X H = zorn' X chain-upper-bound
      where
      chain-upper-bound : (C : chain-Poset l3 X) → has-chain-upper-bound X C
      chain-upper-bound C with lem (is-inhabited-Prop (type-chain-Poset X C))
      ... | inl is-inhabited-C = H C is-inhabited-C
      ... | inr is-empty-C =
        apply-universal-property-trunc-Prop
          ( is-inhabited-X)
          ( has-chain-upper-bound-Prop X C)
          ( λ x →
            ( intro-∃ x
              ( λ (y , y-in-C) → ex-falso (is-empty-C (intro-∃ y y-in-C)))))

    Zorn-iff-Zorn' : Zorn-Prop ⇔ Zorn'-Prop
    pr1 (Zorn-iff-Zorn') = Zorn'-Zorn
    pr2 (Zorn-iff-Zorn') = Zorn-Zorn'
```
