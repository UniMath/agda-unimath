# Zorn's lemma

```agda
module order-theory.zorn where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions

open import order-theory.chains-posets
open import order-theory.maximal-elements-posets
open import order-theory.posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  (l1 l2 l3 : Level)
  where

  Zorn-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn-Prop =
    Π-Prop
      ( Poset l1 l2)
      ( λ X →
          ( function-Prop
            ( (C : chain-Poset l3 X) → has-chain-upper-bound X C)
            ( ∃ (type-Poset X) (is-maximal-element-Poset-Prop X))))

  Zorn : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn = type-Prop Zorn-Prop

  Zorn-non-empty-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn-non-empty-Prop =
    Π-Prop
      ( Poset l1 l2)
      ( λ X →
        ( function-Prop
          ( is-inhabited (type-Poset X))
          ( function-Prop
            ( (C : chain-Poset l3 X) →
              is-inhabited (type-chain-Poset X C) →
              has-chain-upper-bound X C)
            ( ∃ (type-Poset X) (is-maximal-element-Poset-Prop X)))))

  Zorn-non-empty : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  Zorn-non-empty = type-Prop Zorn-non-empty-Prop

  Zorn-Zorn-non-empty : Zorn-non-empty → Zorn
  Zorn-Zorn-non-empty zorn X H =
    zorn X
      ( apply-universal-property-trunc-Prop
        ( H
          ( pair
            ( λ _ → raise-empty-Prop l3)
            ( λ (_ , f) → raise-ex-falso l3 f)))
        ( is-inhabited-Prop (type-Poset X))
        ( λ (x , _) → unit-trunc-Prop x))
      ( λ C _ → H C)

  module _
    (lem : LEM (l1 ⊔ l3))
    where

    Zorn-non-empty-Zorn : Zorn → Zorn-non-empty
    Zorn-non-empty-Zorn zorn X is-inhabited-X H = zorn X chain-upper-bound
      where
      chain-upper-bound : (C : chain-Poset l3 X) → has-chain-upper-bound X C
      chain-upper-bound C with lem (is-inhabited-Prop (type-chain-Poset X C))
      ... | inl is-inhabited-C = H C is-inhabited-C
      ... | inr is-empty-C =
        apply-universal-property-trunc-Prop
          ( is-inhabited-X)
          ( has-chain-upper-bound-Prop X C)
          ( λ x →
            ( intro-exists x
              ( λ (y , y-in-C) →
                ( ex-falso (is-empty-C (intro-exists y y-in-C))))))

    iff-Zorn-non-empty-Zorn : type-iff-Prop Zorn-non-empty-Prop Zorn-Prop
    pr1 (iff-Zorn-non-empty-Zorn) = Zorn-Zorn-non-empty
    pr2 (iff-Zorn-non-empty-Zorn) = Zorn-non-empty-Zorn
```
