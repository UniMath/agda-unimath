# Chain union

```agda
module order-theory.chains-union where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.chains-posets
open import order-theory.maximal-elements-posets
open import order-theory.posets
open import order-theory.subposets
open import order-theory.subtypes-leq-posets
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (C : chain-Poset l3 (subtypes-leq-Poset l2 A))
  where

  in-chain-union : subtype (l1 ⊔ lsuc l2 ⊔ l3) A
  in-chain-union a =
    exists-Prop
      ( type-chain-Poset (subtypes-leq-Poset l2 A) C)
      ( λ x →
        ( inclusion-subtype
          ( sub-preorder-chain-Poset (subtypes-leq-Poset l2 A) C)
          ( x)
          ( a)))

  is-chain-union :
    {l4 : Level} (u : subtype l4 A) → UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
  is-chain-union = equiv-subtypes in-chain-union

  chain-union-is-upper-bound :
    (u : subtype l2 A) →
    is-chain-union u →
    is-chain-upper-bound (subtypes-leq-Poset l2 A) C u
  chain-union-is-upper-bound u u-is-union s a a-in-s =
    map-equiv (u-is-union a) (intro-∃ s a-in-s)

  module _
    (prop-resize : propositional-resizing l2 (l1 ⊔ lsuc l2 ⊔ l3))
    where

    chain-union : Σ (subtype l2 A) is-chain-union
    pr1 chain-union = resize prop-resize ∘ in-chain-union
    pr2 chain-union = inv-equiv ∘ is-equiv-resize prop-resize ∘ in-chain-union

module _
  {l1 l2 l3 l4 : Level} (A : UU l1)
  (S : subtype l3 (subtype l2 A))
  (C : chain-Poset l4 (poset-Subposet (subtypes-leq-Poset l2 A) S))
  where

  private
    poset : Poset (l1 ⊔ lsuc l2 ⊔ l3) (l1 ⊔ l2)
    poset = poset-Subposet (subtypes-leq-Poset l2 A) S

  in-sub-chain-union : subtype (l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4) A
  in-sub-chain-union a =
    exists-Prop
      ( type-chain-Poset poset C)
      ( λ x →
        ( inclusion-subtype S
          ( inclusion-subtype (sub-preorder-chain-Poset poset C) x) a))

  is-sub-chain-union : (u : type-Poset poset) → UU (l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
  is-sub-chain-union u =
    equiv-subtypes in-sub-chain-union (inclusion-subtype S u)

  sub-chain-union-is-upper-bound :
    (u : type-Poset poset) →
    is-sub-chain-union u →
    is-chain-upper-bound poset C u
  sub-chain-union-is-upper-bound u u-is-union s a a-in-s =
    map-equiv (u-is-union a) (intro-∃ s a-in-s)

  module _
    (x : type-chain-Poset poset C)
    (subtype-monotic :
      (y : subtype l2 A) →
      inclusion-subtype S
        ( inclusion-subtype (sub-preorder-chain-Poset poset C) x) ⊆ y →
      is-in-subtype S y)
    (prop-resize : propositional-resizing l2 (l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4))
    where

    sub-chain-union : Σ (type-Poset poset) is-sub-chain-union
    pr1 (pr1 sub-chain-union) =
      resize prop-resize ∘ in-sub-chain-union
    pr2 (pr1 sub-chain-union) =
      subtype-monotic
        ( resize prop-resize ∘ in-sub-chain-union)
        ( λ a a-in-x →
          ( map-equiv
            ( inv-equiv (is-equiv-resize prop-resize (in-sub-chain-union a)))
            ( intro-∃ x a-in-x)))
    pr2 sub-chain-union =
      inv-equiv ∘ is-equiv-resize prop-resize ∘ in-sub-chain-union
```
