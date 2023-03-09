# Subposets

```agda
module order-theory.subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
open import order-theory.subpreorders
```

</details>

## Definitions

### Subposets

```agda

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (S : element-Poset X → Prop l3)
  where

  element-sub-Poset : UU (l1 ⊔ l3)
  element-sub-Poset = element-sub-Preorder (preorder-Poset X) S

  eq-element-sub-Poset :
    (x y : element-sub-Poset) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-sub-Poset = eq-element-sub-Preorder (preorder-Poset X) S

  leq-sub-poset-Prop : (x y : element-sub-Poset) → Prop l2
  leq-sub-poset-Prop = leq-sub-preorder-Prop (preorder-Poset X) S

  leq-sub-Poset : (x y : element-sub-Poset) → UU l2
  leq-sub-Poset = leq-sub-Preorder (preorder-Poset X) S

  is-prop-leq-sub-Poset :
    (x y : element-sub-Poset) → is-prop (leq-sub-Poset x y)
  is-prop-leq-sub-Poset = is-prop-leq-sub-Preorder (preorder-Poset X) S

  refl-leq-sub-Poset : (x : element-sub-Poset) → leq-sub-Poset x x
  refl-leq-sub-Poset = refl-leq-sub-Preorder (preorder-Poset X) S

  transitive-leq-sub-Poset :
    (x y z : element-sub-Poset) →
    leq-sub-Poset y z → leq-sub-Poset x y → leq-sub-Poset x z
  transitive-leq-sub-Poset = transitive-leq-sub-Preorder (preorder-Poset X) S

  antisymmetric-leq-sub-Poset :
    (x y : element-sub-Poset) → leq-sub-Poset x y → leq-sub-Poset y x → Id x y
  antisymmetric-leq-sub-Poset x y H K =
    eq-element-sub-Poset x y (antisymmetric-leq-Poset X (pr1 x) (pr1 y) H K)

  sub-Poset : Poset (l1 ⊔ l3) l2
  pr1 sub-Poset = element-sub-Poset
  pr1 (pr2 sub-Poset) = leq-sub-poset-Prop
  pr1 (pr1 (pr2 (pr2 sub-Poset))) = refl-leq-sub-Poset
  pr2 (pr1 (pr2 (pr2 sub-Poset))) = transitive-leq-sub-Poset
  pr2 (pr2 (pr2 sub-Poset)) = antisymmetric-leq-sub-Poset

```

### Inclusion of sub-posets

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  module _
    {l3 l4 : Level} (S : element-Poset X → Prop l3)
    (T : element-Poset X → Prop l4)
    where

    inclusion-sub-poset-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-poset-Prop =
      inclusion-sub-preorder-Prop (preorder-Poset X) S T

    inclusion-sub-Poset : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-sub-Poset = inclusion-sub-Preorder (preorder-Poset X) S T

    is-prop-inclusion-sub-Poset : is-prop inclusion-sub-Poset
    is-prop-inclusion-sub-Poset =
      is-prop-inclusion-sub-Preorder (preorder-Poset X) S T

  refl-inclusion-sub-Poset :
    {l3 : Level} (S : element-Poset X → Prop l3) →
    inclusion-sub-Poset S S
  refl-inclusion-sub-Poset = refl-inclusion-sub-Preorder (preorder-Poset X)

  transitive-inclusion-sub-Poset :
    {l3 l4 l5 : Level} (S : element-Poset X → Prop l3)
    (T : element-Poset X → Prop l4)
    (U : element-Poset X → Prop l5) →
    inclusion-sub-Poset T U → inclusion-sub-Poset S T →
    inclusion-sub-Poset S U
  transitive-inclusion-sub-Poset =
    transitive-inclusion-sub-Preorder (preorder-Poset X)

  sub-poset-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (sub-poset-Preorder l) = element-Poset X → Prop l
  pr1 (pr2 (sub-poset-Preorder l)) = inclusion-sub-poset-Prop
  pr1 (pr2 (pr2 (sub-poset-Preorder l))) = refl-inclusion-sub-Poset
  pr2 (pr2 (pr2 (sub-poset-Preorder l))) = transitive-inclusion-sub-Poset
```
