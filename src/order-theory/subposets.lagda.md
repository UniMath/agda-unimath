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

  element-Subposet : UU (l1 ⊔ l3)
  element-Subposet = element-Subpreorder (preorder-Poset X) S

  eq-element-Subposet :
    (x y : element-Subposet) → Id (pr1 x) (pr1 y) → Id x y
  eq-element-Subposet = eq-element-Subpreorder (preorder-Poset X) S

  leq-Subposet-Prop : (x y : element-Subposet) → Prop l2
  leq-Subposet-Prop = leq-Subpreorder-Prop (preorder-Poset X) S

  leq-Subposet : (x y : element-Subposet) → UU l2
  leq-Subposet = leq-Subpreorder (preorder-Poset X) S

  is-prop-leq-Subposet :
    (x y : element-Subposet) → is-prop (leq-Subposet x y)
  is-prop-leq-Subposet = is-prop-leq-Subpreorder (preorder-Poset X) S

  refl-leq-Subposet : (x : element-Subposet) → leq-Subposet x x
  refl-leq-Subposet = refl-leq-Subpreorder (preorder-Poset X) S

  transitive-leq-Subposet :
    (x y z : element-Subposet) →
    leq-Subposet y z → leq-Subposet x y → leq-Subposet x z
  transitive-leq-Subposet = transitive-leq-Subpreorder (preorder-Poset X) S

  antisymmetric-leq-Subposet :
    (x y : element-Subposet) → leq-Subposet x y → leq-Subposet y x → Id x y
  antisymmetric-leq-Subposet x y H K =
    eq-element-Subposet x y (antisymmetric-leq-Poset X (pr1 x) (pr1 y) H K)

  Subposet : Poset (l1 ⊔ l3) l2
  pr1 Subposet = element-Subposet
  pr1 (pr2 Subposet) = leq-Subposet-Prop
  pr1 (pr1 (pr2 (pr2 Subposet))) = refl-leq-Subposet
  pr2 (pr1 (pr2 (pr2 Subposet))) = transitive-leq-Subposet
  pr2 (pr2 (pr2 Subposet)) = antisymmetric-leq-Subposet
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

    inclusion-Subposet-Prop : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-Subposet-Prop =
      inclusion-Subpreorder-Prop (preorder-Poset X) S T

    inclusion-Subposet : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Subposet = inclusion-Subpreorder (preorder-Poset X) S T

    is-prop-inclusion-Subposet : is-prop inclusion-Subposet
    is-prop-inclusion-Subposet =
      is-prop-inclusion-Subpreorder (preorder-Poset X) S T

  refl-inclusion-Subposet :
    {l3 : Level} (S : element-Poset X → Prop l3) →
    inclusion-Subposet S S
  refl-inclusion-Subposet = refl-inclusion-Subpreorder (preorder-Poset X)

  transitive-inclusion-Subposet :
    {l3 l4 l5 : Level} (S : element-Poset X → Prop l3)
    (T : element-Poset X → Prop l4)
    (U : element-Poset X → Prop l5) →
    inclusion-Subposet T U → inclusion-Subposet S T →
    inclusion-Subposet S U
  transitive-inclusion-Subposet =
    transitive-inclusion-Subpreorder (preorder-Poset X)

  sub-poset-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (sub-poset-Preorder l) = element-Poset X → Prop l
  pr1 (pr2 (sub-poset-Preorder l)) = inclusion-Subposet-Prop
  pr1 (pr2 (pr2 (sub-poset-Preorder l))) = refl-inclusion-Subposet
  pr2 (pr2 (pr2 (sub-poset-Preorder l))) = transitive-inclusion-Subposet
```
