# Subposets

```agda
module order-theory.subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
open import order-theory.subpreorders
```

</details>

## Idea

A **subposet** of a poset `P` is a subtype of `P`. By restriction of the
ordering on `P`, subposets have again the structure of a poset.

## Definitions

### Subposets

```agda
Subposet :
  {l1 l2 : Level} (l3 : Level) → Poset l1 l2 → UU (l1 ⊔ lsuc l3)
Subposet l3 P = Subpreorder l3 (preorder-Poset P)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (S : Subposet l3 X)
  where

  type-Subposet : UU (l1 ⊔ l3)
  type-Subposet = type-Subpreorder (preorder-Poset X) S

  eq-type-Subposet :
    (x y : type-Subposet) → Id (pr1 x) (pr1 y) → x ＝ y
  eq-type-Subposet = eq-type-Subpreorder (preorder-Poset X) S

  leq-Subposet-Prop : (x y : type-Subposet) → Prop l2
  leq-Subposet-Prop = leq-Subpreorder-Prop (preorder-Poset X) S

  leq-Subposet : (x y : type-Subposet) → UU l2
  leq-Subposet = leq-Subpreorder (preorder-Poset X) S

  is-prop-leq-Subposet :
    (x y : type-Subposet) → is-prop (leq-Subposet x y)
  is-prop-leq-Subposet = is-prop-leq-Subpreorder (preorder-Poset X) S

  refl-leq-Subposet : is-reflexive leq-Subposet
  refl-leq-Subposet = refl-leq-Subpreorder (preorder-Poset X) S

  transitive-leq-Subposet : is-transitive leq-Subposet
  transitive-leq-Subposet = transitive-leq-Subpreorder (preorder-Poset X) S

  antisymmetric-leq-Subposet : is-antisymmetric leq-Subposet
  antisymmetric-leq-Subposet x y H K =
    eq-type-Subposet x y (antisymmetric-leq-Poset X (pr1 x) (pr1 y) H K)

  preorder-Subposet : Preorder (l1 ⊔ l3) l2
  pr1 preorder-Subposet = type-Subposet
  pr1 (pr2 preorder-Subposet) = leq-Subposet-Prop
  pr1 (pr2 (pr2 preorder-Subposet)) = refl-leq-Subposet
  pr2 (pr2 (pr2 preorder-Subposet)) = transitive-leq-Subposet

  poset-Subposet : Poset (l1 ⊔ l3) l2
  pr1 poset-Subposet = preorder-Subposet
  pr2 poset-Subposet = antisymmetric-leq-Subposet
```

### Inclusion of subposets

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  module _
    {l3 l4 : Level} (S : Subposet l3 X) (T : Subposet l4 X)
    where

    inclusion-prop-Subposet : Prop (l1 ⊔ l3 ⊔ l4)
    inclusion-prop-Subposet =
      inclusion-prop-Subpreorder (preorder-Poset X) S T

    inclusion-Subposet : UU (l1 ⊔ l3 ⊔ l4)
    inclusion-Subposet = inclusion-Subpreorder (preorder-Poset X) S T

    is-prop-inclusion-Subposet : is-prop inclusion-Subposet
    is-prop-inclusion-Subposet =
      is-prop-inclusion-Subpreorder (preorder-Poset X) S T

  refl-inclusion-Subposet :
    {l3 : Level} (S : Subposet l3 X) → inclusion-Subposet S S
  refl-inclusion-Subposet = refl-inclusion-Subpreorder (preorder-Poset X)

  transitive-inclusion-Subposet :
    {l3 l4 l5 : Level}
    (S : Subposet l3 X) (T : Subposet l4 X) (U : Subposet l5 X) →
    inclusion-Subposet T U →
    inclusion-Subposet S T →
    inclusion-Subposet S U
  transitive-inclusion-Subposet =
    transitive-inclusion-Subpreorder (preorder-Poset X)

  subposet-Preorder : (l : Level) → Preorder (l1 ⊔ lsuc l) (l1 ⊔ l)
  pr1 (subposet-Preorder l) = Subposet l X
  pr1 (pr2 (subposet-Preorder l)) = inclusion-prop-Subposet
  pr1 (pr2 (pr2 (subposet-Preorder l))) = refl-inclusion-Subposet
  pr2 (pr2 (pr2 (subposet-Preorder l))) = transitive-inclusion-Subposet
```
