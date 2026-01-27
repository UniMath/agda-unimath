# Strict subpreorders

```agda
module order-theory.strict-subpreorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strict-preorders
```

</details>

## Idea

Any [subtype](foundation.subtypes.md) of the underlying type of a
[strict preorder](order-theory.strict-preorders.md) inherits the structure of a
strict preorder.

## Definition

```agda
Strict-Subpreorder :
  {l1 l2 : Level} (l : Level) → Strict-Preorder l1 l2 → UU (l1 ⊔ lsuc l)
Strict-Subpreorder l P = subtype l (type-Strict-Preorder P)

module _
  {l1 l2 l3 : Level}
  (P : Strict-Preorder l1 l2)
  (S : Strict-Subpreorder l3 P)
  where

  type-Strict-Subpreorder : UU (l1 ⊔ l3)
  type-Strict-Subpreorder = type-subtype S

  le-prop-Strict-Subpreorder :
    Relation-Prop l2 type-Strict-Subpreorder
  le-prop-Strict-Subpreorder (x , x∈S) (y , y∈S) =
    le-prop-Strict-Preorder P x y

  le-Strict-Subpreorder : Relation l2 type-Strict-Subpreorder
  le-Strict-Subpreorder =
    type-Relation-Prop le-prop-Strict-Subpreorder

  is-irreflexive-le-Strict-Subpreorder :
    is-irreflexive le-Strict-Subpreorder
  is-irreflexive-le-Strict-Subpreorder (x , x∈S) =
    is-irreflexive-le-Strict-Preorder P x

  is-transitive-le-Strict-Subpreorder :
    is-transitive le-Strict-Subpreorder
  is-transitive-le-Strict-Subpreorder (x , x∈S) (y , y∈S) (z , z∈S) =
    is-transitive-le-Strict-Preorder P x y z

  strict-preorder-Strict-Subpreorder : Strict-Preorder (l1 ⊔ l3) l2
  strict-preorder-Strict-Subpreorder =
    ( type-Strict-Subpreorder ,
      le-prop-Strict-Subpreorder ,
      is-irreflexive-le-Strict-Subpreorder ,
      is-transitive-le-Strict-Subpreorder)
```
