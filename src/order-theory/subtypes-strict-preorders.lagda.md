# Subtypes of strict preorders

```agda
module order-theory.subtypes-strict-preorders where
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
subtype-Strict-Preorder l P = subtype l (type-Strict-Preorder P)

module _
  {l1 l2 l3 : Level}
  (P : Strict-Preorder l1 l2)
  (S : subtype-Strict-Preorder l3 P)
  where

  type-subtype-Strict-Preorder : UU (l1 ⊔ l3)
  type-subtype-Strict-Preorder = type-subtype S

  le-prop-subtype-Strict-Preorder :
    Relation-Prop l2 type-subtype-Strict-Preorder
  le-prop-subtype-Strict-Preorder (x , x∈S) (y , y∈S) =
    le-prop-Strict-Preorder P x y

  le-subtype-Strict-Preorder : Relation l2 type-subtype-Strict-Preorder
  le-subtype-Strict-Preorder =
    type-Relation-Prop le-prop-subtype-Strict-Preorder

  is-irreflexive-le-subtype-Strict-Preorder :
    is-irreflexive le-subtype-Strict-Preorder
  is-irreflexive-le-subtype-Strict-Preorder (x , x∈S) =
    is-irreflexive-le-Strict-Preorder P x

  is-transitive-le-subtype-Strict-Preorder :
    is-transitive le-subtype-Strict-Preorder
  is-transitive-le-subtype-Strict-Preorder (x , x∈S) (y , y∈S) (z , z∈S) =
    is-transitive-le-Strict-Preorder P x y z

  strict-preorder-subtype-Strict-Preorder : Strict-Preorder (l1 ⊔ l3) l2
  strict-preorder-subtype-Strict-Preorder =
    ( type-subtype-Strict-Preorder ,
      le-prop-subtype-Strict-Preorder ,
      is-irreflexive-le-subtype-Strict-Preorder ,
      is-transitive-le-subtype-Strict-Preorder)
```
