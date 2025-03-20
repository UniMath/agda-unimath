# The orbit-stabilizer theorem for concrete groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.orbit-stabilizer-theorem-concrete-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext
open import group-theory.concrete-groups funext
open import group-theory.mere-equivalences-concrete-group-actions funext
open import group-theory.stabilizer-groups-concrete-group-actions funext

open import structured-types.pointed-types
```

</details>

## Idea

The orbit stabilizer theorem for concrete groups asserts that the type
`Orbit(x)` of orbits of an element `x : X *` is deloopable and fits in a fiber
sequence

```text
  BG_x ----> BG ----> B(Orbit(x))
```

To see that this is indeed a formulation of the orbit-stabilizer theorem, note
that the delooping of `Orbit(x)` gives `Orbit(x)` the structure of a group.
Furthermore, this fiber sequence induces a short exact sequence

```text
  G_x ----> G ----> Orbit(x),
```

which induces a bijection from the cosets of the stabilizer subgroup `G_x` of
`G` to the type `Orbit(x)`.

## Definitions

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  classifying-type-quotient-stabilizer-action-Concrete-Group :
    type-action-Concrete-Group G X → UU (lsuc l1 ⊔ lsuc l2)
  classifying-type-quotient-stabilizer-action-Concrete-Group x =
    Σ ( action-Concrete-Group (l1 ⊔ l2) G)
      ( mere-equiv-action-Concrete-Group G
        ( action-stabilizer-action-Concrete-Group G X x))

  point-classifying-type-quotient-stabilizer-action-Concrete-Group :
    (x : type-action-Concrete-Group G X) →
    classifying-type-quotient-stabilizer-action-Concrete-Group x
  pr1 (point-classifying-type-quotient-stabilizer-action-Concrete-Group x) =
    action-stabilizer-action-Concrete-Group G X x
  pr2 (point-classifying-type-quotient-stabilizer-action-Concrete-Group x) =
    refl-mere-equiv-action-Concrete-Group G
      (action-stabilizer-action-Concrete-Group G X x)

  classifying-pointed-type-stabilizer-action-Concrete-Group :
    (x : type-action-Concrete-Group G X) →
    Pointed-Type (lsuc l1 ⊔ lsuc l2)
  pr1 (classifying-pointed-type-stabilizer-action-Concrete-Group x) =
    classifying-type-quotient-stabilizer-action-Concrete-Group x
  pr2 (classifying-pointed-type-stabilizer-action-Concrete-Group x) =
    point-classifying-type-quotient-stabilizer-action-Concrete-Group x
```
