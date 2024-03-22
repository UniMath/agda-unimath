# Large ransitive binary relations

```agda
module foundation.large-transitive-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A
{{#concept "large-transitive binary relation" Agda=is-transitive-Large-Relation Agda=Large-Transitive-Relation}}
is a [large relation](foundation.large-binary-relations.md) `R` on `A` such that
for every triple of elements `x`, `y` and `z` in `A`, there is a binary
operation

```text
  R y z → R x y → R x z.
```

## Definition

### The structure of being a large transitive relation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation β A)
  where

  is-transitive-Large-Relation : UUω
  is-transitive-Large-Relation =
    {l1 l2 l3 : Level} (x : A l1) (y : A l2) (z : A l3) → R y z → R x y → R x z

```

### The predicate on large relations valued in propositions of being transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop β A)
  where

  is-transitive-Large-Relation-Prop : UUω
  is-transitive-Large-Relation-Prop =
    is-transitive-Large-Relation A (large-relation-Large-Relation-Prop A R)

```

### The type of large transitive relations

```agda
record
  Large-Transitive-Relation
  {α : Level → Level}
  (β : Level → Level → Level)
  (A : (l : Level) → UU (α l))
  : UUω
  where

  field
    rel-Large-Transitive-Relation :
      Large-Relation β A

    is-transitive-Large-Transitive-Relation :
      is-transitive-Large-Relation A rel-Large-Transitive-Relation
```
