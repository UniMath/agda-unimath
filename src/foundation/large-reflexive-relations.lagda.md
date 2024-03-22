# Large reflexive relations

```agda
module foundation.large-reflexive-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A {{#concept "large reflexive relation" Agda=Large-Reflexive-Relation}} on on a
family of types indexed by universe levels `A` is a type-valued
[large binary relation](foundation.binary-relations.md) `R`
[equipped](foundation.structure.md) with a proof
`r : {l : Level} (x : A l) → R x x`.

## Definition

### The predicate of being a reflexive relation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation β A)
  where

  is-reflexive-Large-Relation : UUω
  is-reflexive-Large-Relation = {l : Level} (x : A l) → R x x
```

### The predicate of being a reflexive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be _reflexive_ if
its underlying relation is reflexive.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : (l : Level) → UU (α l))
  (R : Large-Relation-Prop β A)
  where

  is-reflexive-Large-Relation-Prop : UUω
  is-reflexive-Large-Relation-Prop =
    is-reflexive-Large-Relation A (large-relation-Large-Relation-Prop A R)
```

### Large reflexive relations

```agda
record
  Large-Reflexive-Relation
  {α : Level → Level}
  (β : Level → Level → Level)
  (A : (l : Level) → UU (α l))
  : UUω
  where

  field
    rel-Large-Reflexive-Relation :
      Large-Relation β A

    is-reflexive-Large-Reflexive-Relation :
      is-reflexive-Large-Relation A rel-Large-Reflexive-Relation
```
