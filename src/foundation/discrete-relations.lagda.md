# Discrete relations

```agda
module foundation.discrete-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.reflexive-relations
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A [relation](foundation.binary-relations.md) `R` on `A` is said to be
{{#concept "discrete" Disambiguation="binary relations valued in types" Agda=is-discrete-Relation}}
if, for every element `x : A`, the type family `R x` is
[torsorial](foundation-core.torsorial-type-families.md). In other words, the
[dependent sum](foundation.dependent-pair-types.md) `Σ (y : A), (R x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`. The
{{#concept "standard discrete relation" Disambiguation="binary relations valued in types"}}
on a type `X` is the relation defined by
[identifications](foundation-core.identity-types.md),

```text
  R x y := (x ＝ y).
```

## Definitions

### The predicate on relations of being discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-discrete-prop-Relation : Prop (l1 ⊔ l2)
  is-discrete-prop-Relation = Π-Prop A (λ x → is-torsorial-Prop (R x))

  is-discrete-Relation : UU (l1 ⊔ l2)
  is-discrete-Relation =
    type-Prop is-discrete-prop-Relation

  is-prop-is-discrete-Relation : is-prop is-discrete-Relation
  is-prop-is-discrete-Relation =
    is-prop-type-Prop is-discrete-prop-Relation
```

### The predicate on reflexive relations of being discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  is-discrete-prop-Reflexive-Relation : Prop (l1 ⊔ l2)
  is-discrete-prop-Reflexive-Relation =
    is-discrete-prop-Relation (rel-Reflexive-Relation R)

  is-discrete-Reflexive-Relation : UU (l1 ⊔ l2)
  is-discrete-Reflexive-Relation =
    type-Prop is-discrete-prop-Reflexive-Relation

  is-prop-is-discrete-Reflexive-Relation :
    is-prop is-discrete-Reflexive-Relation
  is-prop-is-discrete-Reflexive-Relation =
    is-prop-type-Prop is-discrete-prop-Reflexive-Relation
```

### The standard discrete relation on a type

```agda
module _
  {l : Level} (A : UU l)
  where

  is-discrete-Id-Relation : is-discrete-Relation (Id {A = A})
  is-discrete-Id-Relation = is-torsorial-Id
```
