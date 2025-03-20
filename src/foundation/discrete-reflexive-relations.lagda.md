# Discrete reflexive relations

```agda
open import foundation.function-extensionality-axiom

module
  foundation.discrete-reflexive-relations
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations funext
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.reflexive-relations funext
open import foundation.torsorial-type-families funext
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A [reflexive relation](foundation.binary-relations.md) `R` on `A` is said to be
{{#concept "discrete" Disambiguation="reflexive relations valued in types" Agda=is-discrete-Reflexive-Relation}}
if, for every element `x : A`, the type family `R x` is
[torsorial](foundation-core.torsorial-type-families.md). In other words, the
[dependent sum](foundation.dependent-pair-types.md) `Σ (y : A), (R x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`.

The {{#concept "standard discrete reflexive relation"}} on a type `X` is the
relation defined by [identifications](foundation-core.identity-types.md),

```text
  R x y := (x ＝ y).
```

## Definitions

### The predicate on reflexive relations of being discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  is-discrete-prop-Reflexive-Relation : Prop (l1 ⊔ l2)
  is-discrete-prop-Reflexive-Relation =
    Π-Prop A (λ a → is-torsorial-Prop (rel-Reflexive-Relation R a))

  is-discrete-Reflexive-Relation : UU (l1 ⊔ l2)
  is-discrete-Reflexive-Relation =
    type-Prop is-discrete-prop-Reflexive-Relation

  is-prop-is-discrete-Reflexive-Relation :
    is-prop is-discrete-Reflexive-Relation
  is-prop-is-discrete-Reflexive-Relation =
    is-prop-type-Prop is-discrete-prop-Reflexive-Relation
```

## Properties

### The identity relation is discrete

```agda
module _
  {l : Level} (A : UU l)
  where

  is-discrete-Id-Reflexive-Relation :
    is-discrete-Reflexive-Relation (Id-Reflexive-Relation A)
  is-discrete-Id-Reflexive-Relation = is-torsorial-Id
```

## See also

- [Discrete binary relations](foundation.discrete-binary-relations.md)
- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
