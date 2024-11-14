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

A [reflexive relation](foundation.binary-relations.md) `R` on `A` is said to be
{{#concept "discrete" Disambiguation="reflexive relations valued in types" Agda=is-discrete-Reflexive-Relation}}
if, for every element `x : A`, the type family `R x` is
[torsorial](foundation-core.torsorial-type-families.md). In other words, the
[dependent sum](foundation.dependent-pair-types.md) `Σ (y : A), (R x y)` is
[contractible](foundation-core.contractible-types.md) for every `x`.

The
{{#concept "standard discrete relation" Disambiguation="binary relations valued in types"}}
on a type `X` is the relation defined by
[identifications](foundation-core.identity-types.md),

```text
  R x y := (x ＝ y).
```

More generally, a binary relation `R` on `A` is said to be
{{#concept "discrete" Disambiguation="binary relation" Agda=is-discrete-Relation}}
if it is reflexive and discrete as a reflexive relation. Being discrete for
binary relations is therefore not a property.

Note that the directed relation on
[natural numbers](elementary-number-theory.natural-numbers.md) and
`E m n := (m + 1 ＝ n)` as in

```text
  0 ---> 1 ---> 2 ---> ⋯
```

satisfies the condition that the type family `E m` is torsorial for every
`m : ℕ`, simply because the relation `E` is a
[functional correspondence](foundation.functional-correspondences.md). The
condition that a binary relation is torsorial is therefore not sufficient as a
condition of being discrete.

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

### The predicate on relations of being discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-discrete-Relation : UU (l1 ⊔ l2)
  is-discrete-Relation =
    Σ (is-reflexive R) (λ r → is-discrete-Reflexive-Relation (R , r))
```

### The standard discrete relation on a type

```agda
module _
  {l : Level} (A : UU l)
  where

  is-discrete-Id-Relation : is-discrete-Relation (Id {A = A})
  pr1 is-discrete-Id-Relation x = refl
  pr2 is-discrete-Id-Relation = is-torsorial-Id
```
