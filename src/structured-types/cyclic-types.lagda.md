# Cyclic types

```agda
module structured-types.cyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.iterating-automorphisms
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import structured-types.sets-equipped-with-automorphisms
```

</details>

## Idea

A {{#concept "cyclic set" Agda=Cyclic-Set}} consists of a
[set](foundation.sets.md) `A` [equipped](foundation.structure.md) with an
[automorphism](foundation.automorphisms.md) `e : A ≃ A` which is _cyclic_ in the
sense that its underlying set is [inhabited](foundation.inhabited-types.md) and
the map

```text
  k ↦ eᵏ x
```

is [surjective](foundation.surjective-maps.md) for every `x : A`. There are
several equivalent ways of stating the concept of cyclic sets. Two further
equivalent ways are:

- A cyclic set is a
  [connected set bundle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
  over the [circle](synthetic-homotopy-theory.circle.md).
- A cyclic set is a set equipped with a
  [transitive](group-theory.transitive-group-actions.md) `ℤ`-action.
- A cyclic set is a set which is a [`C`-torsor](group-theory.torsors.md) for
  some [cyclic group](group-theory.cyclic-groups.md) `C`.

Note that the [empty set](foundation.empty-types.md) equipped with the identity
automorphism is not considered to be a cyclic set, for reasons similar to those
of not considering empty group actions to be transitive.

## Definition

### The predicate of being a cyclic set

```agda
module _
  {l : Level} (X : Set-With-Automorphism l)
  where

  is-cyclic-prop-Set-With-Automorphism : Prop l
  is-cyclic-prop-Set-With-Automorphism =
    product-Prop
      ( trunc-Prop (type-Set-With-Automorphism X))
      ( Π-Prop
        ( type-Set-With-Automorphism X)
        ( λ x →
          is-surjective-Prop
            ( λ k →
              map-iterate-automorphism-ℤ k (aut-Set-With-Automorphism X) x)))

  is-cyclic-Set-With-Automorphism : UU l
  is-cyclic-Set-With-Automorphism =
    type-Prop is-cyclic-prop-Set-With-Automorphism
```

### Cyclic sets

```agda
Cyclic-Set :
  (l : Level) → UU (lsuc l)
Cyclic-Set l =
  Σ (Set-With-Automorphism l) (λ X → is-cyclic-Set-With-Automorphism X)

module _
  {l : Level} (X : Cyclic-Set l)
  where

  set-with-automorphism-Cyclic-Set : Set-With-Automorphism l
  set-with-automorphism-Cyclic-Set = pr1 X

  set-Cyclic-Set : Set l
  set-Cyclic-Set = set-Set-With-Automorphism set-with-automorphism-Cyclic-Set

  type-Cyclic-Set : UU l
  type-Cyclic-Set = type-Set-With-Automorphism set-with-automorphism-Cyclic-Set

  is-set-type-Cyclic-Set : is-set type-Cyclic-Set
  is-set-type-Cyclic-Set =
    is-set-type-Set-With-Automorphism set-with-automorphism-Cyclic-Set

  aut-Cyclic-Set : Aut type-Cyclic-Set
  aut-Cyclic-Set = aut-Set-With-Automorphism set-with-automorphism-Cyclic-Set

  map-Cyclic-Set : type-Cyclic-Set → type-Cyclic-Set
  map-Cyclic-Set = map-Set-With-Automorphism set-with-automorphism-Cyclic-Set
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
