# Discrete globular types

```agda
{-# OPTIONS --guardedness #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module globular-types.discrete-globular-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.discrete-binary-relations funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import globular-types.empty-globular-types funext univalence truncations
open import globular-types.globular-types
```

</details>

## Idea

A [globular type](globular-types.globular-types.md) `G` is said to be
{{#concept "discrete" Disambiguation="globular type" Agda=is-discrete-Globular-Type}}
if it has no 1-cells, i.e., if the type `G₁ x y` of 1-cells from `x` to `y` in
`G` is [empty](foundation.empty-types.md) for any two 0-cells `x y : G₀`. In
other words, a globular type is discrete if its
[binary relation](foundation.binary-relations.md) is
[discrete](foundation.discrete-binary-relations.md).

The forgetful functor from globular types to types given by `G ↦ G₀` has a left
adjoint, mapping a type `A` to the globular type with the type `A` as its
0-cells and no edges. The image of this left adjoint is precisely the type of
discrete globular types.

Note that the globular type obtained from a type and its iterated
[identity types](foundation-core.identity-types.md) is the
[standard discrete reflexive globular type](globular-types.discrete-reflexive-globular-types.md).

## Definitions

### The predicate on globular types of being discrete

```agda
module _
  {l1 l2 : Level} (G : Globular-Type l1 l2)
  where

  is-discrete-prop-Globular-Type : Prop (l1 ⊔ l2)
  is-discrete-prop-Globular-Type =
    is-discrete-prop-Relation (1-cell-Globular-Type G)

  is-discrete-Globular-Type : UU (l1 ⊔ l2)
  is-discrete-Globular-Type = is-discrete-Relation (1-cell-Globular-Type G)

  is-prop-is-discrete-Globular-Type : is-prop is-discrete-Globular-Type
  is-prop-is-discrete-Globular-Type =
    is-prop-is-discrete-Relation (1-cell-Globular-Type G)
```

### Discrete globular types

```agda
Discrete-Globular-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Discrete-Globular-Type l1 l2 =
  Σ (Globular-Type l1 l2) is-discrete-Globular-Type
```

### The standard discrete globular types

```agda
discrete-Globular-Type :
  {l : Level} (A : UU l) → Globular-Type l lzero
0-cell-Globular-Type (discrete-Globular-Type A) =
  A
1-cell-globular-type-Globular-Type (discrete-Globular-Type A) x y =
  empty-Globular-Type
```

## See also

- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete reflexive globular types](globular-types.discrete-reflexive-globular-types.md)
