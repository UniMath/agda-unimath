# Subfinitely enumerable types

```agda
module univalent-combinatorics.subfinitely-enumerable-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.dedekind-finite-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.subfinite-indexing
open import univalent-combinatorics.subfinite-types
```

</details>

## Idea

A type `X` is
{{#concept "subfinitely enumerable" Agda=is-subfinitely-enumerable Agda=Subfinitely-Enumerable-Type}},
or **Kuratowski subfinite**, if there
[exists](foundation.existential-quantification.md) a
[surjection](foundation.surjective-maps.md) onto `X` from a
[subfinite type](univalent-combinatorics.subfinite-types.md).

## Definitions

### The predicate of being subfinitely enumerable

```agda
is-subfinitely-enumerable-Prop :
  {l1 : Level} (l2 : Level) → UU l1 → Prop (l1 ⊔ lsuc l2)
is-subfinitely-enumerable-Prop l2 X =
  exists-structure-Prop (Subfinite-Type l2) (λ N → type-Subfinite-Type N ↠ X)

is-subfinitely-enumerable :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
is-subfinitely-enumerable l2 X = type-Prop (is-subfinitely-enumerable-Prop l2 X)

is-prop-is-subfinitely-enumerable :
  {l1 l2 : Level} {X : UU l1} → is-prop (is-subfinitely-enumerable l2 X)
is-prop-is-subfinitely-enumerable {l2 = l2} {X} =
  is-prop-type-Prop (is-subfinitely-enumerable-Prop l2 X)
```

### The subuniverse of subfinitely enumerable types

```agda
Subfinitely-Enumerable-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Subfinitely-Enumerable-Type l1 l2 = Σ (UU l1) (is-subfinitely-enumerable l2)

module _
  {l1 l2 : Level} (X : Subfinitely-Enumerable-Type l1 l2)
  where

  type-Subfinitely-Enumerable-Type : UU l1
  type-Subfinitely-Enumerable-Type = pr1 X

  is-subfinitely-enumerable-Subfinitely-Enumerable-Type :
    is-subfinitely-enumerable l2 type-Subfinitely-Enumerable-Type
  is-subfinitely-enumerable-Subfinitely-Enumerable-Type = pr2 X
```

## Properties

### Types with subfinite indexings are subfinitely enumerable

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  abstract
    is-subfinitely-enumerable-has-subfinite-indexing :
      subfinite-indexing l2 X → is-subfinitely-enumerable l2 X
    is-subfinitely-enumerable-has-subfinite-indexing (D , e , h) =
      unit-trunc-Prop ((D , unit-trunc-Prop e) , h)

  abstract
    is-inhabited-subfinite-indexing-is-subfinitely-enumerable :
      is-subfinitely-enumerable l2 X → ║ subfinite-indexing l2 X ║₋₁
    is-inhabited-subfinite-indexing-is-subfinitely-enumerable =
      rec-trunc-Prop
        ( trunc-Prop (subfinite-indexing l2 X))
        ( λ ((D , |e|) , h) → map-trunc-Prop (λ e → (D , e , h)) |e|)
```

### Subfinitely enumerable types are Dedekind finite

```agda
module _
  {l1 l2 : Level} (X : Subfinitely-Enumerable-Type l1 l2)
  where

  is-dedekind-finite-type-Subfinitely-Enumerable-Type :
    is-dedekind-finite (type-Subfinitely-Enumerable-Type X)
  is-dedekind-finite-type-Subfinitely-Enumerable-Type f is-emb-f =
    rec-trunc-Prop
      ( is-equiv-Prop f)
      ( λ c → is-dedekind-finite-subfinite-indexing c f is-emb-f)
      ( is-inhabited-subfinite-indexing-is-subfinitely-enumerable
        ( is-subfinitely-enumerable-Subfinitely-Enumerable-Type X))

  dedekind-finite-type-Subfinitely-Enumerable-Type : Dedekind-Finite-Type l1
  dedekind-finite-type-Subfinitely-Enumerable-Type =
    ( type-Subfinitely-Enumerable-Type X ,
      is-dedekind-finite-type-Subfinitely-Enumerable-Type)

is-dedekind-finite-is-subfinitely-enumerable :
  {l1 l2 : Level} {X : UU l1} →
  is-subfinitely-enumerable l2 X → is-dedekind-finite X
is-dedekind-finite-is-subfinitely-enumerable H =
  is-dedekind-finite-type-Subfinitely-Enumerable-Type (_ , H)
```

### The Cantor–Schröder–Bernstein theorem for subfinitely enumerable types

If two subfinitely enumerable types `X` and `Y` mutually embed, `X ↪ Y` and
`Y ↪ X`, then `X ≃ Y`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Subfinitely-Enumerable-Type l1 l2)
  (Y : Subfinitely-Enumerable-Type l3 l4)
  where

  Cantor-Schröder-Bernstein-Subfinitely-Enumerable-Type :
    (type-Subfinitely-Enumerable-Type X ↪ type-Subfinitely-Enumerable-Type Y) →
    (type-Subfinitely-Enumerable-Type Y ↪ type-Subfinitely-Enumerable-Type X) →
    type-Subfinitely-Enumerable-Type X ≃ type-Subfinitely-Enumerable-Type Y
  Cantor-Schröder-Bernstein-Subfinitely-Enumerable-Type =
    Cantor-Schröder-Bernstein-Dedekind-Finite-Type
      ( dedekind-finite-type-Subfinitely-Enumerable-Type X)
      ( dedekind-finite-type-Subfinitely-Enumerable-Type Y)
```

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
