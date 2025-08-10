# Subfinitely indexed types

```agda
module univalent-combinatorics.subfinitely-indexed-types where
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
{{#concept "subfinitely indexed" Agda=is-subfinitely-indexed Agda=Subfinitely-Indexed-Type}},
or **Kuratowski subfinite**, if there
[exists](foundation.existential-quantification.md) a
[surjection](foundation.surjective-maps.md) onto `X` from a
[subfinite type](univalent-combinatorics.subfinite-types.md).

## Definitions

### The predicate of being subfinitely indexed

```agda
is-subfinitely-indexed-Prop :
  {l1 : Level} (l2 : Level) → UU l1 → Prop (l1 ⊔ lsuc l2)
is-subfinitely-indexed-Prop l2 X =
  exists-structure-Prop (Subfinite-Type l2) (λ N → type-Subfinite-Type N ↠ X)

is-subfinitely-indexed :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
is-subfinitely-indexed l2 X = type-Prop (is-subfinitely-indexed-Prop l2 X)

is-prop-is-subfinitely-indexed :
  {l1 l2 : Level} {X : UU l1} → is-prop (is-subfinitely-indexed l2 X)
is-prop-is-subfinitely-indexed {l2 = l2} {X} =
  is-prop-type-Prop (is-subfinitely-indexed-Prop l2 X)
```

### The subuniverse of subfinitely indexed types

```agda
Subfinitely-Indexed-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Subfinitely-Indexed-Type l1 l2 = Σ (UU l1) (is-subfinitely-indexed l2)

module _
  {l1 l2 : Level} (X : Subfinitely-Indexed-Type l1 l2)
  where

  type-Subfinitely-Indexed-Type : UU l1
  type-Subfinitely-Indexed-Type = pr1 X

  is-subfinitely-indexed-Subfinitely-Indexed-Type :
    is-subfinitely-indexed l2 type-Subfinitely-Indexed-Type
  is-subfinitely-indexed-Subfinitely-Indexed-Type = pr2 X
```

## Properties

### Types with subfinite indexings are subfinitely indexed

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  abstract
    is-subfinitely-indexed-has-subfinite-indexing :
      subfinite-indexing l2 X → is-subfinitely-indexed l2 X
    is-subfinitely-indexed-has-subfinite-indexing (D , e , h) =
      unit-trunc-Prop ((D , unit-trunc-Prop e) , h)

  abstract
    is-inhabited-subfinite-indexing-is-subfinitely-indexed :
      is-subfinitely-indexed l2 X → ║ subfinite-indexing l2 X ║₋₁
    is-inhabited-subfinite-indexing-is-subfinitely-indexed =
      rec-trunc-Prop
        ( trunc-Prop (subfinite-indexing l2 X))
        ( λ ((D , |e|) , h) → map-trunc-Prop (λ e → (D , e , h)) |e|)
```

### Subfinitely indexed types are Dedekind finite

```agda
module _
  {l1 l2 : Level} (X : Subfinitely-Indexed-Type l1 l2)
  where

  is-dedekind-finite-type-Subfinitely-Indexed-Type :
    is-dedekind-finite (type-Subfinitely-Indexed-Type X)
  is-dedekind-finite-type-Subfinitely-Indexed-Type f is-emb-f =
    rec-trunc-Prop
      ( is-equiv-Prop f)
      ( λ c → is-dedekind-finite-subfinite-indexing c f is-emb-f)
      ( is-inhabited-subfinite-indexing-is-subfinitely-indexed
        ( is-subfinitely-indexed-Subfinitely-Indexed-Type X))

  dedekind-finite-type-Subfinitely-Indexed-Type : Dedekind-Finite-Type l1
  dedekind-finite-type-Subfinitely-Indexed-Type =
    ( type-Subfinitely-Indexed-Type X ,
      is-dedekind-finite-type-Subfinitely-Indexed-Type)
```

### The Cantor–Schröder–Bernstein theorem for subfinitely indexed types

If two subfinitely indexed types `X` and `Y` mutually embed, `X ↪ Y` and
`Y ↪ X`, then `X ≃ Y`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Subfinitely-Indexed-Type l1 l2)
  (Y : Subfinitely-Indexed-Type l3 l4)
  where

  Cantor-Schröder-Bernstein-Subfinitely-Indexed-Type :
    (type-Subfinitely-Indexed-Type X ↪ type-Subfinitely-Indexed-Type Y) →
    (type-Subfinitely-Indexed-Type Y ↪ type-Subfinitely-Indexed-Type X) →
    type-Subfinitely-Indexed-Type X ≃ type-Subfinitely-Indexed-Type Y
  Cantor-Schröder-Bernstein-Subfinitely-Indexed-Type =
    Cantor-Schröder-Bernstein-Dedekind-Finite-Type
      ( dedekind-finite-type-Subfinitely-Indexed-Type X)
      ( dedekind-finite-type-Subfinitely-Indexed-Type Y)
```

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Kuratowski`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Kuratowski.html)
  at TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
