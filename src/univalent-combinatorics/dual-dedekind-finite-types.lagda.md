# Dual Dedekind finite types

```agda
module univalent-combinatorics.dual-dedekind-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-maps
```

</details>

## Idea

{{#concept "Dual Dedekind finite types" Agda=is-dual-dedekind-finite Agda=Dual-Dedekind-Finite-Type}}
are types `X` with the [property](foundation-core.propositions.md) that every
[acyclic](synthetic-homotopy-theory.acyclic-maps.md) endomap `X ↠ X` is an
[equivalence](foundation-core.equivalences.md).

Recall that a
[Dedekind finite type](univalent-combinatorics.dedekind-finite-types.md) is a
type such that every self-[embedding](foundation-core.embeddings.md) is an
equivalence. The dual Dedekind finiteness condition is formally dual to the
Dedekind finiteness condition, since acyclic maps are precisely the
[epimorphisms](foundation.epimorphisms.md) in the
[∞-category of types](foundation.wild-category-of-types.md), while embeddings
are precisely the [monomorphisms](foundation.monomorphisms.md).

## Definitions

### The predicate of being a dual Dedekind finite type

```agda
is-dual-dedekind-finite-Prop : {l : Level} → UU l → Prop l
is-dual-dedekind-finite-Prop X =
  Π-Prop
    ( X → X)
    ( λ f → function-Prop (is-acyclic-map f) (is-equiv-Prop f))

is-dual-dedekind-finite : {l : Level} → UU l → UU l
is-dual-dedekind-finite X = type-Prop (is-dual-dedekind-finite-Prop X)

is-prop-is-dual-dedekind-finite :
  {l : Level} {X : UU l} → is-prop (is-dual-dedekind-finite X)
is-prop-is-dual-dedekind-finite {X = X} =
  is-prop-type-Prop (is-dual-dedekind-finite-Prop X)
```

### The subuniverse of dual Dedekind finite types

```agda
Dual-Dedekind-Finite-Type : (l : Level) → UU (lsuc l)
Dual-Dedekind-Finite-Type l = Σ (UU l) is-dual-dedekind-finite

module _
  {l : Level} (X : Dual-Dedekind-Finite-Type l)
  where

  type-Dual-Dedekind-Finite-Type : UU l
  type-Dual-Dedekind-Finite-Type = pr1 X

  is-dual-dedekind-finite-Dual-Dedekind-Finite-Type :
    is-dual-dedekind-finite type-Dual-Dedekind-Finite-Type
  is-dual-dedekind-finite-Dual-Dedekind-Finite-Type = pr2 X
```

## Properties

### If two dual Dedekind finite types mutually project, they are equivalent

This can be understood as a constructive dual
[Cantor–Schröder–Bernstein theorem](foundation.cantor-schroder-bernstein-escardo.md)
for dual Dedekind finite types.

**Proof.** Given epimorphisms `f : X ↠ Y` and `g : Y ↠ X`, we have a commuting
diagram

```text
       g ∘ f
    X ------> X
    |       ∧ |
  f |   g /   | f
    |   /     |
    ∨ /       ∨
    Y ------> Y.
       f ∘ g
```

The top and bottom rows are equivalences by dual Dedekind finiteness, so by the
6-for-2 property of equivalences every edge in this diagram is an equivalence. ∎

```agda
module _
  {l1 l2 : Level}
  (X : Dual-Dedekind-Finite-Type l1)
  (Y : Dual-Dedekind-Finite-Type l2)
  (f :
    acyclic-map
      ( type-Dual-Dedekind-Finite-Type X)
      ( type-Dual-Dedekind-Finite-Type Y))
  (g :
    acyclic-map
      ( type-Dual-Dedekind-Finite-Type Y)
      ( type-Dual-Dedekind-Finite-Type X))
  where

  is-equiv-map-cantor-schröder-bernstein-Dual-Dedekind-Finite-Type :
    is-equiv (map-acyclic-map f)
  is-equiv-map-cantor-schröder-bernstein-Dual-Dedekind-Finite-Type =
    is-equiv-left-is-equiv-top-is-equiv-bottom-square
      ( map-acyclic-map f)
      ( map-acyclic-map f)
      ( map-acyclic-map g)
      ( refl-htpy)
      ( refl-htpy)
      ( is-dual-dedekind-finite-Dual-Dedekind-Finite-Type X
        ( map-acyclic-map g ∘ map-acyclic-map f)
        ( is-acyclic-map-comp-acyclic-map g f))
      ( is-dual-dedekind-finite-Dual-Dedekind-Finite-Type Y
        ( map-acyclic-map f ∘ map-acyclic-map g)
        ( is-acyclic-map-comp-acyclic-map f g))

  cantor-schröder-bernstein-Dual-Dedekind-Finite-Type :
    type-Dual-Dedekind-Finite-Type X ≃ type-Dual-Dedekind-Finite-Type Y
  cantor-schröder-bernstein-Dual-Dedekind-Finite-Type =
    ( map-acyclic-map f ,
      is-equiv-map-cantor-schröder-bernstein-Dual-Dedekind-Finite-Type)
```

## See also

- [Dedekind finite types](univalent-combinatorics.dedekind-finite-types.md)

## External links

- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
