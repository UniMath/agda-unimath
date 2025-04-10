# Dedekind finite sets

```agda
module univalent-combinatorics.dedekind-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Dedekind finite sets" Agda=set-Dedekind-Finite-Set}} are
[sets](foundation-core.sets.md) `X` with the
[property](foundation-core.propositions.md) that every
[embedding](foundation-core.embeddings.md) `X ↪ X` is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### Dedekind finite sets

```agda
is-dedekind-finite-set-Prop : {l : Level} → Set l → Prop l
is-dedekind-finite-set-Prop X =
  Π-Prop
    ( type-Set X → type-Set X)
    ( λ f → function-Prop (is-emb f) (is-equiv-Prop f))

is-dedekind-finite-set : {l : Level} → Set l → UU l
is-dedekind-finite-set X = type-Prop (is-dedekind-finite-set-Prop X)

Dedekind-Finite-Set : (l : Level) → UU (lsuc l)
Dedekind-Finite-Set l = Σ (Set l) is-dedekind-finite-set

module _
  {l : Level} (X : Dedekind-Finite-Set l)
  where

  set-Dedekind-Finite-Set : Set l
  set-Dedekind-Finite-Set = pr1 X

  type-Dedekind-Finite-Set : UU l
  type-Dedekind-Finite-Set = type-Set set-Dedekind-Finite-Set

  is-set-type-Dedekind-Finite-Set : is-set type-Dedekind-Finite-Set
  is-set-type-Dedekind-Finite-Set = is-set-type-Set set-Dedekind-Finite-Set

  is-dedekind-finite-set-Dedekind-Finite-Set :
    is-dedekind-finite-set set-Dedekind-Finite-Set
  is-dedekind-finite-set-Dedekind-Finite-Set = pr2 X
```

### Dedekind finite types

```agda
is-dedekind-finite-Prop : {l : Level} → UU l → Prop l
is-dedekind-finite-Prop X =
  Π-Prop
    ( X → X)
    ( λ f → function-Prop (is-emb f) (is-equiv-Prop f))

is-dedekind-finite : {l : Level} → UU l → UU l
is-dedekind-finite X = type-Prop (is-dedekind-finite-Prop X)

Dedekind-Finite-Type : (l : Level) → UU (lsuc l)
Dedekind-Finite-Type l = Σ (UU l) is-dedekind-finite

module _
  {l : Level} (X : Dedekind-Finite-Type l)
  where

  type-Dedekind-Finite-Type : UU l
  type-Dedekind-Finite-Type = pr1 X

  is-dedekind-finite-Dedekind-Finite-Type :
    is-dedekind-finite type-Dedekind-Finite-Type
  is-dedekind-finite-Dedekind-Finite-Type = pr2 X
```

## Properties

### If two Dedekind finite types mutually embed, they are equivalent

This can be understood as a constructive
[Cantor–Schröder–Bernstein theorem](foundation.cantor-schroder-bernstein-escardo.md)
for Dedekind finite types.

**Proof.** Given embeddings `f : X ↪ Y` and `g : Y ↪ X`, we have a commuting
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

The top and bottom rows are equivalences by Dedekind finiteness, so by the
6-for-2 property of equivalences every edge in this diagram is an equivalence.

```agda
module _
  {l1 l2 : Level}
  (X : Dedekind-Finite-Type l1) (Y : Dedekind-Finite-Type l2)
  (f : type-Dedekind-Finite-Type X ↪ type-Dedekind-Finite-Type Y)
  (g : type-Dedekind-Finite-Type Y ↪ type-Dedekind-Finite-Type X)
  where

  is-equiv-map-cantor-schroder-bernstein-Dedekind-Finite-Type :
    is-equiv (map-emb f)
  is-equiv-map-cantor-schroder-bernstein-Dedekind-Finite-Type =
    is-equiv-left-is-equiv-top-is-equiv-bottom-square
      ( map-emb f)
      ( map-emb f)
      ( map-emb g)
      ( refl-htpy)
      ( refl-htpy)
      ( is-dedekind-finite-Dedekind-Finite-Type X
        ( map-emb g ∘ map-emb f)
        ( is-emb-map-comp-emb g f))
      ( is-dedekind-finite-Dedekind-Finite-Type Y
        ( map-emb f ∘ map-emb g)
        ( is-emb-map-comp-emb f g))

  cantor-schroder-bernstein-Dedekind-Finite-Type :
    type-Dedekind-Finite-Type X ≃ type-Dedekind-Finite-Type Y
  cantor-schroder-bernstein-Dedekind-Finite-Type =
    ( map-emb f , is-equiv-map-cantor-schroder-bernstein-Dedekind-Finite-Type)
```

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)

## References

{{#bibliography}} {{#reference Sto87}}

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Dedekind`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Dedekind.html)
  at TypeTopology
- [finite object#Dedekind finiteness](https://ncatlab.org/nlab/show/finite+object#dedekind_finiteness)
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
