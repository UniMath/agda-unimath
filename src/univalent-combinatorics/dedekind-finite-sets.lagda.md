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

open import univalent-combinatorics.dedekind-finite-types
```

</details>

## Idea

{{#concept "Dedekind finite sets" Agda=set-Dedekind-Finite-Set}} are
[sets](foundation-core.sets.md) `X` with the
[property](foundation-core.propositions.md) that every
self-[embedding](foundation-core.embeddings.md) `X ↪ X` is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being a Dedekind finite set

```agda
is-dedekind-finite-set-Prop : {l : Level} → Set l → Prop l
is-dedekind-finite-set-Prop X =
  is-dedekind-finite-Prop (type-Set X)

is-dedekind-finite-set : {l : Level} → Set l → UU l
is-dedekind-finite-set X = type-Prop (is-dedekind-finite-set-Prop X)
```

### The subuniverse of Dedekind finite sets

```agda
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
  at $n$Lab
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
