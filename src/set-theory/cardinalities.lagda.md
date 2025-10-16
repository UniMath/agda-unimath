# Cardinalities of sets

```agda
module set-theory.cardinalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.set-truncations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "cardinality" Disambiguation="of a set" Agda=cardinality WD="cardinality" WDID=Q4049983}}
of a [set](foundation-core.sets.md) is its
[isomorphism](category-theory.isomorphisms-in-categories.md) class. We take
isomorphism classes of sets by [set truncating](foundation.set-truncations.md)
the universe of sets of any given
[universe level](foundation.universe-levels.md). Note that this definition takes
advantage of the [univalence axiom](foundation.univalence.md): By the univalence
axiom [isomorphic sets](foundation.isomorphisms-of-sets.md) are
[equal](foundation-core.identity-types.md), and will be mapped to the same
element in the set truncation of the universe of all sets.

## Definition

### Cardinals

```agda
Cardinal-Set : (l : Level) → Set (lsuc l)
Cardinal-Set l = trunc-Set (Set l)

Cardinal : (l : Level) → UU (lsuc l)
Cardinal l = type-Set (Cardinal-Set l)

is-set-Cardinal : {l : Level} → is-set (Cardinal l)
is-set-Cardinal {l} = is-set-type-Set (Cardinal-Set l)
```

### The cardinality of a set

```agda
cardinality : {l : Level} → Set l → Cardinal l
cardinality A = unit-trunc-Set A
```

## External links

- [Cardinality](https://en.wikipedia.org/wiki/Cardinality) at Wikipedia
- [cardinal number](https://ncatlab.org/nlab/show/cardinal+number) at $n$Lab
