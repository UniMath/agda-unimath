# Dedekind finite sets

```agda
module univalent-combinatorics.dedekind-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Dedekind finite sets" Agda=set-Finite-Type-Dedekind}} are
[sets](foundation-core.sets.md) `X` with the
[property](foundation-core.propositions.md) that every
[embedding](foundation-core.embeddings.md) `X ↪ X` is an
[equivalence](foundation-core.equivalences.md).

## Definition

```agda
is-dedekind-finite-set-Prop : {l : Level} → Set l → Prop l
is-dedekind-finite-set-Prop X =
  Π-Prop
    ( type-Set X → type-Set X)
    ( λ f → function-Prop (is-emb f) (is-equiv-Prop f))

is-dedekind-finite-set : {l : Level} → Set l → UU l
is-dedekind-finite-set X = type-Prop (is-dedekind-finite-set-Prop X)

𝔽-Dedekind : (l : Level) → UU (lsuc l)
𝔽-Dedekind l = Σ (Set l) is-dedekind-finite-set

module _
  {l : Level} (X : 𝔽-Dedekind l)
  where

  set-Finite-Type-Dedekind : Set l
  set-Finite-Type-Dedekind = pr1 X

  type-𝔽-Dedekind : UU l
  type-𝔽-Dedekind = type-Set set-Finite-Type-Dedekind

  is-set-type-𝔽-Dedekind : is-set type-𝔽-Dedekind
  is-set-type-𝔽-Dedekind = is-set-type-Set set-Finite-Type-Dedekind

  is-dedekind-finite-set-Finite-Type-Dedekind : is-dedekind-finite-set set-Finite-Type-Dedekind
  is-dedekind-finite-set-Finite-Type-Dedekind = pr2 X
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
