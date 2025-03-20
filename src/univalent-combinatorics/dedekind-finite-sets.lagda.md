# Dedekind finite sets

```agda
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics.dedekind-finite-sets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.propositions funext
open import foundation.sets funext
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Dedekind finite sets" Agda=set-Dedekind-Finite-Set}} are
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
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
