# Abelianization of abstract groups

```agda
module group-theory.abelianization-groups where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider a [group homomoprhism](group-theory.homomorphisms-groups.md)
`f : G → A` from a [group](group-theory.groups.md) `G` into an
[abelian group](group-theory.abelian-groups.md) `A`. We say that `f` **is an
abelianization** of `G` if the precomposition function

```text
  - ∘ f : hom A B → hom G B
```

is an [equivalence](foundation-core.equivalences.md) for any abelian group `B`.

The **abelianization** `Gᵃᵇ` of a group `G` always exists, and can be
constructed as the [quotient group](group-theory.quotient-groups.md) `G/[G,G]`
of `G` modulo its [commutator subgroup](group-theory.commutator-subgroups.md).
Therefore we obtain an
[adjunction](category-theory.adjunctions-large-categories.md)

```text
  hom Gᵃᵇ A ≃ hom G A,
```

i.e., the abelianization is left adjoint to the inclusion functor from abelian
groups into groups.

## External links

- [Abelianization](https://groupprops.subwiki.org/wiki/Abelianization) at
  Groupprops
- [Abelianization](https://ncatlab.org/nlab/show/abelianization) at nlab
- [Abelianization](https://en.wikipedia.org/wiki/Commutator_subgroup#Abelianization)
  at Wikipedia
- [Abelianization](https://mathworld.wolfram.com/Abelianization.html) at Wolfram
  Mathworld
- [Commutator subgroup](https://www.wikidata.org/entity/Q522216) at Wikidata

<content id="https://www.wikidata.org/entity/Q522216" />
