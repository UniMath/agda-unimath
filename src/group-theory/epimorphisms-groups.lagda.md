# Epimorphisms in groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.epimorphisms-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.epimorphisms-in-large-precategories funext univalence truncations

open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import group-theory.groups funext univalence truncations
open import group-theory.homomorphisms-groups funext univalence truncations
open import group-theory.isomorphisms-groups funext univalence truncations
open import group-theory.precategory-of-groups funext univalence truncations
```

</details>

## Idea

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` is an
**epimorphism** if the precomposition function

```text
  - ∘ f : hom-set-Group H K → hom-set-Group G K
```

is an [embedding](foundation.embeddings.md) for any
[group](group-theory.groups.md) `K`. In other words, `f` is an epimorphism if
for any two group homomorphisms `g h : H → K` we have that `g ∘ f = h ∘ f`
implies `g = h`.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : hom-Group G H)
  where

  is-epi-prop-hom-Group : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-epi-prop-hom-Group =
    is-epi-prop-Large-Precategory Group-Large-Precategory l3 G H f

  is-epi-hom-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-epi-hom-Group = type-Prop is-epi-prop-hom-Group

  is-prop-is-epi-hom-Group : is-prop is-epi-hom-Group
  is-prop-is-epi-hom-Group = is-prop-type-Prop is-epi-prop-hom-Group
```

## Properties

### Isomorphisms are epimorphisms

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : iso-Group G H)
  where

  is-epi-iso-Group : is-epi-hom-Group l3 G H (hom-iso-Group G H f)
  is-epi-iso-Group =
    is-epi-iso-Large-Precategory Group-Large-Precategory l3 G H f
```

### A group homomorphism is surjective if and only if it is an epimorphism

**Proof using the law of excluded middle:** The forward direction of this claim
is the easier of the two directions, and this part of the proof doesn't require
the [law of excluded middle](foundation.law-of-excluded-middle.md). If `f` is
[surjective](foundation.surjective-maps.md) and `g h : H → K` are two group
homomorphisms such that `g ∘ f ＝ h ∘ f`, then to show that `g ＝ h` it suffices
to show that `g y ＝ h y` for any `y : H`. Since we are proving a
[proposition](foundation.propositions.md) and `f` is assumed to be surjective,
we may assume `x : G` equipped with an
[identification](foundation.identity-types.md) `f x ＝ y`. It therefore suffices
to show that `g (f x) ＝ h (f x)`, which was assumed.

For the converse, suppose that `f : G → H` is an epimorphism and consider the
[image subgroup](group-theory.images-of-group-homomorphisms.md) `I := im f` of
`H`. We first show that `I` is [normal](group-theory.normal-subgroups.md), and
then we show that `I ＝ H`.

In order to show that `I` is normal, we want to show that `I` has only one
conjugacy class, namely itself. Consider the group `K` of permutations of the
set of [conjugate](group-theory.conjugation.md)
[subgroups](group-theory.subgroups.md) of the subgroup `I` of `H`. There is a
group homomorphism `α : H → K` given by `h ↦ J ↦ hJh⁻¹`, where `J` ranges over
the conjugacy classes of `I`. Notice that `I` itself is a fixed point of the
conjugation operation `J ↦ f(x)Jf(x)⁻¹`, i.e., `I` is a fixed point of
`α(f(x))`. We claim that there is another homomorphism `β : H → K` given by
`h ↦ α(h) ∘ (I h⁻¹Ih)`, where we precompose with the
[transposition](finite-group-theory.transpositions.md) `(I h⁻¹Ih)`. This
transposition is defined using the law of excluded middle. However, note that
`I` is always a fixed point of `β(h)`, for any `h : H`. Furthermore, we have
`α(f(x)) ＝ β(f(x))`. Therefore it follows from the assumption that `f` is an
epimorphism that `α ＝ β`. In other words, `I` is a fixed point of any
conjugation operation `J ↦ hJh⁻¹`. We conclude that `I` is normal.

Since `I` is normal, we may consider the
[quotient group](group-theory.quotient-groups.md) `H/I`. Now we observe that the
quotient map maps `f(x)` to the unit of `H/I`. Using the assumption that `f` is
an epimorphism once more, we conclude that the quotient map `H → H/I` is the
[trivial homomorphism](group-theory.trivial-group-homomorphisms.md). Therefore
it follows that `I ＝ H`. This completes the proof.
