# Nontrivial groups

```agda
module group-theory.nontrivial-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.subgroups
open import group-theory.trivial-groups
```

</details>

## Idea

A [group](group-theory.groups.md) is said to be **nontrivial** if there
[exists](foundation.existential-quantification.md) a nonidentity element.

## Definitions

### The predicate of being a nontrivial group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-nontrivial-prop-Group : Prop l1
  is-nontrivial-prop-Group =
    exists-structure-Prop (type-Group G) (λ g → unit-Group G ≠ g)

  is-nontrivial-Group : UU l1
  is-nontrivial-Group =
    type-Prop is-nontrivial-prop-Group

  is-prop-is-nontrivial-Group :
    is-prop is-nontrivial-Group
  is-prop-is-nontrivial-Group =
    is-prop-type-Prop is-nontrivial-prop-Group
```

### The predicate of not being the trivial group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-not-trivial-prop-Group : Prop l1
  is-not-trivial-prop-Group =
    neg-type-Prop ((x : type-Group G) → unit-Group G ＝ x)

  is-not-trivial-Group : UU l1
  is-not-trivial-Group =
    type-Prop is-not-trivial-prop-Group

  is-prop-is-not-trivial-Group :
    is-prop is-not-trivial-Group
  is-prop-is-not-trivial-Group =
    is-prop-type-Prop is-not-trivial-prop-Group
```

## Properties

### A group is not a trivial group if and only if it satisfies the predicate of not being trivial

**Proof:** The proposition `¬ (is-trivial-Group G)` holds if and only if `G` is
not contractible, which holds if and only if `¬ ((x : G) → 1 ＝ x)`.

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  neg-is-trivial-is-not-trivial-Group :
    is-not-trivial-Group G → ¬ (is-trivial-Group G)
  neg-is-trivial-is-not-trivial-Group H p = H (λ x → eq-is-contr p)

  is-not-trivial-neg-is-trivial-Group :
    ¬ (is-trivial-Group G) → is-not-trivial-Group G
  is-not-trivial-neg-is-trivial-Group H p = H (unit-Group G , p)
```

### The map `subgroup-Prop G : Prop → Subgroup G` is an embedding for any nontrivial group

Recall that the subgroup `subgroup-Prop G P` associated to a proposition `P` was
defined in [`group-theory.subgroups`](group-theory.subgroups.md).

**Proof:** Suppose that `G` is a nontrivial group and `x` is a group element
such that `1 ≠ x`. Then `subgroup-Prop G P ＝ subgroup-Prop G Q` if and only if
`x ∈ subgroup-Prop G P ⇔ x ∈ subgroup-Prop G Q`, which holds if and only if
`P ⇔ Q` since `x` is assumed to be a nonidentity element. This shows that
`subgroup-Prop G : Prop → Subgroup G` is an injective map. Since it is an
injective maps between sets, it follows that `subgroup-Prop G` is an embedding.

```agda
module _
  {l1 l2 : Level} (G : Group l1)
  where

  abstract
    is-emb-subgroup-prop-is-nontrivial-Group :
      is-nontrivial-Group G → is-emb (subgroup-Prop {l2 = l2} G)
    is-emb-subgroup-prop-is-nontrivial-Group H =
      apply-universal-property-trunc-Prop H
        ( is-emb-Prop _)
        ( λ (x , f) →
          is-emb-is-injective
            ( is-set-Subgroup G)
            ( λ {P} {Q} α →
              eq-iff
                ( λ p →
                  map-left-unit-law-disjunction-is-empty-Prop
                    ( Id-Prop (set-Group G) _ _)
                    ( Q)
                    ( f)
                    ( forward-implication
                      ( iff-eq (ap (λ T → subset-Subgroup G T x) α))
                      ( inr-disjunction p)))
                ( λ q →
                  map-left-unit-law-disjunction-is-empty-Prop
                    ( Id-Prop (set-Group G) _ _)
                    ( P)
                    ( f)
                    ( backward-implication
                      ( iff-eq (ap (λ T → subset-Subgroup G T x) α))
                      ( inr-disjunction q)))))
```

### If the map `subgroup-Prop G : Prop lzero → Subgroup l1 G` is an embedding, then `G` is not a trivial group

**Proof:** Suppose that `subgroup-Prop G : Prop lzero → Subgroup l1 G` is an
embedding, and by way of contradiction suppose that `G` is trivial. Then it
follows that `Subgroup l1 G` is contractible. Since `subgroup-Prop G` is assumed
to be an embedding, it follows that `Prop lzero` is contractible. This
contradicts the fact that `Prop lzero` contains the distinct propositions
`empty-Prop` and `unit-Prop`.

Note: Our handling of universe levels might be too restrictive here.

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-not-trivial-is-emb-subgroup-Prop :
    is-emb (subgroup-Prop {l2 = lzero} G) → is-not-trivial-Group G
  is-not-trivial-is-emb-subgroup-Prop H K =
    backward-implication
      ( iff-eq
        ( is-injective-is-emb H
          { x = empty-Prop}
          { y = unit-Prop}
          ( eq-is-contr (is-contr-subgroup-is-trivial-Group G (_ , K)))))
      ( star)
```
