# Large abelian subgroups

```agda
module group-theory.large-abelian-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.homomorphisms-large-abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-commutative-monoids
open import group-theory.large-commutative-submonoids
open import group-theory.large-groups
open import group-theory.large-subgroups
open import group-theory.large-submonoids
open import group-theory.subgroups-abelian-groups
open import group-theory.subsets-large-abelian-groups
```

</details>

## Idea

A
{{#concept "subgroup" Disambiguation="of a large abelian group" Agda=Large-Subgroup-Ab}}
of a [large abelian group](group-theory.large-abelian-subgroups.md) `G` is a
[subset](group-theory.subsets-large-groups.md) `G` that contains zero and is
closed under addition and negation.

## Definition

```agda
record
  Large-Subgroup-Ab
    {α : Level → Level}
    {β : Level → Level → Level}
    (γ : Level → Level)
    (G : Large-Ab α β) :
    UUω
  where

  constructor
    make-Large-Subgroup-Ab

  field
    large-subgroup-Large-Subgroup-Ab :
      Large-Subgroup γ (large-group-Large-Ab G)

  large-submonoid-Large-Subgroup-Ab :
    Large-Submonoid γ (large-monoid-Large-Ab G)
  large-submonoid-Large-Subgroup-Ab =
    large-submonoid-Large-Subgroup large-subgroup-Large-Subgroup-Ab

  large-commutative-submonoid-Large-Subgroup-Ab :
    Large-Commutative-Submonoid γ (large-commutative-monoid-Large-Ab G)
  large-commutative-submonoid-Large-Subgroup-Ab =
    make-Large-Commutative-Submonoid large-submonoid-Large-Subgroup-Ab

  type-Large-Subgroup-Ab : (l : Level) → UU (α l ⊔ γ l)
  type-Large-Subgroup-Ab =
    type-Large-Subgroup large-subgroup-Large-Subgroup-Ab

  inclusion-Large-Subgroup-Ab :
    {l : Level} → type-Large-Subgroup-Ab l → type-Large-Ab G l
  inclusion-Large-Subgroup-Ab = pr1

open Large-Subgroup-Ab public
```

## Properties

### Large subgroups of abelian groups induce a large abelian group

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Ab α β}
  (S : Large-Subgroup-Ab γ G)
  where

  large-ab-Large-Subgroup-Ab : Large-Ab (λ l → α l ⊔ γ l) β
  large-ab-Large-Subgroup-Ab =
    make-Large-Ab
      ( large-group-Large-Subgroup (large-subgroup-Large-Subgroup-Ab S))
      ( commutative-mul-Large-Commutative-Submonoid
        ( large-commutative-submonoid-Large-Subgroup-Ab S))
```

### Small subgroups from large subgroups of abelian groups

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Ab α β}
  (S : Large-Subgroup-Ab γ G)
  where

  subgroup-ab-Large-Subgroup-Ab :
    (l : Level) → Subgroup-Ab (γ l) (ab-Large-Ab G l)
  subgroup-ab-Large-Subgroup-Ab =
    subgroup-Large-Subgroup (large-subgroup-Large-Subgroup-Ab S)
```

### The inclusion homomorphism of large abelian subgroups

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Ab α β}
  (S : Large-Subgroup-Ab γ G)
  where

  inclusion-hom-Large-Subgroup-Ab :
    hom-Large-Ab (large-ab-Large-Subgroup-Ab S) G
  inclusion-hom-Large-Subgroup-Ab =
    make-hom-Large-Ab
      ( inclusion-hom-Large-Subgroup (large-subgroup-Large-Subgroup-Ab S))
```
