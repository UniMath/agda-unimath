# Homomorphisms of large abelian groups

```agda
module group-theory.homomorphisms-large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-large-groups
open import group-theory.large-abelian-groups
open import group-theory.large-groups
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of large abelian groups" Agda=hom-Large-Ab}}
from a [large abelian group](group-theory.large-abelian-groups.md) `G` to a
large abelian group `H` is a
[similarity-preserving map](foundation.similarity-preserving-maps-cumulative-large-sets.md)
from `G` to `H` that preserves addition.

## Definition

We create a single-field record to ensure that the source and target large
groups can be determined implicitly from the homomorphism.

```agda
record
  hom-Large-Ab
    {α β : Level → Level}
    {γ δ : Level → Level → Level}
    (G : Large-Ab α γ)
    (H : Large-Ab β δ) :
    UUω
  where

  constructor
    make-hom-Large-Ab

  field
    hom-large-group-hom-Large-Ab :
      hom-Large-Group
        ( large-group-Large-Ab G)
        ( large-group-Large-Ab H)

open hom-Large-Ab public
```

## Properties

### Small abelian group homomorphisms from large abelian group homomorphisms

```agda
module _
  {α β : Level → Level}
  {γ δ : Level → Level → Level}
  {G : Large-Ab α γ}
  {H : Large-Ab β δ}
  (f : hom-Large-Ab G H)
  where

  hom-ab-hom-Large-Ab : (l : Level) → hom-Ab (ab-Large-Ab G l) (ab-Large-Ab H l)
  hom-ab-hom-Large-Ab =
    hom-group-hom-Large-Group (hom-large-group-hom-Large-Ab f)
```
