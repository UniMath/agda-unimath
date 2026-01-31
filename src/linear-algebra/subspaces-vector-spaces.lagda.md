# Subspaces of vector spaces

```agda
module linear-algebra.subspaces-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-submodules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

A
{{#concept "subspace" Disambiguation="of a vector space" WDID=Q728435 WD="linear subspace" Agda=subspace-Vector-Space}}
of a [vector space](linear-algebra.vector-spaces.md) `V` over a
[Heyting field](commutative-algebra.heyting-fields.md) `F` is a
[submodule](linear-algebra.left-submodules-rings.md) of `V` as a
[left module](linear-algebra.left-modules-rings.md) over the underlying
[ring](ring-theory.rings.md) of `F`.

## Definition

```agda
subspace-Vector-Space :
  (l1 : Level) {l2 l3 : Level} (F : Heyting-Field l2) → Vector-Space l3 F →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
subspace-Vector-Space l F = left-submodule-Ring l (ring-Heyting-Field F)

module _
  {l1 l2 l3 : Level}
  (F : Heyting-Field l1)
  (V : Vector-Space l2 F)
  (S : subspace-Vector-Space l3 F V)
  where

  subset-subspace-Vector-Space : subtype l3 (type-Vector-Space F V)
  subset-subspace-Vector-Space =
    subset-left-submodule-Ring (ring-Heyting-Field F) V S

  type-subspace-Vector-Space : UU (l2 ⊔ l3)
  type-subspace-Vector-Space = type-subtype subset-subspace-Vector-Space

  vector-space-subspace-Vector-Space : Vector-Space (l2 ⊔ l3) F
  vector-space-subspace-Vector-Space =
    left-module-left-submodule-Ring (ring-Heyting-Field F) V S
```
