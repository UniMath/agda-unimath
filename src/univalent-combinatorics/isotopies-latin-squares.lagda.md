# Isotopies of Latin squares

```agda
module univalent-combinatorics.isotopies-latin-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import structured-types.morphisms-wild-quasigroups
open import structured-types.wild-quasigroups

open import univalent-combinatorics.latin-squares
```

</details>

## Idea

An isotopy of latin squares from `L` to `K` consists of equivalences of the
rows, columns, and symbols preserving the multiplication tables.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (L : Latin-Square l1 l2 l3) (K : Latin-Square l4 l5 l6)
  where

  isotopy-Latin-Square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  isotopy-Latin-Square =
    Σ ( row-Latin-Square L ≃ row-Latin-Square K)
      ( λ e-row →
        Σ ( column-Latin-Square L ≃ column-Latin-Square K)
          ( λ e-column →
            Σ ( symbol-Latin-Square L ≃ symbol-Latin-Square K)
              ( λ e-symbol →
                ( x : row-Latin-Square L) (y : column-Latin-Square L) →
                Id
                  ( map-equiv e-symbol (mul-Latin-Square L x y))
                  ( mul-Latin-Square K
                    ( map-equiv e-row x)
                    ( map-equiv e-column y)))))
```

## Properties

### [Isomorphisms](structured-types.morphisms-wild-quasigroups.md) of [wild quasigroups](structured-types.wild-quasigroups.md) induce isotopies of their Latin squares

```agda
module _
  {l1 l2 : Level} (A : Wild-Quasigroup l1) (B : Wild-Quasigroup l2)
  (inhb-A : is-inhabited (type-Wild-Quasigroup A))
  (inhb-B : is-inhabited (type-Wild-Quasigroup B))
  where
  hom-Wild-Quasigroup-isotopy-Latin-Square :
    ( f : hom-Wild-Quasigroup A B) → is-equiv (map-hom-Wild-Quasigroup A B f) →
    isotopy-Latin-Square
    ( Wild-Quasigroup-Latin-Square A inhb-A)
    ( Wild-Quasigroup-Latin-Square B inhb-B)
  pr1 (hom-Wild-Quasigroup-isotopy-Latin-Square f equiv-f) =
    map-hom-Wild-Quasigroup A B f , equiv-f
  pr1 (pr2 (hom-Wild-Quasigroup-isotopy-Latin-Square f equiv-f)) =
    map-hom-Wild-Quasigroup A B f , equiv-f
  pr1 (pr2 (pr2 (hom-Wild-Quasigroup-isotopy-Latin-Square f equiv-f))) =
    map-hom-Wild-Quasigroup A B f , equiv-f
  pr2 (pr2 (pr2 (hom-Wild-Quasigroup-isotopy-Latin-Square f equiv-f))) =
    preserves-mul-map-hom-Wild-Quasigroup A B f
```
