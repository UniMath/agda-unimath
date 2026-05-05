# Isotopies of Latin squares

```agda
module univalent-combinatorics.isotopies-latin-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

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
                ( map-equiv e-symbol (mul-Latin-Square L x y)) ＝
                ( mul-Latin-Square K
                  ( map-equiv e-row x)
                  ( map-equiv e-column y)))))
```
