# Latin squares

```agda
module univalent-combinatorics.latin-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import structured-types.wild-quasigroups
```

</details>

## Idea

{{#concept "Latin squares" WDID=Q679367 WD="Latin square" Agda=Latin-Square}}
are multiplication tables in which every element appears in every row and in
every column exactly once. Latin squares are considered to be the same if they
are [isotopic](univalent-combinatorics.isotopies-latin-squares.md). We therefore
define the type of all Latin squares to be the type of all
[inhabited](foundation.inhabited-types.md) types `A`, `B`, and `C`, equipped
with a [binary equivalence](foundation.binary-equivalences.md) `f : A → B → C`.

## Definitions

```agda
Latin-Square : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Latin-Square l1 l2 l3 =
  Σ ( Inhabited-Type l1)
    ( λ A →
      Σ ( Inhabited-Type l2)
        ( λ B →
          Σ ( Inhabited-Type l3)
            ( λ C →
              Σ ( type-Inhabited-Type A → type-Inhabited-Type B →
                  type-Inhabited-Type C)
                ( is-binary-equiv))))

module _
  {l1 l2 l3 : Level} (L : Latin-Square l1 l2 l3)
  where

  inhabited-type-row-Latin-Square : Inhabited-Type l1
  inhabited-type-row-Latin-Square = pr1 L

  row-Latin-Square : UU l1
  row-Latin-Square = type-Inhabited-Type inhabited-type-row-Latin-Square

  inhabited-type-column-Latin-Square : Inhabited-Type l2
  inhabited-type-column-Latin-Square = pr1 (pr2 L)

  column-Latin-Square : UU l2
  column-Latin-Square = type-Inhabited-Type inhabited-type-column-Latin-Square

  inhabited-type-symbol-Latin-Square : Inhabited-Type l3
  inhabited-type-symbol-Latin-Square = pr1 (pr2 (pr2 L))

  symbol-Latin-Square : UU l3
  symbol-Latin-Square = type-Inhabited-Type inhabited-type-symbol-Latin-Square

  mul-Latin-Square :
    row-Latin-Square → column-Latin-Square → symbol-Latin-Square
  mul-Latin-Square = pr1 (pr2 (pr2 (pr2 L)))

  mul-Latin-Square' :
    column-Latin-Square → row-Latin-Square → symbol-Latin-Square
  mul-Latin-Square' x y = mul-Latin-Square y x

  is-binary-equiv-mul-Latin-Square :
    is-binary-equiv mul-Latin-Square
  is-binary-equiv-mul-Latin-Square = pr2 (pr2 (pr2 (pr2 L)))
```

## Properties

### The latin square of an inhabited [wild quasigroup](structured-types.wild-quasigroups.md)

```agda
Wild-Quasigroup-Latin-Square :
  {l : Level} → Wild-Quasigroup l → Latin-Square l l l
Wild-Quasigroup-Latin-Square A = ?
```

## See also

- The [groupoid](foundation.1-types.md) of main classes of latin squares is
  defined in
  [`univalent-combinatorics.main-classes-of-latin-squares`](univalent-combinatorics.main-classes-of-latin-squares.md).
