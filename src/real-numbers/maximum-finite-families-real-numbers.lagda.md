# The maximum of finite families of real numbers

```agda
module real-numbers.maximum-finite-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import real-numbers.dedekind-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import order-theory.join-semilattices
open import order-theory.joins-finite-families-join-semilattices
open import univalent-combinatorics.inhabited-finite-types
```
</details>

## Idea

The
{{#concept "maximum" Disambiguation="inhabited finite family, Dedekind real numbers" Agda=max-finite-family-ℝ WD="maximum" WDID=Q10578722}}
of a family of [Dedekind real numbers](real-numbers.dedekind-real-numbers.md)
indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md)
is their [least upper bound](order-theory.least-upper-bounds-large-posets.md).

## Definition

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (f : type-Inhabited-Finite-Type I → ℝ l2)
  where

  max-finite-family-ℝ : ℝ l2
  max-finite-family-ℝ =
    join-inhabited-finite-family-Order-Theoretic-Join-Semilattice
      ( ℝ-Order-Theoretic-Join-Semilattice l2)
      ( I)
      ( f)
```
