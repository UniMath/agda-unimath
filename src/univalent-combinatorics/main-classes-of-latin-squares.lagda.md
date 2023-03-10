# The groupoid of main classes of Latin squares

```agda
module univalent-combinatorics.main-classes-of-latin-squares where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.mere-equivalences
open import foundation.set-truncations
open import foundation.universe-levels

open import univalent-combinatorics.main-classes-of-latin-hypercubes
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The groupoid of main classes of latin squares consists of unordered triples of inhabited types equipped with a ternary 1-1 correspondence.

## Definition

### Main classes of general latin squares

```agda
Main-Class-Latin-Squares : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Main-Class-Latin-Squares l1 l2 = Main-Class-Latin-Hypercube l1 l2 2
```

### Main classes of latin squares of fixed finite order

```agda
Main-Class-Latin-Square-of-Order : (m : ℕ) → UU (lsuc lzero)
Main-Class-Latin-Square-of-Order m =
  Main-Class-Latin-Hypercube-of-Order 2 m
```

## Properties

### The groupoid of main classes of latin squares of fixed order is π-finite

```agda
is-π-finite-Main-Class-Latin-Square-of-Order :
  (k m : ℕ) → is-π-finite k (Main-Class-Latin-Square-of-Order m)
is-π-finite-Main-Class-Latin-Square-of-Order k m =
  is-π-finite-Main-Class-Latin-Hypercube-of-Order k 2 m
```

### The sequence of the number of main classes of latin squares of finite order

The following sequence defines [A003090](https://oeis.org/A003090) in the OEIS.

```agda
number-of-main-classes-of-Latin-squares-of-order : ℕ → ℕ
number-of-main-classes-of-Latin-squares-of-order =
  number-of-main-classes-of-Latin-hypercubes-of-order 2

mere-equiv-number-of-main-classes-of-Latin-squares-of-order :
  (m : ℕ) →
  mere-equiv
    ( Fin (number-of-main-classes-of-Latin-squares-of-order m))
    ( type-trunc-Set (Main-Class-Latin-Square-of-Order m))
mere-equiv-number-of-main-classes-of-Latin-squares-of-order =
  mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order 2
```
