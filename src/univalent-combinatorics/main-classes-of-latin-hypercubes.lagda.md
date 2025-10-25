# The groupoid of main classes of Latin hypercubes

```agda
module univalent-combinatorics.main-classes-of-latin-hypercubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.1-types
open import foundation.contractible-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.mere-equivalences
open import foundation.products-unordered-tuples-of-types
open import foundation.set-truncations
open import foundation.universe-levels
open import foundation.unordered-tuples

open import univalent-combinatorics.complements-isolated-elements
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.truncated-pi-finite-types
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Definitions

### The type of main classes of Latin hypercubes

```agda
Main-Class-Latin-Hypercube : (l1 l2 : Level) (n : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Main-Class-Latin-Hypercube l1 l2 n =
  Σ ( unordered-tuple (succ-ℕ n) (Inhabited-Type l1))
    ( λ A →
      Σ ( product-unordered-tuple-types (succ-ℕ n)
          ( map-unordered-tuple (succ-ℕ n) type-Inhabited-Type A) → UU l2)
        ( λ R →
          ( i : type-unordered-tuple (succ-ℕ n) A)
          ( f : product-unordered-tuple-types n
                ( unordered-tuple-complement-point-type-unordered-tuple n
                  ( map-unordered-tuple (succ-ℕ n) type-Inhabited-Type A)
                  ( i))) →
          is-contr
            ( Σ ( type-Inhabited-Type (element-unordered-tuple (succ-ℕ n) A i))
                ( λ a →
                  R ( map-equiv-pr-product-unordered-tuple-types n
                      ( map-unordered-tuple (succ-ℕ n) type-Inhabited-Type A)
                      ( i)
                      ( f)
                      ( a))))))
```

### The type of main classes of Latin hypercubes of fixed finite order

```agda
Main-Class-Latin-Hypercube-of-Order : (n m : ℕ) → UU (lsuc lzero)
Main-Class-Latin-Hypercube-of-Order n m =
  Σ ( unordered-tuple (succ-ℕ n) (Type-With-Cardinality-ℕ lzero m))
    ( λ A →
      Σ ( product-unordered-tuple-types (succ-ℕ n)
          ( map-unordered-tuple
            ( succ-ℕ n)
            ( type-Type-With-Cardinality-ℕ m) A) →
          Decidable-Prop lzero)
        ( λ R →
          (i : type-unordered-tuple (succ-ℕ n) A)
          (f :
            product-unordered-tuple-types n
              ( unordered-tuple-complement-point-type-unordered-tuple n
                ( map-unordered-tuple
                  ( succ-ℕ n)
                  ( type-Type-With-Cardinality-ℕ m) A)
                ( i))) →
          is-contr
            ( Σ ( type-Type-With-Cardinality-ℕ m
                  ( element-unordered-tuple (succ-ℕ n) A i))
                ( λ a →
                  type-Decidable-Prop
                    ( R ( map-equiv-pr-product-unordered-tuple-types n
                          ( map-unordered-tuple
                            ( succ-ℕ n)
                            ( type-Type-With-Cardinality-ℕ m) A)
                          ( i)
                          ( f)
                          ( a)))))))
```

## Properties

### The type of main classes of Latin hypercubes of fixed finite order is a groupoid

```agda
is-1-type-Main-Class-Latin-Hypercube-of-Order :
  (n m : ℕ) → is-1-type (Main-Class-Latin-Hypercube-of-Order n m)
is-1-type-Main-Class-Latin-Hypercube-of-Order n m =
  is-1-type-Σ
    ( is-1-type-unordered-tuple
      ( succ-ℕ n)
      ( is-1-type-Type-With-Cardinality-ℕ m))
    ( λ A →
      is-1-type-Σ
        ( is-1-type-function-type (is-1-type-is-set is-set-Decidable-Prop))
        ( λ R →
          is-1-type-Π
            ( λ i →
              is-1-type-Π (λ f → is-1-type-is-prop is-property-is-contr))))
```

### The groupoid of main classes of Latin hypercubes of finite order is unbounded π-finite

```agda
is-untruncated-π-finite-Main-Class-Latin-Hypercube-of-Order :
  (k n m : ℕ) →
  is-untruncated-π-finite k (Main-Class-Latin-Hypercube-of-Order n m)
is-untruncated-π-finite-Main-Class-Latin-Hypercube-of-Order k n m =
  is-untruncated-π-finite-Σ k
    ( is-untruncated-π-finite-Σ
      ( succ-ℕ k)
      ( is-untruncated-π-finite-Type-With-Cardinality-ℕ
        ( succ-ℕ (succ-ℕ k))
        ( succ-ℕ n))
      ( λ X →
        is-untruncated-π-finite-Π
          ( succ-ℕ k)
          ( is-finite-type-Type-With-Cardinality-ℕ (succ-ℕ n) X)
          ( λ i →
            is-untruncated-π-finite-Type-With-Cardinality-ℕ (succ-ℕ k) m)))
    ( λ A →
      is-untruncated-π-finite-Σ k
        ( is-untruncated-π-finite-is-finite
          ( succ-ℕ k)
          ( is-finite-Π
            ( is-finite-Π
              ( is-finite-type-Type-With-Cardinality-ℕ
                ( succ-ℕ n)
                ( type-unordered-tuple-Type-With-Cardinality-ℕ
                  ( succ-ℕ n)
                  ( A)))
              ( λ i →
                is-finite-type-Type-With-Cardinality-ℕ m
                  ( element-unordered-tuple (succ-ℕ n) A i)))
            ( λ f → is-finite-Decidable-Prop)))
        ( λ R →
          is-untruncated-π-finite-is-finite k
            ( is-finite-Π
              ( is-finite-type-Type-With-Cardinality-ℕ
                ( succ-ℕ n)
                ( type-unordered-tuple-Type-With-Cardinality-ℕ
                  ( succ-ℕ n)
                  ( A)))
              ( λ i →
                is-finite-Π
                  ( is-finite-Π
                    ( is-finite-has-cardinality-ℕ n
                      ( has-cardinality-type-complement-element-Type-With-Cardinality-ℕ
                        ( n)
                        ( type-unordered-tuple-Type-With-Cardinality-ℕ
                            ( succ-ℕ n)
                            ( A) ,
                          i)))
                    ( λ j →
                      is-finite-type-Type-With-Cardinality-ℕ m
                        ( element-unordered-tuple (succ-ℕ n) A (pr1 j))))
                  ( λ f →
                    is-finite-is-decidable-Prop
                      ( is-contr-Prop _)
                      ( is-decidable-is-contr-is-finite
                        ( is-finite-type-decidable-subtype
                          ( λ x →
                            R ( map-equiv-pr-product-unordered-tuple-types n
                                ( map-unordered-tuple
                                  ( succ-ℕ n)
                                  ( type-Type-With-Cardinality-ℕ m)
                                  ( A))
                                ( i)
                                ( f)
                                ( x)))
                          ( is-finite-type-Type-With-Cardinality-ℕ m
                            ( element-unordered-tuple (succ-ℕ n) A i)))))))))
```

### The groupoid of main classes of Latin hypercubes of finite order is π₁-finite

```agda
is-truncated-π-finite-Main-Class-Latin-Hypercube-of-Order :
  (n m : ℕ) → is-truncated-π-finite 1 (Main-Class-Latin-Hypercube-of-Order n m)
is-truncated-π-finite-Main-Class-Latin-Hypercube-of-Order n m =
  is-truncated-π-finite-is-untruncated-π-finite 1
    ( is-1-type-Main-Class-Latin-Hypercube-of-Order n m)
    ( is-untruncated-π-finite-Main-Class-Latin-Hypercube-of-Order 1 n m)
```

### The sequence of main classes of Latin hypercubes of fixed finite order

```agda
number-of-main-classes-of-Latin-hypercubes-of-order : ℕ → ℕ → ℕ
number-of-main-classes-of-Latin-hypercubes-of-order n m =
  number-of-elements-is-finite
    ( is-untruncated-π-finite-Main-Class-Latin-Hypercube-of-Order 0 n m)

mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order :
  (n m : ℕ) →
  mere-equiv
    ( Fin (number-of-main-classes-of-Latin-hypercubes-of-order n m))
    ( type-trunc-Set
      ( Main-Class-Latin-Hypercube-of-Order n m))
mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order n m =
  mere-equiv-is-finite
    ( is-untruncated-π-finite-Main-Class-Latin-Hypercube-of-Order 0 n m)
```
