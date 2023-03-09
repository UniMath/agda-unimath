# The groupoid of main classes of Latin hypercubes

```agda
module univalent-combinatorics.main-classes-of-latin-hypercubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.mere-equivalences
open import foundation.products-unordered-tuples-of-types
open import foundation.set-truncations
open import foundation.universe-levels
open import foundation.unordered-tuples
open import foundation.unordered-tuples-of-types

open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

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

### The groupoid of main classes of Latin hypercubes of fixed finite order

```agda
Main-Class-Latin-Hypercube-of-Order : (n m : ℕ) → UU (lsuc lzero)
Main-Class-Latin-Hypercube-of-Order n m =
  Σ ( unordered-tuple (succ-ℕ n) (UU-Fin lzero m))
    ( λ A →
      Σ ( product-unordered-tuple-types (succ-ℕ n)
          ( map-unordered-tuple (succ-ℕ n) (type-UU-Fin m) A) →
          decidable-Prop lzero)
        ( λ R →
          (i : type-unordered-tuple (succ-ℕ n) A)
          (f : product-unordered-tuple-types n
               ( unordered-tuple-complement-point-type-unordered-tuple n
                 ( map-unordered-tuple (succ-ℕ n) (type-UU-Fin m) A)
                 ( i))) →
          is-contr
            ( Σ ( type-UU-Fin m (element-unordered-tuple (succ-ℕ n) A i))
                ( λ a →
                  type-decidable-Prop
                    ( R ( map-equiv-pr-product-unordered-tuple-types n
                          ( map-unordered-tuple (succ-ℕ n) (type-UU-Fin m) A)
                          ( i)
                          ( f)
                          ( a)))))))
```

## Properties

### The groupoid of main classes of Latin hypercubes of finite order is π-finite

```agda
is-π-finite-Main-Class-Latin-Hypercube-of-Order :
  (k n m : ℕ) → is-π-finite k (Main-Class-Latin-Hypercube-of-Order n m)
is-π-finite-Main-Class-Latin-Hypercube-of-Order k n m =
  is-π-finite-Σ k
    ( is-π-finite-Σ
      ( succ-ℕ k)
      ( is-π-finite-UU-Fin (succ-ℕ (succ-ℕ k)) (succ-ℕ n))
      ( λ X →
        is-π-finite-Π
          ( succ-ℕ k)
          ( is-finite-type-UU-Fin (succ-ℕ n) X)
          ( λ i → is-π-finite-UU-Fin (succ-ℕ k) m)))
    ( λ A →
      is-π-finite-Σ k
        ( is-π-finite-is-finite
          ( succ-ℕ k)
          ( is-finite-Π
            ( is-finite-Π
              ( is-finite-type-UU-Fin
                ( succ-ℕ n)
                ( type-unordered-tuple-UU-Fin (succ-ℕ n) A))
              ( λ i →
                is-finite-type-UU-Fin m
                  ( element-unordered-tuple (succ-ℕ n) A i)))
            ( λ f → is-finite-decidable-Prop)))
        ( λ R →
          is-π-finite-is-finite k
            ( is-finite-Π
              ( is-finite-type-UU-Fin
                ( succ-ℕ n)
                ( type-unordered-tuple-UU-Fin (succ-ℕ n) A))
              ( λ i →
                is-finite-Π
                  ( is-finite-Π
                    ( is-finite-has-cardinality n
                      ( has-cardinality-type-complement-point-UU-Fin n
                        ( pair (type-unordered-tuple-UU-Fin (succ-ℕ n) A) i)))
                    ( λ j →
                      is-finite-type-UU-Fin m
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
                                  ( type-UU-Fin m)
                                  ( A))
                                ( i)
                                ( f)
                                ( x)))
                          ( is-finite-type-UU-Fin m
                            ( element-unordered-tuple (succ-ℕ n) A i)))))))))
```

### The sequence of main classes of Latin hypercubes of fixed finite order

```agda
number-of-main-classes-of-Latin-hypercubes-of-order : ℕ → ℕ → ℕ
number-of-main-classes-of-Latin-hypercubes-of-order n m =
  number-of-elements-is-finite
    ( is-π-finite-Main-Class-Latin-Hypercube-of-Order 0 n m)

mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order :
  (n m : ℕ) →
  mere-equiv
    ( Fin (number-of-main-classes-of-Latin-hypercubes-of-order n m))
    ( type-trunc-Set
      ( Main-Class-Latin-Hypercube-of-Order n m))
mere-equiv-number-of-main-classes-of-Latin-hypercubes-of-order n m =
  mere-equiv-is-finite
    ( is-π-finite-Main-Class-Latin-Hypercube-of-Order 0 n m)
```
