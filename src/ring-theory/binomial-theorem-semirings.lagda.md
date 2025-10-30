# The binomial theorem for semirings

```agda
module ring-theory.binomial-theorem-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-semirings

open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "binomial theorem" Disambiguation="for semirings" Agda=binomial-theorem-Semiring}}
for [semirings](ring-theory.semirings.md) asserts that for any two elements `x`
and `y` of a semiring `R` such that `xy = yx` and any
[natural number](elementary-number-theory.natural-numbers.md) `n` we have

```text
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

The binomial theorem is the [44th](literature.100-theorems.md#44) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Binomial sums

```agda
binomial-sum-fin-sequence-type-Semiring :
  {l : Level} (R : Semiring l)
  (n : ℕ) (f : fin-sequence-type-Semiring R (succ-ℕ n)) →
  type-Semiring R
binomial-sum-fin-sequence-type-Semiring R n f =
  sum-fin-sequence-type-Semiring R (succ-ℕ n)
    ( λ i →
      mul-nat-scalar-Semiring R
        ( binomial-coefficient-Fin n i)
        ( f i))
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Semiring l)
  where

  binomial-sum-one-element-Semiring :
    (f : fin-sequence-type-Semiring R 1) →
    binomial-sum-fin-sequence-type-Semiring R 0 f ＝
    head-fin-sequence-type-Semiring R 0 f
  binomial-sum-one-element-Semiring f =
    ( compute-sum-one-element-Semiring R
      ( λ i →
        mul-nat-scalar-Semiring R
          ( binomial-coefficient-Fin 0 i)
          ( f i))) ∙
    ( left-unit-law-mul-nat-scalar-Semiring R
      ( head-fin-sequence-type-Semiring R 0 f))

  binomial-sum-two-elements-Semiring :
    (f : fin-sequence-type-Semiring R 2) →
    binomial-sum-fin-sequence-type-Semiring R 1 f ＝
    add-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Semiring f =
    compute-sum-two-elements-Semiring R
      ( λ i → mul-nat-scalar-Semiring R (binomial-coefficient-Fin 1 i) (f i)) ∙
      ( ap-binary
        ( add-Semiring R)
        ( left-unit-law-mul-nat-scalar-Semiring R (f (zero-Fin 1)))
        ( left-unit-law-mul-nat-scalar-Semiring R (f (one-Fin 1))))
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Semiring l)
  where

  htpy-binomial-sum-fin-sequence-type-Semiring :
    (n : ℕ) {f g : fin-sequence-type-Semiring R (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-fin-sequence-type-Semiring R n f ＝
    binomial-sum-fin-sequence-type-Semiring R n g
  htpy-binomial-sum-fin-sequence-type-Semiring n H =
    htpy-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( λ i →
        ap
          ( mul-nat-scalar-Semiring R (binomial-coefficient-Fin n i))
          ( H i))
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-distributive-mul-binomial-sum-fin-sequence-type-Semiring :
    (n : ℕ) (x : type-Semiring R)
    (f : fin-sequence-type-Semiring R (succ-ℕ n)) →
    mul-Semiring R x (binomial-sum-fin-sequence-type-Semiring R n f) ＝
    binomial-sum-fin-sequence-type-Semiring R n (λ i → mul-Semiring R x (f i))
  left-distributive-mul-binomial-sum-fin-sequence-type-Semiring n x f =
    ( left-distributive-mul-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( x)
      ( λ i →
        mul-nat-scalar-Semiring R (binomial-coefficient-Fin n i) (f i))) ∙
    ( htpy-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( λ i →
        right-nat-scalar-law-mul-Semiring R
          ( binomial-coefficient-Fin n i)
          ( x)
          ( f i)))

  right-distributive-mul-binomial-sum-fin-sequence-type-Semiring :
    (n : ℕ) (f : fin-sequence-type-Semiring R (succ-ℕ n)) →
    (x : type-Semiring R) →
    mul-Semiring R (binomial-sum-fin-sequence-type-Semiring R n f) x ＝
    binomial-sum-fin-sequence-type-Semiring R n (λ i → mul-Semiring R (f i) x)
  right-distributive-mul-binomial-sum-fin-sequence-type-Semiring n f x =
    ( right-distributive-mul-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( λ i →
        mul-nat-scalar-Semiring R (binomial-coefficient-Fin n i) (f i))
      ( x)) ∙
    ( htpy-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( λ i →
        left-nat-scalar-law-mul-Semiring R
          ( binomial-coefficient-Fin n i)
          ( f i)
          ( x)))
```

## Lemmas

### Computing a left summand that will appear in the proof of the binomial theorem

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-summand-binomial-theorem-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    (H : mul-Semiring R x y ＝ mul-Semiring R y x) →
    ( mul-Semiring R
      ( binomial-sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-Semiring R
            ( power-Semiring R (nat-Fin (succ-ℕ (succ-ℕ n)) i) x)
            ( power-Semiring R
              ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n)) y)))
      ( x)) ＝
    ( add-Semiring R
      ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
      ( sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
            ( mul-Semiring R
              ( power-Semiring R
                ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                ( x))
              ( power-Semiring R
                ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                ( y))))))
  left-summand-binomial-theorem-Semiring n x y H =
    ( right-distributive-mul-binomial-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( λ i →
        mul-Semiring R
          ( power-Semiring R
            ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
            ( x))
          ( power-Semiring R
            ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
            ( y)))
      ( x)) ∙
    ( ( htpy-binomial-sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( λ i →
          ( ( associative-mul-Semiring R
              ( power-Semiring R (nat-Fin (succ-ℕ (succ-ℕ n)) i) x)
              ( power-Semiring R
                ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
                ( y))
              ( x)) ∙
            ( ( ap
                ( mul-Semiring R
                  ( power-Semiring R (nat-Fin (succ-ℕ (succ-ℕ n)) i) x))
                ( commute-powers-Semiring' R
                  ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
                  ( inv H))) ∙
              ( inv
                ( associative-mul-Semiring R
                  ( power-Semiring R (nat-Fin (succ-ℕ (succ-ℕ n)) i) x)
                  ( x)
                  ( power-Semiring R
                    ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
                    ( y)))))) ∙
          ( ap
            ( mul-Semiring' R
              ( power-Semiring R
                ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
                ( y)))
            ( inv
              ( power-succ-Semiring R
                ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                ( x)))))) ∙
      ( ( ap
          ( add-Semiring R _)
          ( ( ap-mul-nat-scalar-Semiring R
              ( is-one-on-diagonal-binomial-coefficient-ℕ (succ-ℕ n))
              ( ap
                ( λ t →
                  mul-Semiring R
                    ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
                    ( power-Semiring R t y))
                ( dist-eq-ℕ' (succ-ℕ n)))) ∙
            ( ( left-unit-law-mul-nat-scalar-Semiring R
                ( mul-Semiring R
                  ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
                  ( one-Semiring R))) ∙
              ( right-unit-law-mul-Semiring R
                ( power-Semiring R (succ-ℕ (succ-ℕ n)) x))))) ∙
        ( commutative-add-Semiring R
          ( sum-fin-sequence-type-Semiring R
            ( succ-ℕ n)
            ( λ i →
              mul-nat-scalar-Semiring R
                ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
                ( mul-Semiring R
                  ( power-Semiring R
                    ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                    ( x))
                  ( power-Semiring R
                    ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                    ( y)))))
          ( power-Semiring R (succ-ℕ (succ-ℕ n)) x))))
```

### Computing a right summand that will appear in the proof of the binomial theorem

```agda
  right-summand-binomial-theorem-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    ( mul-Semiring R
      ( binomial-sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-Semiring R
            ( power-Semiring R
              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
              ( x))
            ( power-Semiring R
              ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
              ( y))))
      ( y)) ＝
    ( add-Semiring R
      ( power-Semiring R (succ-ℕ (succ-ℕ n)) y)
      ( sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-ℕ
              ( succ-ℕ n)
              ( succ-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
            ( mul-Semiring R
              ( power-Semiring R
                ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                ( x))
              ( power-Semiring R
                ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                ( y))))))
  right-summand-binomial-theorem-Semiring n x y =
    ( right-distributive-mul-binomial-sum-fin-sequence-type-Semiring R
      ( succ-ℕ n)
      ( λ i →
        mul-Semiring R
          ( power-Semiring R
            ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
            ( x))
          ( power-Semiring R
            ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
            ( y)))
      ( y)) ∙
    ( ( htpy-binomial-sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( λ i →
          ( associative-mul-Semiring R
            ( power-Semiring R
              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
              ( x))
            ( power-Semiring R
              ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
              ( y))
            ( y)) ∙
          ( ap
            ( mul-Semiring R
              ( power-Semiring R
                ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                ( x)))
            ( inv
              ( ap
                ( λ m → power-Semiring R m y)
                ( right-successor-law-dist-ℕ
                  ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                  ( succ-ℕ n)
                  ( upper-bound-nat-Fin (succ-ℕ n) i)) ∙
                ( power-succ-Semiring R
                  ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ n))
                  ( y))))))) ∙
      ( ( snoc-sum-fin-sequence-type-Semiring R
          ( succ-ℕ n)
          ( λ i →
            mul-nat-scalar-Semiring R
              ( binomial-coefficient-Fin (succ-ℕ n) i)
              ( mul-Semiring R
                ( power-Semiring R
                  ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                  ( x))
                ( power-Semiring R
                  ( dist-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) i) (succ-ℕ (succ-ℕ n)))
                  ( y))))
          ( ( ap
              ( λ m →
                mul-nat-scalar-Semiring R
                  ( binomial-coefficient-ℕ (succ-ℕ n) m)
                  ( mul-Semiring R
                    ( power-Semiring R m x)
                    ( power-Semiring R
                      ( dist-ℕ m (succ-ℕ (succ-ℕ n)))
                      ( y))))
              ( is-zero-nat-zero-Fin {n})) ∙
            ( ( left-unit-law-mul-nat-scalar-Semiring R
                ( mul-Semiring R
                  ( one-Semiring R)
                  ( power-Semiring R (succ-ℕ (succ-ℕ n)) y))) ∙
              ( left-unit-law-mul-Semiring R
                ( power-Semiring R (succ-ℕ (succ-ℕ n)) y))))) ∙
        ( ap-add-Semiring R
          ( refl)
          ( htpy-sum-fin-sequence-type-Semiring R
            ( succ-ℕ n)
            ( λ i →
              ( ap
                ( λ m →
                  mul-nat-scalar-Semiring R
                    ( binomial-coefficient-ℕ (succ-ℕ n) m)
                    ( mul-Semiring R
                      ( power-Semiring R m x)
                      ( power-Semiring R
                        ( dist-ℕ m (succ-ℕ (succ-ℕ n)))
                        ( y))))
                ( nat-inr-Fin (succ-ℕ n) i)))))))
```

## Theorem

### Binomial theorem for semirings

```agda
binomial-theorem-Semiring :
  {l : Level} (R : Semiring l) (n : ℕ) (x y : type-Semiring R) →
  mul-Semiring R x y ＝ mul-Semiring R y x →
  power-Semiring R n (add-Semiring R x y) ＝
  binomial-sum-fin-sequence-type-Semiring R n
    ( λ i →
      mul-Semiring R
      ( power-Semiring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Semiring R (dist-ℕ (nat-Fin (succ-ℕ n) i) n) y))
binomial-theorem-Semiring R zero-ℕ x y H =
  inv
    ( ( compute-sum-one-element-Semiring R
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-Fin 0 i)
            ( mul-Semiring R
              ( power-Semiring R (nat-Fin 1 i) x)
              ( power-Semiring R (dist-ℕ (nat-Fin 1 i) 0) y)))) ∙
      ( ( left-unit-law-mul-nat-scalar-Semiring R
          ( mul-Semiring R
            ( one-Semiring R)
            ( one-Semiring R))) ∙
        ( left-unit-law-mul-Semiring R (one-Semiring R))))
binomial-theorem-Semiring R (succ-ℕ zero-ℕ) x y H =
  ( commutative-add-Semiring R x y) ∙
  ( ( ap-binary
      ( add-Semiring R)
      ( ( inv (left-unit-law-mul-Semiring R y)) ∙
        ( inv
          ( left-unit-law-mul-nat-scalar-Semiring R
            ( mul-Semiring R (one-Semiring R) y))))
      ( ( inv (right-unit-law-mul-Semiring R x)) ∙
        ( inv
          ( left-unit-law-mul-nat-scalar-Semiring R
            ( mul-Semiring R x (one-Semiring R)))))) ∙
    ( inv
      ( compute-sum-two-elements-Semiring R
        ( λ i →
          mul-nat-scalar-Semiring R
          ( binomial-coefficient-Fin 1 i)
          ( mul-Semiring R
            ( power-Semiring R (nat-Fin 2 i) x)
            ( power-Semiring R (dist-ℕ (nat-Fin 2 i) 1) y))))))
binomial-theorem-Semiring R (succ-ℕ (succ-ℕ n)) x y H =
  ( ap
    ( λ r → mul-Semiring R r (add-Semiring R x y))
    ( binomial-theorem-Semiring R (succ-ℕ n) x y H)) ∙
  ( ( left-distributive-mul-add-Semiring R _ x y) ∙
    ( ( ap-add-Semiring R
        ( left-summand-binomial-theorem-Semiring R n x y H)
        ( right-summand-binomial-theorem-Semiring R n x y)) ∙
      ( ( interchange-add-add-Semiring R
          ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
          ( sum-fin-sequence-type-Semiring R
            ( succ-ℕ n)
            ( λ i →
              mul-nat-scalar-Semiring R
              ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
              ( mul-Semiring R
                ( power-Semiring R
                  ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                  ( x))
                ( power-Semiring R
                  ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                  ( y)))))
          ( power-Semiring R (succ-ℕ (succ-ℕ n)) y)
          ( sum-fin-sequence-type-Semiring R
            ( succ-ℕ n)
            ( λ i →
              mul-nat-scalar-Semiring R
              ( binomial-coefficient-ℕ
                ( succ-ℕ n)
                ( succ-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
              ( mul-Semiring R
                ( power-Semiring R
                  ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                  ( x))
                ( power-Semiring R
                  ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                  ( y)))))) ∙
        ( ( ap-add-Semiring R
            ( commutative-add-Semiring R
              ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
              ( power-Semiring R (succ-ℕ (succ-ℕ n)) y))
            ( ( interchange-add-sum-fin-sequence-type-Semiring R
                ( succ-ℕ n)
                ( λ i →
                  mul-nat-scalar-Semiring R
                  ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
                  ( mul-Semiring R
                    ( power-Semiring R
                      ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                      ( x))
                    ( power-Semiring R
                      ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                      ( y))))
                ( λ i →
                  mul-nat-scalar-Semiring R
                  ( binomial-coefficient-ℕ
                    ( succ-ℕ n)
                    ( succ-ℕ
                      ( nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
                    ( mul-Semiring R
                      ( power-Semiring R
                        ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                        ( x))
                      ( power-Semiring R
                        ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                        ( y))))) ∙
              ( htpy-sum-fin-sequence-type-Semiring R
                ( succ-ℕ n)
                ( λ i →
                  ( inv
                    ( right-distributive-mul-nat-scalar-add-Semiring R
                      ( binomial-coefficient-ℕ
                        ( succ-ℕ n)
                        ( nat-Fin (succ-ℕ n) i))
                      ( binomial-coefficient-ℕ
                        ( succ-ℕ n)
                        ( succ-ℕ (nat-Fin (succ-ℕ n) i)))
                      ( mul-Semiring R
                        ( power-Semiring R
                          ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                          ( x))
                        ( power-Semiring R
                          ( dist-ℕ (nat-Fin (succ-ℕ n) i) (succ-ℕ n))
                          ( y))))) ∙
                  ( ap
                    ( λ m →
                      mul-nat-scalar-Semiring R
                        ( binomial-coefficient-ℕ (succ-ℕ (succ-ℕ n)) m)
                        ( mul-Semiring R
                          ( power-Semiring R m x)
                          ( power-Semiring R
                            ( dist-ℕ m (succ-ℕ (succ-ℕ n)))
                            ( y))))
                    ( inv (nat-inr-Fin (succ-ℕ n) i))))))) ∙
          ( ( right-swap-add-Semiring R
              ( power-Semiring R (succ-ℕ (succ-ℕ n)) y)
              ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)
              ( _)) ∙
            ( ( ap
                ( add-Semiring' R
                  ( power-Semiring R (succ-ℕ (succ-ℕ n)) x))
                ( inv
                  ( snoc-sum-fin-sequence-type-Semiring R
                    ( succ-ℕ n)
                    ( λ i →
                      mul-nat-scalar-Semiring R
                        ( binomial-coefficient-ℕ
                          ( succ-ℕ (succ-ℕ n))
                          ( nat-Fin (succ-ℕ (succ-ℕ n)) i))
                        ( mul-Semiring R
                          ( power-Semiring R
                            ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                            ( x))
                          ( power-Semiring R
                            ( dist-ℕ
                              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                              ( succ-ℕ (succ-ℕ n)))
                            ( y))))
                    ( ( ap
                        ( λ m →
                          mul-nat-scalar-Semiring R
                            ( binomial-coefficient-ℕ (succ-ℕ (succ-ℕ n)) m)
                            ( mul-Semiring R
                              ( power-Semiring R m x)
                              ( power-Semiring R
                                ( dist-ℕ m (succ-ℕ (succ-ℕ n)))
                                ( y))))
                        ( is-zero-nat-zero-Fin {n})) ∙
                      ( ( left-unit-law-mul-nat-scalar-Semiring R
                          ( mul-Semiring R
                            ( one-Semiring R)
                            ( power-Semiring R
                              ( succ-ℕ (succ-ℕ n))
                              ( y)))) ∙
                        ( left-unit-law-mul-Semiring R
                          ( power-Semiring R
                            ( succ-ℕ (succ-ℕ n))
                            ( y)))))))) ∙
              ( inv
                ( cons-sum-fin-sequence-type-Semiring R
                  ( succ-ℕ (succ-ℕ n))
                  ( λ i →
                    mul-nat-scalar-Semiring R
                      ( binomial-coefficient-Fin (succ-ℕ (succ-ℕ n)) i)
                      ( mul-Semiring R
                        ( power-Semiring R
                          ( nat-Fin (succ-ℕ (succ-ℕ (succ-ℕ n))) i)
                          ( x))
                        ( power-Semiring R
                          ( dist-ℕ
                            ( nat-Fin (succ-ℕ (succ-ℕ (succ-ℕ n))) i)
                            ( succ-ℕ (succ-ℕ n)))
                          ( y))))
                  ( ( ap-mul-nat-scalar-Semiring R
                      ( is-one-on-diagonal-binomial-coefficient-ℕ
                        ( succ-ℕ (succ-ℕ n)))
                      ( ( ap
                          ( mul-Semiring R
                            ( power-Semiring R (succ-ℕ (succ-ℕ n)) x))
                          ( ap
                            ( λ m → power-Semiring R m y)
                            ( dist-eq-ℕ' (succ-ℕ (succ-ℕ n))))) ∙
                        ( right-unit-law-mul-Semiring R
                          ( power-Semiring R (succ-ℕ (succ-ℕ n)) x)))) ∙
                    ( left-unit-law-mul-nat-scalar-Semiring R
                      ( power-Semiring R
                        ( succ-ℕ (succ-ℕ n))
                        ( x))))))))))))
```

## Corollaries

### If `x` commutes with `y`, then we can compute `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Semiring :
  {l : Level} (R : Semiring l) (n m : ℕ) (x y : type-Semiring R) →
  mul-Semiring R x y ＝ mul-Semiring R y x →
  power-Semiring R (n +ℕ m) (add-Semiring R x y) ＝
  add-Semiring R
    ( mul-Semiring R
      ( power-Semiring R m y)
      ( sum-fin-sequence-type-Semiring R n
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
            ( mul-Semiring R
              ( power-Semiring R (nat-Fin n i) x)
              ( power-Semiring R (dist-ℕ (nat-Fin n i) n) y)))))
    ( mul-Semiring R
      ( power-Semiring R n x)
      ( sum-fin-sequence-type-Semiring R
        ( succ-ℕ m)
        ( λ i →
          mul-nat-scalar-Semiring R
            ( binomial-coefficient-ℕ
              ( n +ℕ m)
              ( n +ℕ (nat-Fin (succ-ℕ m) i)))
            ( mul-Semiring R
              ( power-Semiring R (nat-Fin (succ-ℕ m) i) x)
              ( power-Semiring R (dist-ℕ (nat-Fin (succ-ℕ m) i) m) y)))))
is-linear-combination-power-add-Semiring R n m x y H =
  ( binomial-theorem-Semiring R (n +ℕ m) x y H) ∙
  ( ( split-sum-fin-sequence-type-Semiring R n
      ( succ-ℕ m)
      ( λ i →
        mul-nat-scalar-Semiring R
          ( binomial-coefficient-ℕ
            ( n +ℕ m)
            ( nat-Fin (n +ℕ (succ-ℕ m)) i))
          ( mul-Semiring R
            ( power-Semiring R
              ( nat-Fin (n +ℕ (succ-ℕ m)) i)
              ( x))
            ( power-Semiring R
              ( dist-ℕ
                ( nat-Fin (n +ℕ (succ-ℕ m)) i)
                ( n +ℕ m))
              ( y))))) ∙
    ( ( ap-add-Semiring R
        ( ( htpy-sum-fin-sequence-type-Semiring R n
            ( λ i →
              ( ap
                ( λ u →
                  mul-nat-scalar-Semiring R
                    ( binomial-coefficient-ℕ (n +ℕ m) u)
                    ( mul-Semiring R
                      ( power-Semiring R u x)
                      ( power-Semiring R
                        ( dist-ℕ u (n +ℕ m))
                        ( y))))
                ( nat-inl-coproduct-Fin n m i)) ∙
              ( ( ( ap
                    ( mul-nat-scalar-Semiring R
                      ( binomial-coefficient-ℕ
                        ( n +ℕ m)
                        ( nat-Fin n i)))
                    ( ( ap
                        ( mul-Semiring R
                          ( power-Semiring R
                            ( nat-Fin n i)
                            ( x)))
                        ( ( ap
                            ( λ u → power-Semiring R u y)
                            ( ( inv
                                ( triangle-equality-dist-ℕ
                                  ( nat-Fin n i)
                                  ( n)
                                  ( n +ℕ m)
                                  ( upper-bound-nat-Fin' n i)
                                  ( leq-add-ℕ n m)) ∙
                                ( ap
                                  ( (dist-ℕ (nat-Fin n i) n) +ℕ_)
                                  ( dist-add-ℕ n m))) ∙
                              ( commutative-add-ℕ
                                ( dist-ℕ (nat-Fin n i) n)
                                ( m)))) ∙
                          ( ( distributive-power-add-Semiring R m
                              ( dist-ℕ (nat-Fin n i) n))))) ∙
                      ( ( inv
                          ( associative-mul-Semiring R
                            ( power-Semiring R (nat-Fin n i) x)
                            ( power-Semiring R m y)
                            ( power-Semiring R (dist-ℕ (nat-Fin n i) n) y))) ∙
                        ( ( ap
                            ( mul-Semiring' R
                              ( power-Semiring R (dist-ℕ (nat-Fin n i) n) y))
                            ( commute-powers-Semiring R (nat-Fin n i) m H)) ∙
                          ( associative-mul-Semiring R
                            ( power-Semiring R m y)
                            ( power-Semiring R (nat-Fin n i) x)
                            ( power-Semiring R
                              ( dist-ℕ (nat-Fin n i) n)
                              ( y))))))) ∙
                  ( inv
                    ( right-nat-scalar-law-mul-Semiring R
                      ( binomial-coefficient-ℕ
                        ( n +ℕ m)
                        ( nat-Fin n i))
                      ( power-Semiring R m y)
                      ( mul-Semiring R
                        ( power-Semiring R (nat-Fin n i) x)
                        ( power-Semiring R
                          ( dist-ℕ (nat-Fin n i) n)
                          ( y))))))))) ∙
          ( ( inv
              ( left-distributive-mul-sum-fin-sequence-type-Semiring R n
                ( power-Semiring R m y)
                ( λ i →
                  mul-nat-scalar-Semiring R
                    ( binomial-coefficient-ℕ (n +ℕ m) (nat-Fin n i))
                    ( mul-Semiring R
                      ( power-Semiring R (nat-Fin n i) x)
                      ( power-Semiring R (dist-ℕ (nat-Fin n i) n) y)))))))
        ( ( htpy-sum-fin-sequence-type-Semiring R
            ( succ-ℕ m)
            ( λ i →
              ( ap
                ( λ u →
                  mul-nat-scalar-Semiring R
                    ( binomial-coefficient-ℕ (n +ℕ m) u)
                    ( mul-Semiring R
                      ( power-Semiring R u x)
                      ( power-Semiring R
                        ( dist-ℕ u (n +ℕ m))
                        ( y))))
                ( nat-inr-coproduct-Fin n (succ-ℕ m) i)) ∙
              ( ( ap
                  ( mul-nat-scalar-Semiring R
                    ( binomial-coefficient-ℕ
                      ( n +ℕ m)
                      ( n +ℕ (nat-Fin (succ-ℕ m) i))))
                  ( ap-mul-Semiring R
                    ( distributive-power-add-Semiring R n
                      ( nat-Fin (succ-ℕ m) i))
                    ( ap
                      ( λ u → power-Semiring R u y)
                      ( translation-invariant-dist-ℕ
                        ( n)
                        ( nat-Fin (succ-ℕ m) i)
                        ( m))) ∙
                    ( associative-mul-Semiring R
                      ( power-Semiring R n x)
                      ( power-Semiring R (nat-Fin (succ-ℕ m) i) x)
                      ( power-Semiring R
                        ( dist-ℕ (nat-Fin (succ-ℕ m) i) m)
                        ( y))))) ∙
                ( inv
                  ( right-nat-scalar-law-mul-Semiring R
                    ( binomial-coefficient-ℕ
                      ( n +ℕ m)
                      ( n +ℕ (nat-Fin (succ-ℕ m) i)))
                    ( power-Semiring R n x)
                    ( mul-Semiring R
                      ( power-Semiring R (nat-Fin (succ-ℕ m) i) x)
                      ( power-Semiring R
                        ( dist-ℕ (nat-Fin (succ-ℕ m) i) m)
                        ( y)))))))) ∙
          ( inv
            ( left-distributive-mul-sum-fin-sequence-type-Semiring R
              ( succ-ℕ m)
              ( power-Semiring R n x)
              ( λ i →
                mul-nat-scalar-Semiring R
                  ( binomial-coefficient-ℕ
                    ( n +ℕ m)
                    ( n +ℕ (nat-Fin (succ-ℕ m) i)))
                  ( mul-Semiring R
                    ( power-Semiring R (nat-Fin (succ-ℕ m) i) x)
                    ( power-Semiring R
                      ( dist-ℕ (nat-Fin (succ-ℕ m) i) m)
                      ( y))))))))))
```

## References

{{#bibliography}}
