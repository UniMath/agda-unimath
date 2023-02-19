# The binomial theorem in commutative rings

```agda
module commutative-algebra.binomial-theorem-commutative-rings where

open import commutative-algebra.commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors-on-commutative-rings

open import univalent-combinatorics.standard-finite-types
```

## Idea

The binomial theorem in commutative rings asserts that for any two elements `x` and `y` of a commutative ring `R` and any natural number `n`, we have

```md
  (x + y)ⁿ = ∑_{0 ≤ i < n+1} (n choose i) xⁱ yⁿ⁻ⁱ.
```

## Definitions

### Binomial sums

```agda
binomial-sum-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l)
  (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
  type-Commutative-Ring R
binomial-sum-Commutative-Ring R n f =
  sum-Commutative-Ring R (succ-ℕ n)
    ( λ i →
      mul-nat-Commutative-Ring R
        ( binomial-coefficient-Fin n i)
        ( f i))
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where
  
  binomial-sum-one-element-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 1) →
    binomial-sum-Commutative-Ring R 0 f ＝
    head-functional-vec-Commutative-Ring R 0 f
  binomial-sum-one-element-Commutative-Ring f =
    ( sum-one-element-Commutative-Ring R
      ( λ i →
        mul-nat-Commutative-Ring R
          ( binomial-coefficient-Fin 0 i)
          ( f i))) ∙
    ( mul-nat-one-Commutative-Ring R
      ( head-functional-vec-Commutative-Ring R 0 f))

  binomial-sum-two-elements-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 2) →
    binomial-sum-Commutative-Ring R 1 f ＝
    add-Commutative-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  binomial-sum-two-elements-Commutative-Ring f =
    sum-two-elements-Commutative-Ring R
      ( λ i → mul-nat-Commutative-Ring R (binomial-coefficient-Fin 1 i) (f i)) ∙
      ( ap-binary
        ( add-Commutative-Ring R)
        ( mul-nat-one-Commutative-Ring R (f (zero-Fin 1)))
        ( mul-nat-one-Commutative-Ring R (f (one-Fin 1))))
```

### Binomial sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-binomial-sum-Commutative-Ring :
    (n : ℕ) {f g : functional-vec-Commutative-Ring R (succ-ℕ n)} →
    (f ~ g) →
    binomial-sum-Commutative-Ring R n f ＝ binomial-sum-Commutative-Ring R n g
  htpy-binomial-sum-Commutative-Ring n H =
    htpy-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( λ i →
        ap
          ( mul-nat-Commutative-Ring R (binomial-coefficient-Fin n i))
          ( H i))
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-binomial-sum-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R)
    (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    mul-Commutative-Ring R x (binomial-sum-Commutative-Ring R n f) ＝
    binomial-sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R x (f i))
  left-distributive-mul-binomial-sum-Commutative-Ring n x f =
    ( left-distributive-mul-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( x)
      ( λ i →
        mul-nat-Commutative-Ring R (binomial-coefficient-Fin n i) (f i))) ∙
    ( htpy-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( λ i →
        right-mul-nat-law-mul-Commutative-Ring R
          ( binomial-coefficient-Fin n i)
          ( x)
          ( f i)))

  right-distributive-mul-binomial-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    (x : type-Commutative-Ring R) →
    mul-Commutative-Ring R (binomial-sum-Commutative-Ring R n f) x ＝
    binomial-sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R (f i) x)
  right-distributive-mul-binomial-sum-Commutative-Ring n f x =
    ( right-distributive-mul-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( λ i →
        mul-nat-Commutative-Ring R (binomial-coefficient-Fin n i) (f i))
      ( x)) ∙
    ( htpy-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( λ i →
        left-mul-nat-law-mul-Commutative-Ring R
          ( binomial-coefficient-Fin n i)
          ( f i )
          ( x)))
```

## Lemmas

### Computing a left summand that will appear in the proof of the binomial theorem

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-summand-binomial-theorem-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring R) →
    ( mul-Commutative-Ring R
      ( binomial-sum-Commutative-Ring R
        ( succ-ℕ n)
        ( λ i →
          mul-Commutative-Ring R
            ( power-Commutative-Ring R (nat-Fin (succ-ℕ (succ-ℕ n)) i) x)
            ( power-Commutative-Ring R
              ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i)) y)))
      ( x)) ＝
    ( add-Commutative-Ring R
      ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)
      ( sum-Commutative-Ring R
        ( succ-ℕ n)
        ( λ i →
          mul-nat-Commutative-Ring R
            ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
            ( mul-Commutative-Ring R
              ( power-Commutative-Ring R
                ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                ( x))
              ( power-Commutative-Ring R
                ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                ( y))))))
  left-summand-binomial-theorem-Commutative-Ring n x y =
    ( right-distributive-mul-binomial-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( λ i →
        mul-Commutative-Ring R
          ( power-Commutative-Ring R
            ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
            ( x))
          ( power-Commutative-Ring R
            ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
            ( y)))
      ( x)) ∙
    ( ( htpy-binomial-sum-Commutative-Ring R
        ( succ-ℕ n)
        ( λ i →
          ( right-swap-mul-Commutative-Ring R
            ( power-Commutative-Ring R
              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
              ( x))
            ( power-Commutative-Ring R
              ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
              ( y))
            ( x)) ∙
          ( ap
            ( mul-Commutative-Ring' R
              ( power-Commutative-Ring R
                ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
                ( y)))
            ( inv
              ( power-succ-Commutative-Ring R
                ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                ( x)))))) ∙
      ( ( ap
          ( add-Commutative-Ring R _)
          ( ( ap-mul-nat-Commutative-Ring R
              ( is-one-on-diagonal-binomial-coefficient-ℕ (succ-ℕ n))
              ( ap
                ( λ t →
                  mul-Commutative-Ring R
                    ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)
                    ( power-Commutative-Ring R t y))
                ( dist-eq-ℕ' (succ-ℕ n)))) ∙
            ( ( mul-nat-one-Commutative-Ring R
                ( mul-Commutative-Ring R
                  ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)
                  ( one-Commutative-Ring R))) ∙
              ( right-unit-law-mul-Commutative-Ring R
                ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x))))) ∙
        ( commutative-add-Commutative-Ring R
          ( sum-Commutative-Ring R
            ( succ-ℕ n)
            ( λ i →
              mul-nat-Commutative-Ring R
                ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
                ( mul-Commutative-Ring R
                  ( power-Commutative-Ring R
                    ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                    ( x))
                  ( power-Commutative-Ring R
                    ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                    ( y)))))
          ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x))))
```

### Computing a right summand that will appear in the proof of the binomial theorem

```agda
  right-summand-binomial-theorem-Commutative-Ring :
    (n : ℕ) (x y : type-Commutative-Ring R) →
    ( mul-Commutative-Ring R
      ( binomial-sum-Commutative-Ring R
        ( succ-ℕ n)
        ( λ i →
          mul-Commutative-Ring R
            ( power-Commutative-Ring R
              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
              ( x))
            ( power-Commutative-Ring R
              ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
              ( y))))
      ( y)) ＝
    ( add-Commutative-Ring R
      ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) y)
      ( sum-Commutative-Ring R
        ( succ-ℕ n)
        ( λ i →
          mul-nat-Commutative-Ring R
            ( binomial-coefficient-ℕ
              ( succ-ℕ n)
              ( succ-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
            ( mul-Commutative-Ring R
              ( power-Commutative-Ring R
                ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                ( x))
              ( power-Commutative-Ring R
                ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                ( y))))))
  right-summand-binomial-theorem-Commutative-Ring n x y =
    ( right-distributive-mul-binomial-sum-Commutative-Ring R
      ( succ-ℕ n)
      ( λ i →
        mul-Commutative-Ring R
          ( power-Commutative-Ring R
            ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
            ( x))
          ( power-Commutative-Ring R
            ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
            ( y)))
      ( y)) ∙
    ( ( htpy-binomial-sum-Commutative-Ring R
        ( succ-ℕ n)
        ( λ i →
          ( associative-mul-Commutative-Ring R
            ( power-Commutative-Ring R
              ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
              ( x))
            ( power-Commutative-Ring R
              ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
              ( y))
            ( y)) ∙
          ( ap
            ( mul-Commutative-Ring R
              ( power-Commutative-Ring R
                ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                ( x)))
            ( inv
              ( ap
                ( λ m → power-Commutative-Ring R m y)
                ( left-successor-law-dist-ℕ
                  ( succ-ℕ n)
                  ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                  ( upper-bound-nat-Fin (succ-ℕ n) i)) ∙
                ( power-succ-Commutative-Ring R
                  ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
                  ( y))))))) ∙
      ( ( snoc-sum-Commutative-Ring R
          ( succ-ℕ n)
          ( λ i →
            mul-nat-Commutative-Ring R
              ( binomial-coefficient-Fin (succ-ℕ n) i)
              ( mul-Commutative-Ring R
                ( power-Commutative-Ring R
                  ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                  ( x))
                ( power-Commutative-Ring R
                  ( dist-ℕ (succ-ℕ (succ-ℕ n)) (nat-Fin (succ-ℕ (succ-ℕ n)) i))
                  ( y))))
          ( ( ap
              ( λ m →
                mul-nat-Commutative-Ring R
                  ( binomial-coefficient-ℕ (succ-ℕ n) m)
                  ( mul-Commutative-Ring R
                    ( power-Commutative-Ring R m x)
                    ( power-Commutative-Ring R
                      ( dist-ℕ (succ-ℕ (succ-ℕ n)) m)
                      ( y))))
              ( is-zero-nat-zero-Fin {n})) ∙
            ( ( mul-nat-one-Commutative-Ring R
                ( mul-Commutative-Ring R
                  ( one-Commutative-Ring R)
                  ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) y))) ∙
              ( left-unit-law-mul-Commutative-Ring R
                ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) y))))) ∙
        ( ap-add-Commutative-Ring R
          ( refl)
          ( htpy-sum-Commutative-Ring R
            ( succ-ℕ n)
            ( λ i →
              ( ap
                ( λ m →
                  mul-nat-Commutative-Ring R
                    ( binomial-coefficient-ℕ (succ-ℕ n) m)
                    ( mul-Commutative-Ring R
                      ( power-Commutative-Ring R m x)
                      ( power-Commutative-Ring R
                        ( dist-ℕ (succ-ℕ (succ-ℕ n)) m)
                        ( y))))
                ( nat-inr-Fin (succ-ℕ n) i)))))))
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  (n : ℕ) (x y : type-Commutative-Ring R) →
  power-Commutative-Ring R n (add-Commutative-Ring R x y) ＝
  binomial-sum-Commutative-Ring R n
    ( λ i →
      mul-Commutative-Ring R
      ( power-Commutative-Ring R (nat-Fin (succ-ℕ n) i) x)
      ( power-Commutative-Ring R (dist-ℕ n (nat-Fin (succ-ℕ n) i)) y))
binomial-theorem-Commutative-Ring R zero-ℕ x y =
  inv
    ( ( sum-one-element-Commutative-Ring R
        ( λ i →
          mul-nat-Commutative-Ring R
            ( binomial-coefficient-Fin 0 i)
            ( mul-Commutative-Ring R
              ( power-Commutative-Ring R (nat-Fin 1 i) x)
              ( power-Commutative-Ring R (dist-ℕ 0 (nat-Fin 1 i)) y)))) ∙
      ( ( mul-nat-one-Commutative-Ring R
          ( mul-Commutative-Ring R
            ( one-Commutative-Ring R)
            ( one-Commutative-Ring R))) ∙
        ( left-unit-law-mul-Commutative-Ring R (one-Commutative-Ring R))))
binomial-theorem-Commutative-Ring R (succ-ℕ zero-ℕ) x y =
  ( commutative-add-Commutative-Ring R x y) ∙
  ( ( ap-binary
      ( add-Commutative-Ring R)
      ( ( inv (left-unit-law-mul-Commutative-Ring R y)) ∙
        ( inv
          ( mul-nat-one-Commutative-Ring R
            ( mul-Commutative-Ring R (one-Commutative-Ring R) y))))
      ( ( inv (right-unit-law-mul-Commutative-Ring R x)) ∙
        ( inv
          ( mul-nat-one-Commutative-Ring R
            ( mul-Commutative-Ring R x (one-Commutative-Ring R)))))) ∙
    ( inv
      ( sum-two-elements-Commutative-Ring R
        ( λ i →
          mul-nat-Commutative-Ring R
          ( binomial-coefficient-Fin 1 i)
          ( mul-Commutative-Ring R
            ( power-Commutative-Ring R (nat-Fin 2 i) x)
            ( power-Commutative-Ring R (dist-ℕ 1 (nat-Fin 2 i)) y))))))
binomial-theorem-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x y =
  ( ap
    ( λ r → mul-Commutative-Ring R r (add-Commutative-Ring R x y))
    ( binomial-theorem-Commutative-Ring R (succ-ℕ n) x y)) ∙
  ( ( left-distributive-mul-add-Commutative-Ring R _ x y) ∙
    ( ( ap-add-Commutative-Ring R
        ( left-summand-binomial-theorem-Commutative-Ring R n x y)
        ( right-summand-binomial-theorem-Commutative-Ring R n x y)) ∙
      ( ( interchange-add-add-Commutative-Ring R
          ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)
          ( sum-Commutative-Ring R
            ( succ-ℕ n)
            ( λ i →
              mul-nat-Commutative-Ring R
              ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
              ( mul-Commutative-Ring R
                ( power-Commutative-Ring R
                  ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                  ( x))
                ( power-Commutative-Ring R
                  ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                  ( y)))))
          ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) y)
          ( sum-Commutative-Ring R
            ( succ-ℕ n)
            ( λ i →
              mul-nat-Commutative-Ring R
              ( binomial-coefficient-ℕ
                ( succ-ℕ n)
                ( succ-ℕ (nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
              ( mul-Commutative-Ring R
                ( power-Commutative-Ring R
                  ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                  ( x))
                ( power-Commutative-Ring R
                  ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                  ( y)))))) ∙
        ( ( ap-add-Commutative-Ring R
            ( commutative-add-Commutative-Ring R
              ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)
              ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) y))
            ( ( interchange-add-sum-Commutative-Ring R
                ( succ-ℕ n)
                ( λ i →
                  mul-nat-Commutative-Ring R
                  ( binomial-coefficient-Fin (succ-ℕ n) (inl-Fin (succ-ℕ n) i))
                  ( mul-Commutative-Ring R
                    ( power-Commutative-Ring R
                      ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                      ( x))
                    ( power-Commutative-Ring R
                      ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                      ( y))))
                ( λ i →
                  mul-nat-Commutative-Ring R
                  ( binomial-coefficient-ℕ
                    ( succ-ℕ n)
                    ( succ-ℕ
                      ( nat-Fin (succ-ℕ (succ-ℕ n)) (inl-Fin (succ-ℕ n) i))))
                    ( mul-Commutative-Ring R
                      ( power-Commutative-Ring R
                        ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                        ( x))
                      ( power-Commutative-Ring R
                        ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                        ( y))))) ∙
              ( htpy-sum-Commutative-Ring R
                ( succ-ℕ n)
                ( λ i →
                  ( inv
                    ( right-distributive-mul-nat-add-Commutative-Ring R
                      ( binomial-coefficient-ℕ
                        ( succ-ℕ n)
                        ( nat-Fin (succ-ℕ n) i))
                      ( binomial-coefficient-ℕ
                        ( succ-ℕ n)
                        ( succ-ℕ (nat-Fin (succ-ℕ n) i)))
                      ( mul-Commutative-Ring R
                        ( power-Commutative-Ring R
                          ( succ-ℕ (nat-Fin (succ-ℕ n) i))
                          ( x))
                        ( power-Commutative-Ring R
                          ( dist-ℕ (succ-ℕ n) (nat-Fin (succ-ℕ n) i))
                          ( y))))) ∙
                  ( ap
                    ( λ m →
                      mul-nat-Commutative-Ring R
                        ( binomial-coefficient-ℕ (succ-ℕ (succ-ℕ n)) m)
                        ( mul-Commutative-Ring R
                          ( power-Commutative-Ring R m x)
                          ( power-Commutative-Ring R
                            ( dist-ℕ (succ-ℕ (succ-ℕ n)) m)
                            ( y))))
                    ( inv (nat-inr-Fin (succ-ℕ n) i))))))) ∙
          ( ( right-swap-add-Commutative-Ring R
              ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) y)
              ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)
              ( _)) ∙
            ( ( ap
                ( add-Commutative-Ring' R
                  ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x))
                ( inv
                  ( snoc-sum-Commutative-Ring R
                    ( succ-ℕ n)
                    ( λ i →
                      mul-nat-Commutative-Ring R
                        ( binomial-coefficient-ℕ
                          ( succ-ℕ (succ-ℕ n))
                          ( nat-Fin (succ-ℕ (succ-ℕ n)) i))
                        ( mul-Commutative-Ring R
                          ( power-Commutative-Ring R
                            ( nat-Fin (succ-ℕ (succ-ℕ n)) i)
                            ( x))
                          ( power-Commutative-Ring R
                            ( dist-ℕ
                              ( succ-ℕ (succ-ℕ n))
                              ( nat-Fin (succ-ℕ (succ-ℕ n)) i))
                            ( y))))
                    ( ( ap
                        ( λ m →
                          mul-nat-Commutative-Ring R
                            ( binomial-coefficient-ℕ (succ-ℕ (succ-ℕ n)) m)
                            ( mul-Commutative-Ring R
                              ( power-Commutative-Ring R m x)
                              ( power-Commutative-Ring R
                                ( dist-ℕ (succ-ℕ (succ-ℕ n)) m)
                                ( y))))
                        ( is-zero-nat-zero-Fin {n})) ∙
                      ( ( mul-nat-one-Commutative-Ring R
                          ( mul-Commutative-Ring R
                            ( one-Commutative-Ring R)
                            ( power-Commutative-Ring R
                              ( succ-ℕ (succ-ℕ n))
                              ( y)))) ∙
                        ( left-unit-law-mul-Commutative-Ring R
                          ( power-Commutative-Ring R
                            ( succ-ℕ (succ-ℕ n))
                            ( y)))))))) ∙
              ( inv
                ( cons-sum-Commutative-Ring R
                  ( succ-ℕ (succ-ℕ n))
                  ( λ i →
                    mul-nat-Commutative-Ring R
                      ( binomial-coefficient-Fin (succ-ℕ (succ-ℕ n)) i)
                      ( mul-Commutative-Ring R
                        ( power-Commutative-Ring R
                          ( nat-Fin (succ-ℕ (succ-ℕ (succ-ℕ n))) i)
                          ( x))
                        ( power-Commutative-Ring R
                          ( dist-ℕ
                            ( succ-ℕ (succ-ℕ n))
                            ( nat-Fin (succ-ℕ (succ-ℕ (succ-ℕ n))) i)) y)))
                  ( ( ap-mul-nat-Commutative-Ring R
                      ( is-one-on-diagonal-binomial-coefficient-ℕ
                        ( succ-ℕ (succ-ℕ n)))
                      ( ( ap
                          ( mul-Commutative-Ring R
                            ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x))
                          ( ap
                            ( λ m → power-Commutative-Ring R m y)
                            ( dist-eq-ℕ' (succ-ℕ (succ-ℕ n))))) ∙
                        ( right-unit-law-mul-Commutative-Ring R
                          ( power-Commutative-Ring R (succ-ℕ (succ-ℕ n)) x)))) ∙
                    ( mul-nat-one-Commutative-Ring R
                      ( power-Commutative-Ring R
                        ( succ-ℕ (succ-ℕ n))
                        ( x))))))))))))
```


