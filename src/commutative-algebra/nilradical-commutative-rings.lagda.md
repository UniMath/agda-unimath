# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The nilradical of a commutative ring is the ideal consisting of all nilpotent
elements.

## Definitions

```agda
subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → subset-Commutative-Ring l R
subset-nilradical-Commutative-Ring R =
  is-nilpotent-element-ring-Prop (ring-Commutative-Ring R)
```

## Properties

### The nilradical is the intersection of all prime ideals

```agda
contains-zero-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  contains-zero-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
contains-zero-nilradical-Commutative-Ring R = intro-∃ 1 refl
```

### The nilradical is closed under addition

```agda
is-closed-under-add-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-closed-under-add-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
is-closed-under-add-nilradical-Commutative-Ring R x y f h =
  apply-universal-property-trunc-Prop f
    ( subset-nilradical-Commutative-Ring R (add-Commutative-Ring R x y))
    ( λ (n , p) →
      apply-universal-property-trunc-Prop h
        ( subset-nilradical-Commutative-Ring R (add-Commutative-Ring R x y))
        ( λ (m , q) →
          intro-∃
            ( add-ℕ n m)
            ( ( binomial-theorem-Commutative-Ring R (add-ℕ n m) x y) ∙
              ( ( split-sum-Commutative-Ring R n
                  ( succ-ℕ m)
                  ( λ i →
                    mul-nat-scalar-Commutative-Ring R
                      ( binomial-coefficient-ℕ
                        ( add-ℕ n m)
                        ( nat-Fin (add-ℕ n (succ-ℕ m)) i))
                      ( mul-Commutative-Ring R
                        ( power-Commutative-Ring R
                          ( nat-Fin (add-ℕ n (succ-ℕ m)) i)
                          ( x))
                        ( power-Commutative-Ring R
                          ( dist-ℕ
                            ( add-ℕ n m)
                            ( nat-Fin (add-ℕ n (succ-ℕ m)) i))
                          ( y))))) ∙
                ( ( ap-add-Commutative-Ring R
                    ( ( htpy-sum-Commutative-Ring R n
                        ( λ i →
                          ( ap
                            ( λ u →
                              mul-nat-scalar-Commutative-Ring R
                                ( binomial-coefficient-ℕ (add-ℕ n m) u)
                                ( mul-Commutative-Ring R
                                  ( power-Commutative-Ring R u x)
                                  ( power-Commutative-Ring R
                                    ( dist-ℕ (add-ℕ n m) u)
                                    ( y))))
                            ( nat-inl-coprod-Fin n m i)) ∙
                          ( ( ( ap
                                ( mul-nat-scalar-Commutative-Ring R
                                  ( binomial-coefficient-ℕ
                                    ( add-ℕ n m)
                                    ( nat-Fin n i)))
                                ( ( ap
                                    ( mul-Commutative-Ring R
                                      ( power-Commutative-Ring R
                                        ( nat-Fin n i)
                                        ( x)))
                                    ( ( ap
                                        ( λ u → power-Commutative-Ring R u y)
                                        ( ( symmetric-dist-ℕ
                                            ( add-ℕ n m)
                                            ( nat-Fin n i)) ∙
                                          ( ( inv
                                              ( triangle-equality-dist-ℕ
                                                ( nat-Fin n i)
                                                ( n)
                                                ( add-ℕ n m)
                                                ( upper-bound-nat-Fin' n i)
                                                ( leq-add-ℕ n m))) ∙
                                            ( ap
                                              ( add-ℕ (dist-ℕ (nat-Fin n i) n))
                                              ( dist-add-ℕ n m))))) ∙
                                      ( ( power-add-Commutative-Ring R
                                          ( dist-ℕ (nat-Fin n i) n)
                                          ( m)) ∙
                                        ( ( ap
                                            ( mul-Commutative-Ring R
                                              ( power-Commutative-Ring R
                                                ( dist-ℕ (nat-Fin n i) n)
                                                ( y)))
                                            ( q)) ∙
                                          ( right-zero-law-mul-Commutative-Ring
                                            ( R)
                                            ( power-Commutative-Ring R
                                              ( dist-ℕ (nat-Fin n i) n)
                                              ( y))))))) ∙
                                  ( right-zero-law-mul-Commutative-Ring R
                                    ( power-Commutative-Ring R
                                      ( nat-Fin n i)
                                      ( x)))))) ∙
                            ( right-zero-law-mul-nat-scalar-Commutative-Ring R
                              ( binomial-coefficient-ℕ
                                ( add-ℕ n m)
                                ( nat-Fin n i)))))) ∙
                      ( sum-zero-Commutative-Ring R n))
                    ( ( htpy-sum-Commutative-Ring R (succ-ℕ m)
                        ( λ i →
                          ( ap
                            ( λ u →
                              mul-nat-scalar-Commutative-Ring R
                                ( binomial-coefficient-ℕ (add-ℕ n m) u)
                                ( mul-Commutative-Ring R
                                  ( power-Commutative-Ring R u x)
                                  ( power-Commutative-Ring R
                                    ( dist-ℕ (add-ℕ n m) u)
                                    ( y))))
                            ( nat-inr-coprod-Fin n (succ-ℕ m) i)) ∙
                          ( ( ap
                              ( mul-nat-scalar-Commutative-Ring R
                                ( binomial-coefficient-ℕ
                                  ( add-ℕ n m)
                                  ( add-ℕ n (nat-Fin (succ-ℕ m) i))))
                              ( ( ap
                                  ( mul-Commutative-Ring' R
                                    ( power-Commutative-Ring R
                                      ( dist-ℕ
                                        ( add-ℕ n m)
                                        ( add-ℕ n (nat-Fin (succ-ℕ m) i)))
                                      ( y)))
                                  ( ( power-add-Commutative-Ring R n
                                      ( nat-Fin (succ-ℕ m) i)) ∙
                                    ( ( ap (mul-Commutative-Ring' R _) p) ∙
                                      ( left-zero-law-mul-Commutative-Ring R
                                        ( power-Commutative-Ring R
                                          ( nat-Fin (succ-ℕ m) i)
                                          ( x)))))) ∙
                                ( left-zero-law-mul-Commutative-Ring R _))) ∙
                            ( right-zero-law-mul-nat-scalar-Commutative-Ring R
                              ( binomial-coefficient-ℕ
                                ( add-ℕ n m)
                                ( add-ℕ n (nat-Fin (succ-ℕ m) i))))))) ∙
                      ( sum-zero-Commutative-Ring R (succ-ℕ m)))) ∙
                  ( left-unit-law-add-Commutative-Ring R
                    ( zero-Commutative-Ring R)))))))
```

### The nilradical is closed under negatives

```agda
is-closed-under-neg-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-closed-under-neg-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
is-closed-under-neg-nilradical-Commutative-Ring R x H =
  apply-universal-property-trunc-Prop H
    ( subset-nilradical-Commutative-Ring R (neg-Commutative-Ring R x))
    ( λ (n , p) →
      intro-∃ n
        ( ( ap
            ( power-Commutative-Ring R n)
            ( inv (mul-neg-one-Commutative-Ring R x))) ∙
          ( ( distributive-power-mul-Commutative-Ring R n
              ( neg-one-Commutative-Ring R)
              ( x)) ∙
            ( ( ap
                ( mul-Commutative-Ring R
                  ( power-Commutative-Ring R n
                    ( neg-one-Commutative-Ring R)))
                ( p)) ∙
              ( right-zero-law-mul-Commutative-Ring R
                ( power-Commutative-Ring R n (neg-one-Commutative-Ring R)))))))
```

### The nilradical is closed under multiplication with ring elements

```agda
is-closed-under-mul-right-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-closed-under-mul-right-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
is-closed-under-mul-right-nilradical-Commutative-Ring R x y f =
  apply-universal-property-trunc-Prop f
    ( subset-nilradical-Commutative-Ring R (mul-Commutative-Ring R x y))
    ( λ (n , p) →
      intro-∃ n
        ( ( distributive-power-mul-Commutative-Ring R n x y) ∙
          ( ( ap (mul-Commutative-Ring' R (power-Commutative-Ring R n y)) p) ∙
            ( left-zero-law-mul-Commutative-Ring R
              ( power-Commutative-Ring R n y)))))
```

### The nilradical ideal

```agda
nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → ideal-Commutative-Ring l R
nilradical-Commutative-Ring R =
  ideal-right-ideal-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
    ( contains-zero-nilradical-Commutative-Ring R)
    ( is-closed-under-add-nilradical-Commutative-Ring R)
    ( is-closed-under-neg-nilradical-Commutative-Ring R)
    ( is-closed-under-mul-right-nilradical-Commutative-Ring R)

is-closed-under-mul-left-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-closed-under-mul-left-subset-Commutative-Ring R
    ( subset-nilradical-Commutative-Ring R)
is-closed-under-mul-left-nilradical-Commutative-Ring R =
  is-closed-under-mul-left-ideal-Commutative-Ring R
    ( nilradical-Commutative-Ring R)
```
