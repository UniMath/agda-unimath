# Nilpotent elements in semirings

```agda
module ring-theory.nilpotent-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.binomial-theorem-semirings
open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.sums-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A nilpotent element in a semiring is an element `x` for which there is a natural
number `n` such that `x^n = 0`.

## Definition

```agda
is-nilpotent-element-semiring-Prop :
  {l : Level} (R : Semiring l) → type-Semiring R → Prop l
is-nilpotent-element-semiring-Prop R x =
  ∃-Prop ℕ (λ n → power-Semiring R n x ＝ zero-Semiring R)

is-nilpotent-element-Semiring :
  {l : Level} (R : Semiring l) → type-Semiring R → UU l
is-nilpotent-element-Semiring R x =
  type-Prop (is-nilpotent-element-semiring-Prop R x)

is-prop-is-nilpotent-element-Semiring :
  {l : Level} (R : Semiring l) (x : type-Semiring R) →
  is-prop (is-nilpotent-element-Semiring R x)
is-prop-is-nilpotent-element-Semiring R x =
  is-prop-type-Prop (is-nilpotent-element-semiring-Prop R x)
```

## Properties

### Zero is nilpotent

```agda
is-nilpotent-zero-Semiring :
  {l : Level} (R : Semiring l) →
  is-nilpotent-element-Semiring R (zero-Semiring R)
is-nilpotent-zero-Semiring R = intro-∃ 1 refl
```

### If `x` and `y` commute and are both nilpotent, then `x + y` is nilpotent

```agda
is-nilpotent-add-Semiring :
  {l : Level} (R : Semiring l) →
  (x y : type-Semiring R) → (mul-Semiring R x y ＝ mul-Semiring R y x) →
  is-nilpotent-element-Semiring R x → is-nilpotent-element-Semiring R y →
  is-nilpotent-element-Semiring R (add-Semiring R x y)
is-nilpotent-add-Semiring R x y H f h =
  apply-universal-property-trunc-Prop f
    ( is-nilpotent-element-semiring-Prop R (add-Semiring R x y))
    ( λ (n , p) →
      apply-universal-property-trunc-Prop h
        ( is-nilpotent-element-semiring-Prop R (add-Semiring R x y))
        ( λ (m , q) →
          intro-∃
            ( add-ℕ n m)
            ( ( binomial-theorem-Semiring R (add-ℕ n m) x y H) ∙
              ( ( split-sum-Semiring R n
                  ( succ-ℕ m)
                  ( λ i →
                    mul-nat-scalar-Semiring R
                      ( binomial-coefficient-ℕ
                        ( add-ℕ n m)
                        ( nat-Fin (add-ℕ n (succ-ℕ m)) i))
                      ( mul-Semiring R
                        ( power-Semiring R
                          ( nat-Fin (add-ℕ n (succ-ℕ m)) i)
                          ( x))
                        ( power-Semiring R
                          ( dist-ℕ
                            ( add-ℕ n m)
                            ( nat-Fin (add-ℕ n (succ-ℕ m)) i))
                          ( y))))) ∙
                ( ( ap-add-Semiring R
                    ( ( htpy-sum-Semiring R n
                        ( λ i →
                          ( ap
                            ( λ u →
                              mul-nat-scalar-Semiring R
                                ( binomial-coefficient-ℕ (add-ℕ n m) u)
                                ( mul-Semiring R
                                  ( power-Semiring R u x)
                                  ( power-Semiring R
                                    ( dist-ℕ (add-ℕ n m) u)
                                    ( y))))
                            ( nat-inl-coprod-Fin n m i)) ∙
                          ( ( ( ap
                                ( mul-nat-scalar-Semiring R
                                  ( binomial-coefficient-ℕ
                                    ( add-ℕ n m)
                                    ( nat-Fin n i)))
                                ( ( ap
                                    ( mul-Semiring R
                                      ( power-Semiring R
                                        ( nat-Fin n i)
                                        ( x)))
                                    ( ( ap
                                        ( λ u → power-Semiring R u y)
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
                                      ( ( power-add-Semiring R
                                          ( dist-ℕ (nat-Fin n i) n)
                                          ( m)) ∙
                                        ( ( ap
                                            ( mul-Semiring R
                                              ( power-Semiring R
                                                ( dist-ℕ (nat-Fin n i) n)
                                                ( y)))
                                            ( q)) ∙
                                          ( right-zero-law-mul-Semiring
                                            ( R)
                                            ( power-Semiring R
                                              ( dist-ℕ (nat-Fin n i) n)
                                              ( y))))))) ∙
                                  ( right-zero-law-mul-Semiring R
                                    ( power-Semiring R
                                      ( nat-Fin n i)
                                      ( x)))))) ∙
                            ( right-zero-law-mul-nat-scalar-Semiring R
                              ( binomial-coefficient-ℕ
                                ( add-ℕ n m)
                                ( nat-Fin n i)))))) ∙
                      ( sum-zero-Semiring R n))
                    ( ( htpy-sum-Semiring R (succ-ℕ m)
                        ( λ i →
                          ( ap
                            ( λ u →
                              mul-nat-scalar-Semiring R
                                ( binomial-coefficient-ℕ (add-ℕ n m) u)
                                ( mul-Semiring R
                                  ( power-Semiring R u x)
                                  ( power-Semiring R
                                    ( dist-ℕ (add-ℕ n m) u)
                                    ( y))))
                            ( nat-inr-coprod-Fin n (succ-ℕ m) i)) ∙
                          ( ( ap
                              ( mul-nat-scalar-Semiring R
                                ( binomial-coefficient-ℕ
                                  ( add-ℕ n m)
                                  ( add-ℕ n (nat-Fin (succ-ℕ m) i))))
                              ( ( ap
                                  ( mul-Semiring' R
                                    ( power-Semiring R
                                      ( dist-ℕ
                                        ( add-ℕ n m)
                                        ( add-ℕ n (nat-Fin (succ-ℕ m) i)))
                                      ( y)))
                                  ( ( power-add-Semiring R n
                                      ( nat-Fin (succ-ℕ m) i)) ∙
                                    ( ( ap (mul-Semiring' R _) p) ∙
                                      ( left-zero-law-mul-Semiring R
                                        ( power-Semiring R
                                          ( nat-Fin (succ-ℕ m) i)
                                          ( x)))))) ∙
                                ( left-zero-law-mul-Semiring R _))) ∙
                            ( right-zero-law-mul-nat-scalar-Semiring R
                              ( binomial-coefficient-ℕ
                                ( add-ℕ n m)
                                ( add-ℕ n (nat-Fin (succ-ℕ m) i))))))) ∙
                      ( sum-zero-Semiring R (succ-ℕ m)))) ∙
                  ( left-unit-law-add-Semiring R
                    ( zero-Semiring R)))))))
```

### If `x` is nilpotent and `y` commutes with `x`, then `xy` is also nilpotent

```agda
module _
  {l : Level} (R : Semiring l)
  where
  
  is-nilpotent-element-mul-Semiring :
    (x y : type-Semiring R) →
    mul-Semiring R x y ＝ mul-Semiring R y x →
    is-nilpotent-element-Semiring R x → 
    is-nilpotent-element-Semiring R (mul-Semiring R x y)
  is-nilpotent-element-mul-Semiring x y H f =
    apply-universal-property-trunc-Prop f
      ( is-nilpotent-element-semiring-Prop R (mul-Semiring R x y))
      ( λ (n , p) →
        intro-∃ n
          ( ( distributive-power-mul-Semiring R n H) ∙
            ( ( ap (mul-Semiring' R (power-Semiring R n y)) p) ∙
              ( left-zero-law-mul-Semiring R
                ( power-Semiring R n y)))))

  is-nilpotent-element-mul-Semiring' :
    (x y : type-Semiring R) →
    mul-Semiring R x y ＝ mul-Semiring R y x →
    is-nilpotent-element-Semiring R x →
    is-nilpotent-element-Semiring R (mul-Semiring R y x)
  is-nilpotent-element-mul-Semiring' x y H f =
    is-closed-under-eq-subtype
      ( is-nilpotent-element-semiring-Prop R)
      ( is-nilpotent-element-mul-Semiring x y H f)
      ( H)
```
