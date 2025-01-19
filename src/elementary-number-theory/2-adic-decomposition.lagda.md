# 2-Adic decomposition

```agda
module elementary-number-theory.2-adic-decomposition where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-strong-induction-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.largest-power-divisors-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositions
open import foundation.split-surjective-maps
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Idea

The {{#concept "2-adic decomposition" Agda=2-adic-decomposition-ℕ}} of a [natural number](elementary-number-theory.natural-numbers.md) $n$ is a factorization of $n$ into a [power](elementary-number-theory.exponentiation-natural-numbers.md) of $2$ and an [odd](elementary-number-theory.parity-natural-numbers.md) natural number.

The $2$-adic decomposition of the natural numbers can be used to construct an [equivalence](foundation-core.equivalences.md) $\mathbb{N}\times\mathbb{N} \simeq \mathbb{N}$ by mapping

$$
  (m , n) \mapsto 2^m(2n + 1) - 1.
$$

The exponent $k$ such that the 2-adic decomposition of $n$ is $2^k \cdot m=n$ is called the {{#concept "2-adic valuation" Disambiguation="natural numbers" Agda=valuation-2-adic-decomposition-ℕ}} of $n$.

## Definitions

### The $2$-adic composition function

```agda
2-adic-composition-ℕ : ℕ → ℕ → ℕ
2-adic-composition-ℕ k l = 2 ^ℕ k *ℕ odd-number-ℕ l
```

### The type of $2$-adic decompositions of a natural number

```agda
2-adic-decomposition-ℕ : ℕ → UU lzero
2-adic-decomposition-ℕ n =
  Σ ℕ (λ k → Σ ℕ (λ l → 2-adic-composition-ℕ k l ＝ n))

module _
  (n : ℕ) (d : 2-adic-decomposition-ℕ n)
  where

  valuation-2-adic-decomposition-ℕ : ℕ
  valuation-2-adic-decomposition-ℕ = pr1 d

  index-odd-factor-2-adic-decomposition-ℕ : ℕ
  index-odd-factor-2-adic-decomposition-ℕ = pr1 (pr2 d)

  odd-factor-2-adic-decomposition-ℕ : ℕ
  odd-factor-2-adic-decomposition-ℕ =
    odd-number-ℕ index-odd-factor-2-adic-decomposition-ℕ

  eq-2-adic-decomposition-ℕ :
    2-adic-composition-ℕ
      valuation-2-adic-decomposition-ℕ
      index-odd-factor-2-adic-decomposition-ℕ ＝
    n
  eq-2-adic-decomposition-ℕ = pr2 (pr2 d)
```

## Properties

### The values of the $2$-adic composition function are nonzero

```agda
is-nonzero-2-adic-composition-ℕ :
  (k l : ℕ) → is-nonzero-ℕ (2-adic-composition-ℕ k l)
is-nonzero-2-adic-composition-ℕ k l =
  is-nonzero-mul-ℕ
    ( 2 ^ℕ k)
    ( odd-number-ℕ l)
    ( is-nonzero-exp-ℕ 2 k is-nonzero-two-ℕ)
    ( is-nonzero-odd-number-ℕ l)
```

### Any number that has a $2$-adic decomposition is nonzero

```agda
is-nonzero-2-adic-decomposition-ℕ :
  (n : ℕ) → 2-adic-decomposition-ℕ n → is-nonzero-ℕ n
is-nonzero-2-adic-decomposition-ℕ ._ (k , l , refl) =
  is-nonzero-2-adic-composition-ℕ k l
```

### Every odd number has a $2$-adic decomposition

```agda
2-adic-decomposition-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → 2-adic-decomposition-ℕ n
pr1 (2-adic-decomposition-is-odd-ℕ n H) =
  0
pr1 (pr2 (2-adic-decomposition-is-odd-ℕ n H)) =
  pr1 (has-odd-expansion-is-odd-ℕ n H)
pr2 (pr2 (2-adic-decomposition-is-odd-ℕ n H)) =
  left-unit-law-mul-ℕ _ ∙ pr2 (has-odd-expansion-is-odd-ℕ n H)
```

### Every nonzero natural number has a $2$-adic decomposition

```agda
module _
  (n : ℕ) (H : 1 ≤-ℕ n)
  where
  
  valuation-2-adic-decomposition-nat-ℕ :
    ℕ
  valuation-2-adic-decomposition-nat-ℕ =
    valuation-largest-power-divisor-ℕ 2 n star H
  
  div-exp-valuation-2-adic-decomposition-nat-ℕ :
    div-ℕ (2 ^ℕ valuation-2-adic-decomposition-nat-ℕ) n
  div-exp-valuation-2-adic-decomposition-nat-ℕ =
    div-exp-valuation-largest-power-divisor-ℕ 2 n star H

  is-upper-bound-valuation-2-adic-decomposition-nat-ℕ :
    (k : ℕ) → div-ℕ (2 ^ℕ k) n → k ≤-ℕ valuation-2-adic-decomposition-nat-ℕ
  is-upper-bound-valuation-2-adic-decomposition-nat-ℕ =
    is-upper-bound-valuation-largest-power-divisor-ℕ 2 n star H

  odd-factor-2-adic-decomposition-nat-ℕ :
    ℕ
  odd-factor-2-adic-decomposition-nat-ℕ =
    quotient-div-ℕ
      ( 2 ^ℕ valuation-2-adic-decomposition-nat-ℕ)
      ( n)
      ( div-exp-valuation-2-adic-decomposition-nat-ℕ)

  is-odd-odd-factor-2-adic-decomposition-nat-ℕ :
    is-odd-ℕ odd-factor-2-adic-decomposition-nat-ℕ
  is-odd-odd-factor-2-adic-decomposition-nat-ℕ K =
    neg-succ-leq-ℕ
      ( valuation-2-adic-decomposition-nat-ℕ)
      ( is-upper-bound-valuation-2-adic-decomposition-nat-ℕ
        ( succ-ℕ valuation-2-adic-decomposition-nat-ℕ)
        ( tr
          ( is-divisor-ℕ n)
          ( inv (exp-succ-ℕ 2 valuation-2-adic-decomposition-nat-ℕ))
          ( div-div-quotient-div-ℕ 2 n
            ( 2 ^ℕ valuation-2-adic-decomposition-nat-ℕ)
            ( div-exp-valuation-2-adic-decomposition-nat-ℕ)
            ( K))))

  has-odd-expansion-odd-factor-2-adic-decomposition-nat-ℕ :
    has-odd-expansion-ℕ odd-factor-2-adic-decomposition-nat-ℕ
  has-odd-expansion-odd-factor-2-adic-decomposition-nat-ℕ =
    has-odd-expansion-is-odd-ℕ
      odd-factor-2-adic-decomposition-nat-ℕ
      is-odd-odd-factor-2-adic-decomposition-nat-ℕ

  index-odd-factor-2-adic-decomposition-nat-ℕ :
    ℕ
  index-odd-factor-2-adic-decomposition-nat-ℕ =
    pr1 has-odd-expansion-odd-factor-2-adic-decomposition-nat-ℕ

  eq-index-odd-factor-2-adic-decomposition-nat-ℕ :
    odd-number-ℕ index-odd-factor-2-adic-decomposition-nat-ℕ ＝
    odd-factor-2-adic-decomposition-nat-ℕ
  eq-index-odd-factor-2-adic-decomposition-nat-ℕ =
    pr2 has-odd-expansion-odd-factor-2-adic-decomposition-nat-ℕ

  eq-2-adic-decomposition-nat-ℕ :
    2-adic-composition-ℕ
      ( valuation-2-adic-decomposition-nat-ℕ)
      ( index-odd-factor-2-adic-decomposition-nat-ℕ) ＝
    n
  eq-2-adic-decomposition-nat-ℕ =
    ( ap
      ( 2 ^ℕ valuation-2-adic-decomposition-nat-ℕ *ℕ_)
      ( eq-index-odd-factor-2-adic-decomposition-nat-ℕ)) ∙
    ( eq-quotient-div-ℕ'
      ( 2 ^ℕ valuation-2-adic-decomposition-nat-ℕ)
      ( n)
      ( div-exp-valuation-2-adic-decomposition-nat-ℕ))

  2-adic-decomposition-nat-ℕ :
    2-adic-decomposition-ℕ n
  pr1 2-adic-decomposition-nat-ℕ =
    valuation-2-adic-decomposition-nat-ℕ
  pr1 (pr2 2-adic-decomposition-nat-ℕ) =
    index-odd-factor-2-adic-decomposition-nat-ℕ
  pr2 (pr2 2-adic-decomposition-nat-ℕ) =
    eq-2-adic-decomposition-nat-ℕ
```

### If $2^km$ is a $2$-adic decomposition of a number $n$, then $2^k$ is the largest power divisor of $n$ base $2$

```agda
largest-power-divisor-2-adic-decomposition-ℕ :
  (n : ℕ) → 2-adic-decomposition-ℕ n → {!!}
largest-power-divisor-2-adic-decomposition-ℕ = {!!}
```

### The type of 2-adic decompositions of any natural number is a proposition

```agda
all-elements-equal-2-adic-decomposition-ℕ :
  (n : ℕ) → all-elements-equal (2-adic-decomposition-ℕ n)
all-elements-equal-2-adic-decomposition-ℕ n (k , m , p) (k' , m' , p') = {!!}
```

```text
pair-expansion : ℕ → UU lzero
pair-expansion n =
  Σ (ℕ × ℕ)
    ( λ p →
      ( (exp-ℕ 2 (pr1 p)) *ℕ (succ-ℕ ((pr2 p) *ℕ 2))) ＝
        succ-ℕ n)

is-nonzero-pair-expansion :
  (u v : ℕ) →
  is-nonzero-ℕ ((exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2)))
is-nonzero-pair-expansion u v =
  is-nonzero-mul-ℕ _ _
    ( is-nonzero-exp-ℕ 2 u is-nonzero-two-ℕ)
    ( is-nonzero-succ-ℕ _)

abstract
  has-pair-expansion-is-even-or-odd :
    (n : ℕ) → is-even-ℕ n + is-odd-ℕ n → pair-expansion n
  has-pair-expansion-is-even-or-odd n =
    strong-ind-ℕ
    ( λ m → (is-even-ℕ m + is-odd-ℕ m) → (pair-expansion m))
    ( λ x → (0 , 0) , refl)
    ( λ k f →
      ( λ where
        ( inl x) →
          ( let s = has-odd-expansion-is-odd-ℕ k (is-odd-is-even-succ-ℕ k x)
            in
            ( ( 0 , succ-ℕ (pr1 s)) ,
              ( ap
                ( succ-ℕ ∘ succ-ℕ)
                ( left-unit-law-add-ℕ _ ∙
                  ap succ-ℕ (commutative-mul-ℕ (pr1 s) 2) ∙
                  pr2 s))))
        ( inr x) →
          ( let
            e : is-even-ℕ k
            e = is-even-is-odd-succ-ℕ k x

            t : quotient-div-ℕ 2 k e ≤-ℕ k
            t = upper-bound-quotient-div-ℕ 2 k e

            s : (pair-expansion (quotient-div-ℕ 2 k e))
            s =
              f (quotient-div-ℕ 2 k e)
                ( t)
                ( is-decidable-is-even-ℕ (quotient-div-ℕ 2 k e))
            in
            pair
              ( succ-ℕ (pr1 (pr1 s)) , pr2 (pr1 s))
              ( ( ap
                  ( _*ℕ (succ-ℕ ((pr2 (pr1 s)) *ℕ 2)))
                  ( commutative-mul-ℕ (exp-ℕ 2 (pr1 (pr1 s))) 2)) ∙
                ( ( associative-mul-ℕ
                    ( 2)
                    ( exp-ℕ 2 (pr1 (pr1 s)))
                    ( succ-ℕ ((pr2 (pr1 s)) *ℕ 2))) ∙
                  ( ( ap (2 *ℕ_) (pr2 s)) ∙
                    ( ( ap
                        ( succ-ℕ)
                        ( ( left-successor-law-add-ℕ
                            ( 0 +ℕ quotient-div-ℕ 2 k e)
                            ( quotient-div-ℕ 2 k e)))) ∙
                      ( ( ap
                          ( succ-ℕ ∘ succ-ℕ)
                          ( ap
                            ( _+ℕ quotient-div-ℕ 2 k e)
                            ( left-unit-law-add-ℕ (quotient-div-ℕ 2 k e)))) ∙
                        ( ( ap
                            ( succ-ℕ ∘ succ-ℕ)
                            ( inv
                              ( right-two-law-mul-ℕ
                                ( quotient-div-ℕ 2 k e)))) ∙
                          ( ap
                            ( succ-ℕ ∘ succ-ℕ)
                            ( eq-quotient-div-ℕ 2 k e)))))))))))
    ( n)

has-pair-expansion : (n : ℕ) → pair-expansion n
has-pair-expansion n =
  has-pair-expansion-is-even-or-odd n (is-decidable-is-even-ℕ n)
```

### If `(u , v)` and `(u' , v')` are the pairs corresponding the same number `x`, then `u ＝ u'` and `v ＝ v'`

```text
is-pair-expansion-unique :
  (u u' v v' : ℕ) →
  ((exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2))) ＝
    ((exp-ℕ 2 u') *ℕ (succ-ℕ (v' *ℕ 2))) →
  (u ＝ u') × (v ＝ v')
is-pair-expansion-unique zero-ℕ zero-ℕ v v' p =
  ( pair refl
    ( is-injective-right-mul-ℕ 2 is-nonzero-two-ℕ
      ( is-injective-left-add-ℕ 0 (is-injective-succ-ℕ p))))
is-pair-expansion-unique zero-ℕ (succ-ℕ u') v v' p =
  ex-falso (s t)
  where
  s : is-odd-ℕ (succ-ℕ (0 +ℕ (v *ℕ 2)))
  s =
    is-odd-has-odd-expansion-ℕ _
    ( v ,
      ap
        ( succ-ℕ)
        ( commutative-mul-ℕ 2 v ∙
          inv (left-unit-law-add-ℕ _)))
  t : is-even-ℕ (succ-ℕ (0 +ℕ (v *ℕ 2)))
  t = tr is-even-ℕ (inv p) (div-mul-ℕ' _ 2 _ ((exp-ℕ 2 u') , refl))
is-pair-expansion-unique (succ-ℕ u) zero-ℕ v v' p =
  ex-falso (s t)
  where
  s : is-odd-ℕ (succ-ℕ (0 +ℕ (v' *ℕ 2)))
  s =
    is-odd-has-odd-expansion-ℕ _
      ( v' ,
        ap
          ( succ-ℕ)
          ( commutative-mul-ℕ 2 v' ∙ inv (left-unit-law-add-ℕ _)))
  t : is-even-ℕ (succ-ℕ (0 +ℕ (v' *ℕ 2)))
  t = tr is-even-ℕ p (div-mul-ℕ' _ 2 _ ((exp-ℕ 2 u) , refl))
is-pair-expansion-unique (succ-ℕ u) (succ-ℕ u') v v' p =
  pu , pv
  where
  q :
    ((exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2))) ＝
      ((exp-ℕ 2 u') *ℕ (succ-ℕ (v' *ℕ 2)))
  q = is-injective-left-mul-ℕ 2 is-nonzero-two-ℕ
    ( inv (associative-mul-ℕ 2 (exp-ℕ 2 u) (succ-ℕ (v *ℕ 2))) ∙
    ( ( ap (_*ℕ (succ-ℕ (v *ℕ 2)))
      ( commutative-mul-ℕ 2 (exp-ℕ 2 u))) ∙
    ( ( p) ∙
    ( ( ap (_*ℕ (succ-ℕ (v' *ℕ 2)))
      ( commutative-mul-ℕ (exp-ℕ 2 u') 2)) ∙
    ( associative-mul-ℕ 2 (exp-ℕ 2 u') (succ-ℕ (v' *ℕ 2)))))))
  pu : (succ-ℕ u) ＝ (succ-ℕ u')
  pu = ap succ-ℕ (pr1 (is-pair-expansion-unique u u' v v' q))
  pv : v ＝ v'
  pv = pr2 (is-pair-expansion-unique u u' v v' q)
```

A pairing function is a bijection between `ℕ × ℕ` and `ℕ`.

## Definition

```text
pairing-map : ℕ × ℕ → ℕ
pairing-map (u , v) =
  pr1 (is-successor-is-nonzero-ℕ (is-nonzero-pair-expansion u v))
```

### Pairing function is split surjective

```text
is-split-surjective-pairing-map : is-split-surjective pairing-map
is-split-surjective-pairing-map n =
  (u , v) , is-injective-succ-ℕ (q ∙ s)
  where
  u = pr1 (pr1 (has-pair-expansion n))
  v = pr2 (pr1 (has-pair-expansion n))
  s = pr2 (has-pair-expansion n)
  r = is-successor-is-nonzero-ℕ (is-nonzero-pair-expansion u v)
  q :
    ( succ-ℕ (pairing-map (u , v))) ＝
    ( (exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2)))
  q = inv (pr2 r)
```

### Pairing function is injective

```text
is-injective-pairing-map : is-injective pairing-map
is-injective-pairing-map {u , v} {u' , v'} p =
  ( eq-pair' (is-pair-expansion-unique u u' v v' q))
  where
  r = is-successor-is-nonzero-ℕ (is-nonzero-pair-expansion u v)
  s = is-successor-is-nonzero-ℕ (is-nonzero-pair-expansion u' v')
  q :
    ( (exp-ℕ 2 u) *ℕ (succ-ℕ (v *ℕ 2))) ＝
    ( (exp-ℕ 2 u') *ℕ (succ-ℕ (v' *ℕ 2)))
  q = (pr2 r) ∙ (ap succ-ℕ p ∙ inv (pr2 s))
```

### Pairing function is equivalence

```text
is-equiv-pairing-map : is-equiv pairing-map
is-equiv-pairing-map =
  is-equiv-is-split-surjective-is-injective
    pairing-map
    is-injective-pairing-map
    is-split-surjective-pairing-map
```
