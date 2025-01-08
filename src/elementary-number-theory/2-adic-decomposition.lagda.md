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
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.split-surjective-maps
open import foundation.transport-along-identifications
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

  exponent-2-adic-decomposition-ℕ : ℕ
  exponent-2-adic-decomposition-ℕ = pr1 d

  index-odd-factor-2-adic-decomposition-ℕ : ℕ
  index-odd-factor-2-adic-decomposition-ℕ = pr1 (pr2 d)

  eq-2-adic-decomposition-ℕ :
    2-adic-composition-ℕ
      exponent-2-adic-decomposition-ℕ
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

The proof is by [based strong induction](elementary-number-theory.based-strong-induction-natural-numbers.md).
We have already seen that every odd natural number has a $2$-adic expansion.
If $1 \leq x$ is an even number, then write $x = 2 \cdot y$. Given a $2$-adic decomposition $(k , l)$ of the number $y$, it follows that $(k + 1 , l)$ is a $2$-adic decomposition of $x$, because

$$
  2^{k+1}(2l + 1) = 2(2^k(2l + 1)) = 2*y = x.
$$

```agda
module _
  (x : ℕ) (H : 1 ≤-ℕ x)
  (f :
    based-□-≤-ℕ 1 (λ y → is-even-ℕ y + is-odd-ℕ y → 2-adic-decomposition-ℕ y) x)
  (K@(q , p) : is-even-ℕ (succ-ℕ x))
  where

  2-adic-decomposition-quotient-even-case-2-adic-decomposition-is-even-or-odd-ℕ :
    2-adic-decomposition-ℕ q
  2-adic-decomposition-quotient-even-case-2-adic-decomposition-is-even-or-odd-ℕ =
    f ( q)
      ( leq-one-quotient-div-ℕ 2 (succ-ℕ x) K (leq-zero-ℕ x))
      ( upper-bound-quotient-is-even-succ-ℕ x K)
      ( is-decidable-is-even-ℕ q)

  exponent-even-case-2-adic-decomposition-is-even-or-odd-ℕ :
    ℕ
  exponent-even-case-2-adic-decomposition-is-even-or-odd-ℕ =
    succ-ℕ
      ( exponent-2-adic-decomposition-ℕ
        ( q)
        ( 2-adic-decomposition-quotient-even-case-2-adic-decomposition-is-even-or-odd-ℕ))
  
  even-case-2-adic-decomposition-is-even-or-odd-ℕ :
    2-adic-decomposition-ℕ (succ-ℕ x)
  even-case-2-adic-decomposition-is-even-or-odd-ℕ =
    ( succ-ℕ (pr1 d) , pr1 (pr2 d) , {!!})
    where

    d =
      f ( q)
        ( leq-one-quotient-div-ℕ 2 (succ-ℕ x) K (leq-zero-ℕ x))
        {!!}
        {!!}
  
2-adic-decomposition-is-even-or-odd-ℕ :
  (n : ℕ) → 1 ≤-ℕ n → is-even-ℕ n + is-odd-ℕ n →
  2-adic-decomposition-ℕ n
2-adic-decomposition-is-even-or-odd-ℕ =
  based-strong-ind-ℕ 1
    ( λ x → (is-even-ℕ x + is-odd-ℕ x) → 2-adic-decomposition-ℕ x)
    ( rec-coproduct
      ( λ H → ex-falso (is-odd-one-ℕ H))
      ( 2-adic-decomposition-is-odd-ℕ 1))
    ( λ x H f →
      rec-coproduct
        ( even-case-2-adic-decomposition-is-even-or-odd-ℕ x H f
          {-
          λ K@(q , p) →
          let
          
          L : 2-adic-decomposition-ℕ q
d          L =
            f ( q)
              ( leq-one-quotient-div-ℕ 2 (succ-ℕ x) K (leq-zero-ℕ x))
              {! upper-bound-quotient-div-ℕ 2 (succ-ℕ x) K!}
              {!!}
          in
          {!f q (leq-one-quotient-div-ℕ 2 (succ-ℕ x) K (leq-zero-ℕ x)) ? ?!}
          -})
        ( 2-adic-decomposition-is-odd-ℕ (succ-ℕ x)))
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
