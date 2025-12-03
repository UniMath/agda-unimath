# Powers of two

```agda
module elementary-number-theory.powers-of-two where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
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

Any natural number `x` can be written as `(2^u(2v-1))-1` for some pair of
natural numbers `(u , v)`

```agda
map-pair-expansion : ℕ → ℕ → ℕ
map-pair-expansion u v = exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2)

map-pair-expansion-succ-ℕ :
  (u v : ℕ) → map-pair-expansion (succ-ℕ u) v ＝ map-pair-expansion u v *ℕ 2
map-pair-expansion-succ-ℕ u v =
  right-swap-mul-ℕ (exp-ℕ 2 u) 2 (succ-ℕ (v *ℕ 2))

pair-expansion : ℕ → UU lzero
pair-expansion n =
  Σ (ℕ × ℕ) (λ p → (ind-Σ map-pair-expansion p ＝ succ-ℕ n))

abstract
  is-nonzero-pair-expansion :
    (u v : ℕ) → is-nonzero-ℕ (map-pair-expansion u v)
  is-nonzero-pair-expansion u v =
    is-nonzero-mul-ℕ _ _
      ( is-nonzero-exp-ℕ 2 u is-nonzero-two-ℕ)
      ( is-nonzero-succ-ℕ _)

  has-pair-expansion-is-even-or-odd :
    (n : ℕ) → is-even-ℕ n + is-odd-ℕ n → pair-expansion n
  has-pair-expansion-is-even-or-odd n =
    strong-ind-ℕ
    ( λ m → (is-even-ℕ m + is-odd-ℕ m) → (pair-expansion m))
    ( λ x → (0 , 0) , refl)
    ( λ k f →
      ( λ where
        ( inl x) →
          ( let s = has-odd-expansion-is-odd k (is-odd-is-even-succ-ℕ k x)
            in
              pair
                ( 0 , (succ-ℕ (pr1 s)))
                ( ( ap ((succ-ℕ ∘ succ-ℕ) ∘ succ-ℕ) (left-unit-law-add-ℕ _)) ∙
                  ( ( ap (succ-ℕ ∘ succ-ℕ) (pr2 s)))))
        ( inr x) →
          ( let e : is-even-ℕ k
                e = is-even-is-odd-succ-ℕ k x

                t : (pr1 e) ≤-ℕ k
                t = leq-quotient-div-ℕ' 2 k is-nonzero-two-ℕ e

                s : (pair-expansion (pr1 e))
                s = f (pr1 e) t (is-decidable-is-even-ℕ (pr1 e))
            in
              pair
                ( succ-ℕ (pr1 (pr1 s)) , pr2 (pr1 s))
                ( ( ap
                    ( _*ℕ (succ-ℕ ((pr2 (pr1 s)) *ℕ 2)))
                    ( commutative-mul-ℕ (exp-ℕ 2 (pr1 (pr1 s))) 2)) ∙
                  ( ( associative-mul-ℕ 2
                      ( exp-ℕ 2 (pr1 (pr1 s)))
                      ( succ-ℕ ((pr2 (pr1 s)) *ℕ 2))) ∙
                    ( ( ap (2 *ℕ_) (pr2 s)) ∙
                      ( ( ap succ-ℕ
                          ( left-successor-law-add-ℕ (0 +ℕ (pr1 e)) (pr1 e))) ∙
                        ( ( ap
                            ( succ-ℕ ∘ succ-ℕ)
                            ( ap (_+ℕ (pr1 e)) (left-unit-law-add-ℕ (pr1 e)))) ∙
                          ( ( ap
                              ( succ-ℕ ∘ succ-ℕ)
                              ( inv (right-two-law-mul-ℕ (pr1 e)))) ∙
                              ( ( ap (succ-ℕ ∘ succ-ℕ) (pr2 e))))))))))))
    ( n)

has-pair-expansion : (n : ℕ) → pair-expansion n
has-pair-expansion n =
  has-pair-expansion-is-even-or-odd n (is-decidable-is-even-ℕ n)
```

### If `(u , v)` and `(u' , v')` are the pairs corresponding the same number `x`, then `u ＝ u'` and `v ＝ v'`

```agda
abstract
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
    s = is-odd-has-odd-expansion _
      ( v , ap succ-ℕ (inv (left-unit-law-add-ℕ _)))
    t : is-even-ℕ (succ-ℕ (0 +ℕ (v *ℕ 2)))
    t = tr is-even-ℕ (inv p) (div-mul-ℕ' _ 2 _ ((exp-ℕ 2 u') , refl))
  is-pair-expansion-unique (succ-ℕ u) zero-ℕ v v' p =
    ex-falso (s t)
    where
    s : is-odd-ℕ (succ-ℕ (0 +ℕ (v' *ℕ 2)))
    s = is-odd-has-odd-expansion _
      ( v' , ap succ-ℕ (inv (left-unit-law-add-ℕ _)))
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

```agda
pairing-map : ℕ × ℕ → ℕ
pairing-map (u , v) =
  pr1 (is-successor-is-nonzero-ℕ (is-nonzero-pair-expansion u v))
```

### Pairing function is split surjective

```agda
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

```agda
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

```agda
is-equiv-pairing-map : is-equiv pairing-map
is-equiv-pairing-map =
  is-equiv-is-split-surjective-is-injective
    pairing-map
    is-injective-pairing-map
    is-split-surjective-pairing-map
```
