# Type arithmetic with natural numbers

```agda
module foundation.type-arithmetic-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.pairing-function
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.functoriality-coproduct-types
open import foundation.split-surjective-maps

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-pair-types
open import foundation-core.empty-types
open import foundation-core.equality-cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
```

</details>

## Idea

We prove arithmetical laws involving the natural numbers

## Laws

### The coproduct `ℕ + ℕ` is equivalent to `ℕ`

```agda
succ-ℕ+ℕ : ℕ + ℕ → ℕ + ℕ
succ-ℕ+ℕ = map-coprod succ-ℕ succ-ℕ

map-ℕ+ℕ-to-ℕ : ℕ + ℕ → ℕ
map-ℕ+ℕ-to-ℕ (inl x) = mul-ℕ 2 x
map-ℕ+ℕ-to-ℕ (inr x) = succ-ℕ (mul-ℕ 2 x)

action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ :
  (x : ℕ + ℕ) →
    (map-ℕ+ℕ-to-ℕ (succ-ℕ+ℕ x)) ＝
      (succ-ℕ (succ-ℕ (map-ℕ+ℕ-to-ℕ x)))
action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ (inl x) =
  ap succ-ℕ (left-successor-law-add-ℕ _ _)
action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ (inr x) =
  ap (succ-ℕ ∘ succ-ℕ) (left-successor-law-add-ℕ _ _)

is-split-surjective-map-ℕ+ℕ-to-ℕ : is-split-surjective map-ℕ+ℕ-to-ℕ
is-split-surjective-map-ℕ+ℕ-to-ℕ zero-ℕ =
  ( pair (inl 0) refl)
is-split-surjective-map-ℕ+ℕ-to-ℕ (succ-ℕ zero-ℕ) =
  ( pair (inr 0) refl)
is-split-surjective-map-ℕ+ℕ-to-ℕ (succ-ℕ (succ-ℕ b)) =
  ( pair
    ( succ-ℕ+ℕ (pr1 (is-split-surjective-map-ℕ+ℕ-to-ℕ b)))
    ( ( action-map-ℕ+ℕ-to-ℕ-on-succ-ℕ+ℕ
        ( pr1 (is-split-surjective-map-ℕ+ℕ-to-ℕ b))) ∙
      ( ap (succ-ℕ ∘ succ-ℕ)
        ( pr2 (is-split-surjective-map-ℕ+ℕ-to-ℕ b)))))

is-injective-map-ℕ+ℕ-to-ℕ : is-injective map-ℕ+ℕ-to-ℕ
is-injective-map-ℕ+ℕ-to-ℕ {inl x} {inl y} p =
  ( ap inl (is-injective-mul-succ-ℕ 1 p))
is-injective-map-ℕ+ℕ-to-ℕ {inl x} {inr y} p = ex-falso (t s)
  where
    s : (div-ℕ 2 (succ-ℕ (mul-ℕ 2 y)))
    s = concatenate-div-eq-ℕ (x , commutative-mul-ℕ x 2) p

    t : ¬ (div-ℕ 2 (succ-ℕ (mul-ℕ 2 y)))
    t =
      ( is-odd-succ-is-even-ℕ
        ( mul-ℕ 2 y)
        ( y , commutative-mul-ℕ y 2))
is-injective-map-ℕ+ℕ-to-ℕ {inr x} {inl y} p = ex-falso (t s)
  where
    s : (div-ℕ 2 (succ-ℕ (mul-ℕ 2 x)))
    s = concatenate-div-eq-ℕ (y , commutative-mul-ℕ y 2) (inv p)

    t : ¬ (div-ℕ 2 (succ-ℕ (mul-ℕ 2 x)))
    t =
      ( is-odd-succ-is-even-ℕ
        ( mul-ℕ 2 x)
        ( x , commutative-mul-ℕ x 2))
is-injective-map-ℕ+ℕ-to-ℕ {inr x} {inr y} p =
  ( ap inr (is-injective-mul-succ-ℕ 1 (is-injective-succ-ℕ p)))

is-equiv-map-ℕ+ℕ-to-ℕ : is-equiv map-ℕ+ℕ-to-ℕ
is-equiv-map-ℕ+ℕ-to-ℕ =
  is-equiv-is-split-surjective-is-injective
    ( map-ℕ+ℕ-to-ℕ)
    ( is-injective-map-ℕ+ℕ-to-ℕ)
    ( is-split-surjective-map-ℕ+ℕ-to-ℕ)

ℕ+ℕ≃ℕ : (ℕ + ℕ) ≃ ℕ
ℕ+ℕ≃ℕ = pair map-ℕ+ℕ-to-ℕ is-equiv-map-ℕ+ℕ-to-ℕ

map-ℕ-to-ℕ+ℕ : ℕ → ℕ + ℕ
map-ℕ-to-ℕ+ℕ = map-inv-is-equiv (pr2 ℕ+ℕ≃ℕ)

is-equiv-map-ℕ-to-ℕ+ℕ : is-equiv map-ℕ-to-ℕ+ℕ
is-equiv-map-ℕ-to-ℕ+ℕ = is-equiv-map-inv-is-equiv (pr2 ℕ+ℕ≃ℕ)
```

### The product `ℕ × ℕ` is equivalent to `ℕ`

```agda
ℕ×ℕ≃ℕ : (ℕ × ℕ) ≃ ℕ
ℕ×ℕ≃ℕ = pair pairing-map is-equiv-pairing-map

map-ℕ-to-ℕ×ℕ : ℕ → ℕ × ℕ
map-ℕ-to-ℕ×ℕ = map-inv-is-equiv (pr2 ℕ×ℕ≃ℕ)

is-equiv-map-ℕ-to-ℕ×ℕ : is-equiv map-ℕ-to-ℕ×ℕ
is-equiv-map-ℕ-to-ℕ×ℕ = is-equiv-map-inv-is-equiv (pr2 ℕ×ℕ≃ℕ)
```

### The coproduct `1 + ℕ` is equivalent to `N`

```agda
map-ℕ-to-1+ℕ : ℕ → unit + ℕ
map-ℕ-to-1+ℕ zero-ℕ = inl star
map-ℕ-to-1+ℕ (succ-ℕ n) = inr n

map-1+ℕ-to-ℕ : unit + ℕ → ℕ
map-1+ℕ-to-ℕ (inr n) = succ-ℕ n
map-1+ℕ-to-ℕ (inl star) = zero-ℕ

is-equiv-map-1+ℕ-to-ℕ : is-equiv map-1+ℕ-to-ℕ
is-equiv-map-1+ℕ-to-ℕ =
  ( map-ℕ-to-1+ℕ ,
    ( λ {
      ( zero-ℕ) → refl ;
      ( succ-ℕ x) → refl})) ,
  ( map-ℕ-to-1+ℕ ,
    ( λ {
      ( inr x) → refl ;
      ( inl star) → refl}))

1+ℕ≃ℕ : (unit + ℕ) ≃ ℕ
1+ℕ≃ℕ = map-1+ℕ-to-ℕ , is-equiv-map-1+ℕ-to-ℕ
```

### The integers `ℤ` is equivalent to `ℕ`

```agda
ℤ≃ℕ : ℤ ≃ ℕ
ℤ≃ℕ = (ℕ+ℕ≃ℕ) ∘e (equiv-coprod id-equiv 1+ℕ≃ℕ)
```
