# Type arithmetic with natural numbers

```agda
module elementary-number-theory.type-arithmetic-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.powers-of-two

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.iterating-functions
open import foundation.split-surjective-maps
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We prove arithmetical laws involving the natural numbers

## Laws

### The natural numbers is a fixpoint to the functor `X ↦ 1 + X`

```agda
map-equiv-ℕ : ℕ → unit + ℕ
map-equiv-ℕ zero-ℕ = inl star
map-equiv-ℕ (succ-ℕ n) = inr n

map-inv-equiv-ℕ : unit + ℕ → ℕ
map-inv-equiv-ℕ (inl x) = zero-ℕ
map-inv-equiv-ℕ (inr n) = succ-ℕ n

is-retraction-map-inv-equiv-ℕ :
  ( map-inv-equiv-ℕ ∘ map-equiv-ℕ) ~ id
is-retraction-map-inv-equiv-ℕ zero-ℕ = refl
is-retraction-map-inv-equiv-ℕ (succ-ℕ n) = refl

is-section-map-inv-equiv-ℕ :
  ( map-equiv-ℕ ∘ map-inv-equiv-ℕ) ~ id
is-section-map-inv-equiv-ℕ (inl star) = refl
is-section-map-inv-equiv-ℕ (inr n) = refl

equiv-ℕ : ℕ ≃ (unit + ℕ)
pr1 equiv-ℕ = map-equiv-ℕ
pr2 equiv-ℕ =
  is-equiv-is-invertible
    map-inv-equiv-ℕ
    is-section-map-inv-equiv-ℕ
    is-retraction-map-inv-equiv-ℕ
```

### The coproduct `ℕ + ℕ` is equivalent to `ℕ`

```agda
succ-ℕ+ℕ : ℕ + ℕ → ℕ + ℕ
succ-ℕ+ℕ = map-coproduct succ-ℕ succ-ℕ

map-ℕ+ℕ-to-ℕ : ℕ + ℕ → ℕ
map-ℕ+ℕ-to-ℕ (inl x) = 2 *ℕ x
map-ℕ+ℕ-to-ℕ (inr x) = succ-ℕ (2 *ℕ x)

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
  ( ap inl (is-injective-left-mul-succ-ℕ 1 p))
is-injective-map-ℕ+ℕ-to-ℕ {inl x} {inr y} p =
  ex-falso (t s)
  where
  s : (div-ℕ 2 (succ-ℕ (2 *ℕ y)))
  s = concatenate-div-eq-ℕ (x , commutative-mul-ℕ x 2) p

  t : ¬ (div-ℕ 2 (succ-ℕ (2 *ℕ y)))
  t =
    ( is-odd-succ-is-even-ℕ
      ( 2 *ℕ y)
      ( y , commutative-mul-ℕ y 2))
is-injective-map-ℕ+ℕ-to-ℕ {inr x} {inl y} p =
  ex-falso (t s)
  where
  s : (div-ℕ 2 (succ-ℕ (2 *ℕ x)))
  s = concatenate-div-eq-ℕ (y , commutative-mul-ℕ y 2) (inv p)

  t : ¬ (div-ℕ 2 (succ-ℕ (2 *ℕ x)))
  t =
    ( is-odd-succ-is-even-ℕ
      ( 2 *ℕ x)
      ( x , commutative-mul-ℕ x 2))
is-injective-map-ℕ+ℕ-to-ℕ {inr x} {inr y} p =
  ( ap inr (is-injective-left-mul-succ-ℕ 1 (is-injective-succ-ℕ p)))

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

### The iterated coproduct `ℕ + ℕ + ... + ℕ` is equivalent to `ℕ` for any n

```agda
equiv-iterated-coproduct-ℕ :
  (n : ℕ) → (iterate n (_+_ ℕ) ℕ) ≃ ℕ
equiv-iterated-coproduct-ℕ zero-ℕ = id-equiv
equiv-iterated-coproduct-ℕ (succ-ℕ n) =
  ( ℕ+ℕ≃ℕ) ∘e
    ( equiv-coproduct id-equiv (equiv-iterated-coproduct-ℕ n))
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

### The iterated coproduct `ℕ × ℕ × ... × ℕ` is equivalent to `ℕ` for any n

```agda
equiv-iterated-product-ℕ :
  (n : ℕ) → (iterate n (_×_ ℕ) ℕ) ≃ ℕ
equiv-iterated-product-ℕ zero-ℕ = id-equiv
equiv-iterated-product-ℕ (succ-ℕ n) =
  ( ℕ×ℕ≃ℕ) ∘e
    ( equiv-product id-equiv (equiv-iterated-product-ℕ n))
```

### The coproduct `(Fin n) + ℕ` is equivalent to `N` for any standard finite `Fin n`

```agda
equiv-coproduct-Fin-ℕ : (n : ℕ) → ((Fin n) + ℕ) ≃ ℕ
equiv-coproduct-Fin-ℕ zero-ℕ = left-unit-law-coproduct ℕ
equiv-coproduct-Fin-ℕ (succ-ℕ n) =
  ( equiv-coproduct-Fin-ℕ n) ∘e
    ( equiv-coproduct id-equiv (inv-equiv equiv-ℕ) ∘e
      ( associative-coproduct))
```

### The product `(Fin n) × ℕ` is equivalent to `N` for any standard finite `Fin n` where n is nonzero

```agda
equiv-product-Fin-ℕ : (n : ℕ) → ((Fin (succ-ℕ n)) × ℕ) ≃ ℕ
equiv-product-Fin-ℕ zero-ℕ =
  ( left-unit-law-coproduct ℕ) ∘e
  ( ( equiv-coproduct (left-absorption-product ℕ) left-unit-law-product) ∘e
    ( right-distributive-product-coproduct))
equiv-product-Fin-ℕ (succ-ℕ n) =
  ( ℕ+ℕ≃ℕ) ∘e
  ( ( equiv-coproduct (equiv-product-Fin-ℕ n) left-unit-law-product) ∘e
    ( right-distributive-product-coproduct))
```

### The integers `ℤ` is equivalent to `ℕ`

```agda
ℤ≃ℕ : ℤ ≃ ℕ
ℤ≃ℕ = (ℕ+ℕ≃ℕ) ∘e (equiv-coproduct id-equiv (inv-equiv equiv-ℕ))

map-ℕ-to-ℤ : ℕ → ℤ
map-ℕ-to-ℤ = map-inv-is-equiv (pr2 ℤ≃ℕ)

is-equiv-map-ℕ-to-ℤ : is-equiv map-ℕ-to-ℤ
is-equiv-map-ℕ-to-ℤ = is-equiv-map-inv-is-equiv (pr2 ℤ≃ℕ)
```
