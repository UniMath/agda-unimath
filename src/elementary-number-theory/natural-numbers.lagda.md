# The type of natural numbers

```agda
module elementary-number-theory.natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
```

</details>

## Idea

The {{#concept "natural numbers" WD="natural number" WDID=Q21199 Agda=ℕ}} is an
inductively generated type by the zero element and the successor function. The
induction principle for the natural numbers works to construct sections of type
families over the natural numbers.

## Definitions

### The inductive definition of the type of natural numbers

```agda
data ℕ : UU lzero where
  zero-ℕ : ℕ
  succ-ℕ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

second-succ-ℕ : ℕ → ℕ
second-succ-ℕ = succ-ℕ ∘ succ-ℕ

third-succ-ℕ : ℕ → ℕ
third-succ-ℕ = succ-ℕ ∘ second-succ-ℕ

fourth-succ-ℕ : ℕ → ℕ
fourth-succ-ℕ = succ-ℕ ∘ third-succ-ℕ
```

### Useful predicates on the natural numbers

These predicates can of course be asserted directly without much trouble.
However, using the defined predicates ensures uniformity, and helps naming
definitions.

```agda
is-zero-ℕ : ℕ → UU lzero
is-zero-ℕ n = (n ＝ zero-ℕ)

is-zero-ℕ' : ℕ → UU lzero
is-zero-ℕ' n = (zero-ℕ ＝ n)

is-successor-ℕ : ℕ → UU lzero
is-successor-ℕ n = Σ ℕ (λ y → n ＝ succ-ℕ y)

is-nonzero-ℕ : ℕ → UU lzero
is-nonzero-ℕ n = ¬ (is-zero-ℕ n)

is-one-ℕ : ℕ → UU lzero
is-one-ℕ n = (n ＝ 1)

is-one-ℕ' : ℕ → UU lzero
is-one-ℕ' n = (1 ＝ n)

is-not-one-ℕ : ℕ → UU lzero
is-not-one-ℕ n = ¬ (is-one-ℕ n)

is-not-one-ℕ' : ℕ → UU lzero
is-not-one-ℕ' n = ¬ (is-one-ℕ' n)
```

## Properties

### The induction principle of ℕ

The induction principle of the natural numbers is the
[74th](literature.100-theorems.md#74) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
ind-ℕ :
  {l : Level} {P : ℕ → UU l} →
  P 0 → ((n : ℕ) → P n → P (succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p-zero p-succ 0 = p-zero
ind-ℕ p-zero p-succ (succ-ℕ n) = p-succ n (ind-ℕ p-zero p-succ n)
```

### The recursion principle of ℕ

```agda
rec-ℕ : {l : Level} {A : UU l} → A → (ℕ → A → A) → (ℕ → A)
rec-ℕ = ind-ℕ
```

### The successor function on ℕ is injective

```agda
is-injective-succ-ℕ : is-injective succ-ℕ
is-injective-succ-ℕ refl = refl
```

### Successors are nonzero

```agda
is-nonzero-succ-ℕ : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
is-nonzero-succ-ℕ x ()

is-nonzero-is-successor-ℕ : {x : ℕ} → is-successor-ℕ x → is-nonzero-ℕ x
is-nonzero-is-successor-ℕ (x , refl) ()

is-successor-is-nonzero-ℕ : {x : ℕ} → is-nonzero-ℕ x → is-successor-ℕ x
is-successor-is-nonzero-ℕ {zero-ℕ} H = ex-falso (H refl)
pr1 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = x
pr2 (is-successor-is-nonzero-ℕ {succ-ℕ x} H) = refl

has-no-fixed-points-succ-ℕ : (x : ℕ) → ¬ (succ-ℕ x ＝ x)
has-no-fixed-points-succ-ℕ x ()
```

### Basic nonequalities

```agda
is-nonzero-one-ℕ : is-nonzero-ℕ 1
is-nonzero-one-ℕ ()

is-not-one-zero-ℕ : is-not-one-ℕ zero-ℕ
is-not-one-zero-ℕ ()

is-nonzero-two-ℕ : is-nonzero-ℕ 2
is-nonzero-two-ℕ ()

is-not-one-two-ℕ : is-not-one-ℕ 2
is-not-one-two-ℕ ()
```

## See also

- The based induction principle is defined in
  [`based-induction-natural-numbers`](elementary-number-theory.based-induction-natural-numbers.md).
- The strong induction principle is defined in
  [`strong-induction-natural-numbers`](elementary-number-theory.strong-induction-natural-numbers.md).
- The based strong induction principle is defined in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).

## References

{{#bibliography}}
