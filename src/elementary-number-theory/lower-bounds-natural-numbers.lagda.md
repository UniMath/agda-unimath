# Lower bounds of type families over the natural numbers

```agda
module elementary-number-theory.lower-bounds-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "lower bound" Disambiguation="for a type family over ℕ" Agda=is-lower-bound-ℕ}}
for a type family `P` over the
[natural numbers](elementary-number-theory.natural-numbers.md) is a natural
number `n` such that `P x → n ≤ x` for all `x : ℕ`.

## Definition

```agda
is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-lower-bound-ℕ P n = (m : ℕ) → P m → leq-ℕ n m
```

## Properties

### Being a lower bound is a property

```agda
module _
  {l1 : Level} {P : ℕ → UU l1}
  where

  abstract
    is-prop-is-lower-bound-ℕ : (x : ℕ) → is-prop (is-lower-bound-ℕ P x)
    is-prop-is-lower-bound-ℕ x =
      is-prop-Π (λ y → is-prop-function-type (is-prop-leq-ℕ x y))

  is-lower-bound-ℕ-Prop : (x : ℕ) → Prop l1
  pr1 (is-lower-bound-ℕ-Prop x) = is-lower-bound-ℕ P x
  pr2 (is-lower-bound-ℕ-Prop x) = is-prop-is-lower-bound-ℕ x
```

### If `P` is a decidable subtype of `ℕ`, then being a lower bound for `P` is decidable

```agda
module _
  {l1 : Level} (P : decidable-subtype l1 ℕ)
  where

  abstract
    is-decidable-is-lower-bound-decidable-subtype-ℕ :
      (x : ℕ) → is-decidable (is-lower-bound-ℕ (is-in-decidable-subtype P) x)
    is-decidable-is-lower-bound-decidable-subtype-ℕ zero-ℕ =
      inl (λ y _ → leq-zero-ℕ y)
    is-decidable-is-lower-bound-decidable-subtype-ℕ (succ-ℕ n)
      with
        is-decidable-is-lower-bound-decidable-subtype-ℕ n |
        is-decidable-decidable-subtype P n
    ... | inr ¬bound-n | _ =
      inr
        ( λ bound-sn →
          ¬bound-n
            ( λ m pm →
              transitive-leq-ℕ n (succ-ℕ n) m (bound-sn m pm) (succ-leq-ℕ n)))
    ... | inl bound-n | inl pn =
      inr
        ( λ bound-sn →
          contradiction-le-ℕ
            ( n)
            ( succ-ℕ n)
            ( succ-le-ℕ n)
            ( bound-sn n pn))
    ... | inl bound-n | inr ¬pn =
      inl
        ( λ m pm →
          leq-not-le-ℕ
            ( m)
            ( succ-ℕ n)
            ( λ m<sn →
              rec-coproduct
                ( λ m<n → contradiction-le-ℕ m n m<n (bound-n m pm))
                ( λ n≤m →
                  ¬pn
                    ( tr
                      ( is-in-decidable-subtype P)
                      ( antisymmetric-leq-ℕ m n (leq-le-succ-ℕ m n m<sn) n≤m)
                      ( pm)))
                ( decide-le-leq-ℕ m n)))

  decidable-subtype-lower-bound-decidable-subtype-ℕ : decidable-subtype l1 ℕ
  decidable-subtype-lower-bound-decidable-subtype-ℕ n =
    ( is-lower-bound-ℕ (is-in-decidable-subtype P) n ,
      is-prop-is-lower-bound-ℕ n ,
      is-decidable-is-lower-bound-decidable-subtype-ℕ n)
```
