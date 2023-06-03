# Iterating identities

```agda
module foundation.iterating-identities where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.universal-property-integers

open import foundation.coproduct-types
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

```agda
module _
  { l : Level} {X : UU l} {x : X}
  where

  iterate-identity-ℕ : (x ＝ x) → ℕ → (x ＝ x)
  iterate-identity-ℕ p zero-ℕ = refl
  iterate-identity-ℕ p (succ-ℕ n) = p ∙ (iterate-identity-ℕ p n)

  iterate-identity-ℤ : (x ＝ x) → ℤ → (x ＝ x)
  iterate-identity-ℤ p (inl zero-ℕ) = inv p
  iterate-identity-ℤ p (inl (succ-ℕ n)) = inv p ∙ (iterate-identity-ℤ p (inl n))
  iterate-identity-ℤ p (inr (inl star)) = refl
  iterate-identity-ℤ p (inr (inr zero-ℕ)) = p
  iterate-identity-ℤ p (inr (inr (succ-ℕ n))) =
    p ∙ (iterate-identity-ℤ p (inr (inr n)))

  iterate-pos :
    (n : ℕ) → (p : x ＝ x) →
    iterate-identity-ℤ p (int-ℕ n) ＝ iterate-identity-ℕ p n
  iterate-pos zero-ℕ = refl-htpy
  iterate-pos (succ-ℕ zero-ℕ) p = inv right-unit
  iterate-pos (succ-ℕ (succ-ℕ n)) p = ap (p ∙_) (iterate-pos (succ-ℕ n) p)
```

### Transport along iterated identities

```agda
  tr-iterate-identity-ℕ :
    {l2 : Level} {B : X → UU l2} →
    (p : x ＝ x) (n : ℕ) →
    tr B (iterate-identity-ℕ p n) ~ iterate n (tr B p)
  tr-iterate-identity-ℕ p zero-ℕ = refl-htpy
  tr-iterate-identity-ℕ {B = B} p (succ-ℕ n) =
    homotopy-reasoning
      tr B (iterate-identity-ℕ p (succ-ℕ n))
        ~ tr B (iterate-identity-ℕ p n) ∘ (tr B p)
          by tr-concat p _
        ~ iterate (succ-ℕ n) (tr B p)
          by
            ( tr-iterate-identity-ℕ p n ∘ (tr B p)) ∙h
            ( inv-htpy (iterate-succ-ℕ n (tr B p)))
```
