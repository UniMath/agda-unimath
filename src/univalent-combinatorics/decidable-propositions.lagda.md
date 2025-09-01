# Decidable propositions

```agda
module univalent-combinatorics.decidable-propositions where

open import foundation.decidable-propositions public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

### Propositions have countings if and only if they are decidable

```agda
is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e (zero-Fin k))

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-type-Decidable-Prop :
  {l1 : Level} (P : Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-type-Decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-type-Decidable-Prop P (inr f) = count-is-empty f
```

### We can count the elements of an identity type of a type that has decidable equality

```agda
cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (x ＝ y)) → count (x ＝ y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (x ＝ y)
count-eq d x y = cases-count-eq d (d x y)

cases-number-of-elements-count-eq' :
  {l : Level} {X : UU l} {x y : X} →
  is-decidable (x ＝ y) → ℕ
cases-number-of-elements-count-eq' (inl p) = 1
cases-number-of-elements-count-eq' (inr f) = 0

number-of-elements-count-eq' :
  {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) → ℕ
number-of-elements-count-eq' d x y =
  cases-number-of-elements-count-eq' (d x y)

cases-number-of-elements-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (x ＝ y)) →
  Id
    ( number-of-elements-count (cases-count-eq d e))
    ( cases-number-of-elements-count-eq' e)
cases-number-of-elements-count-eq d (inl p) = refl
cases-number-of-elements-count-eq d (inr f) = refl

abstract
  number-of-elements-count-eq :
    {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) →
    number-of-elements-count (count-eq d x y) ＝
    number-of-elements-count-eq' d x y
  number-of-elements-count-eq d x y =
    cases-number-of-elements-count-eq d (d x y)
```
