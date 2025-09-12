# Counting the elements of dependent pair types

```agda
module univalent-combinatorics.counting-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Consider a type family `B` over `A`, and consider the following statements

1. The elements of `A` can be counted.
2. For each `x : A`, the elements of `B x` can be counted
3. The elements of `Σ A B` can be counted.

If 1 holds, then 2 holds if and only if 3 holds. Furthermore if 2 and 3 hold,
then 1 holds if and only if the elements of `Σ (x : A), ¬ (B x)` can be counted,
i.e., if the elements in the complement of `B` can be counted.

## Proofs

### `Σ A B` can be counted if `A` can be counted and if each `B x` can be counted

```agda
count-Σ-Fin :
  {l : Level} (k : ℕ) {B : Fin k → UU l} →
  ((x : Fin k) → count (B x)) → count (Σ (Fin k) B)
count-Σ-Fin 0 f = count-is-empty pr1
count-Σ-Fin (succ-ℕ k) {B} f =
  count-equiv'
    ( ( equiv-coproduct id-equiv (left-unit-law-Σ (B ∘ inr))) ∘e
      ( right-distributive-Σ-coproduct B))
    ( count-coproduct (count-Σ-Fin k (f ∘ inl)) (f (inr star)))

count-Σ' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' k {B = B} e f =
  count-equiv (equiv-Σ-equiv-base B e) (count-Σ-Fin k (f ∘ map-equiv e))

abstract
  equiv-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
    Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
  equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
pr1 (count-Σ (pair k e) f) = number-of-elements-count (count-Σ' k e f)
pr2 (count-Σ (pair k e) f) = equiv-count-Σ' k e f
```

### We compute the number of elements of a Σ-type

```agda
abstract
  number-of-elements-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
    (f : (x : A) → count (B x)) →
    Id ( number-of-elements-count (count-Σ' k e f))
      ( sum-Fin-ℕ k (λ x → number-of-elements-count (f (map-equiv e x))))
  number-of-elements-count-Σ' zero-ℕ e f = refl
  number-of-elements-count-Σ' (succ-ℕ k) e f =
    ( number-of-elements-count-coproduct
      ( count-Σ' k id-equiv (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star)))) ∙
    ( ap
      ( _+ℕ (number-of-elements-count (f (map-equiv e (inr star)))))
      ( number-of-elements-count-Σ' k id-equiv (λ x → f (map-equiv e (inl x)))))

abstract
  number-of-elements-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : (x : A) → count (B x)) →
    Id ( number-of-elements-count (count-Σ e f))
      ( sum-count-ℕ e (λ x → number-of-elements-count (f x)))
  number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f
```

### If `A` and `Σ A B` can be counted, then each `B x` can be counted

```agda
count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  has-decidable-equality A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} d f x =
  count-equiv
    ( equiv-fiber-pr1 B x)
    ( count-Σ f
      ( λ z → count-eq d (pr1 z) x))

count-fiber-count-Σ-count-base :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ-count-base e f x =
  count-fiber-count-Σ (has-decidable-equality-count e) f x
```

### If `Σ A B` and each `B x` can be counted, and if `B` has a section, then `A` can be counted

```agda
count-fiber-map-section-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fiber (map-section-family b) t)
count-fiber-map-section-family {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-torsorial-Id' y)
            ( pair y refl)) ∘e
        ( inv-associative-Σ)) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fiber (map-section-family b))
    ( count-Σ e (count-fiber-map-section-family b e f))
```

More generally, if `Σ A B` and each `B x` can be counted, then `A` can be
counted if and only if the type `Σ (x : A), ¬ (B x)` can be counted. However, to
avoid having to invoke function extensionality, we show that if `Σ A B` and each
`B x` can be counted, then `A` can be counted if and only if

```text
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))),
```

where `f : (x : A) → count (B x)`. Thus, we have a precise characterization of
when the elements of `A` can be counted, if it is given that `Σ A B` and each
`B x` can be counted.

```agda
section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → (B x) + (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) (zero-Fin k)))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coproduct)
      ( count-coproduct e g))
    ( λ x →
      count-coproduct
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))
```

### If `A` can be counted and `Σ A P` can be counted for a subtype of `A`, then `P` is decidable

```agda
is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ-count-base e f x)
```

```agda
abstract
  double-counting-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) →
    Id
      ( number-of-elements-count count-C)
      ( sum-count-ℕ count-A (λ x → number-of-elements-count (count-B x)))
  double-counting-Σ count-A count-B count-C =
    ( double-counting count-C (count-Σ count-A count-B)) ∙
    ( number-of-elements-count-Σ count-A count-B)

abstract
  sum-number-of-elements-count-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : count (Σ A B)) →
    Id
      ( sum-count-ℕ e
        ( λ x → number-of-elements-count
          (count-fiber-count-Σ-count-base e f x)))
      ( number-of-elements-count f)
  sum-number-of-elements-count-fiber-count-Σ e f =
    ( inv
      ( number-of-elements-count-Σ e (count-fiber-count-Σ-count-base e f))) ∙
    ( double-counting (count-Σ e (count-fiber-count-Σ-count-base e f)) f)

abstract
  double-counting-fiber-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (count-C : count (Σ A B)) (x : A) →
    Id
      ( number-of-elements-count (count-B x))
      ( number-of-elements-count
        ( count-fiber-count-Σ-count-base count-A count-C x))
  double-counting-fiber-count-Σ count-A count-B count-C x =
    double-counting
      ( count-B x)
      ( count-fiber-count-Σ-count-base count-A count-C x)

abstract
  sum-number-of-elements-count-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-ΣAB : count (Σ A B)) (count-B : (x : A) → count (B x)) →
    Id
      ( sum-count-ℕ
        ( count-base-count-Σ b count-ΣAB count-B)
        ( λ x → number-of-elements-count (count-B x)))
      ( number-of-elements-count count-ΣAB)
  sum-number-of-elements-count-base-count-Σ b count-ΣAB count-B =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ b count-ΣAB count-B)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ (count-base-count-Σ b count-ΣAB count-B) count-B)
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    (count-A : count A) (count-B : (x : A) → count (B x))
    (count-ΣAB : count (Σ A B)) →
    Id
      ( number-of-elements-count (count-base-count-Σ b count-ΣAB count-B))
      ( number-of-elements-count count-A)
  double-counting-base-count-Σ b count-A count-B count-ΣAB =
    double-counting (count-base-count-Σ b count-ΣAB count-B) count-A

abstract
  sum-number-of-elements-count-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-ΣAB : count (Σ A B)) →
    ( count-B : (x : A) → count (B x)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    Id
      ( sum-count-ℕ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( λ x → number-of-elements-count (count-B x)))
      ( number-of-elements-count count-ΣAB)
  sum-number-of-elements-count-base-count-Σ' count-ΣAB count-B count-nB =
    ( inv
      ( number-of-elements-count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))) ∙
    ( double-counting
      ( count-Σ
        ( count-base-count-Σ' count-ΣAB count-B count-nB)
        ( count-B))
      ( count-ΣAB))

abstract
  double-counting-base-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    ( count-B : (x : A) → count (B x)) (count-ΣAB : count (Σ A B)) →
    ( count-nB :
      count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (count-B x))))) →
    Id
      ( number-of-elements-count
        ( count-base-count-Σ' count-ΣAB count-B count-nB))
      ( number-of-elements-count count-A)
  double-counting-base-count-Σ' count-A count-B count-ΣAB count-nB =
    double-counting (count-base-count-Σ' count-ΣAB count-B count-nB) count-A
```
