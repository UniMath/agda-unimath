# Bezout's lemma in the integers

```agda
module elementary-number-theory.bezouts-lemma-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bezouts-lemma-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.identity-types
open import foundation.unit-type
```

</details>

## Lemma

```agda
bezouts-lemma-eqn-to-int :
  (x y : ℤ) → (H : is-nonzero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))) →
  nat-gcd-ℤ x y ＝
  dist-ℕ
    ( abs-ℤ
      ( mul-ℤ
        ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)) x))
    ( abs-ℤ
      ( mul-ℤ
        ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)) y))
bezouts-lemma-eqn-to-int x y H =
  equational-reasoning
    nat-gcd-ℤ x y
    ＝ dist-ℕ
      ( mul-ℕ
        ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H) (abs-ℤ x))
      ( mul-ℕ
        ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) (abs-ℤ y))
      by (inv (bezouts-lemma-eqn-ℕ (abs-ℤ x) (abs-ℤ y) H))
    ＝ dist-ℕ
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ x))
        ( mul-ℕ
          ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)
          ( abs-ℤ y))
      by
        ( ap
          ( λ K →
            dist-ℕ
              ( mul-ℕ K (abs-ℤ x))
              ( mul-ℕ
                ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)
                ( abs-ℤ y)))
          ( inv
            ( abs-int-ℕ
              ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))))
    ＝ dist-ℕ
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ x))
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ y))
      by
        ( ap
          ( λ K →
            dist-ℕ
              ( mul-ℕ
                ( abs-ℤ
                  ( int-ℕ
                    ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)))
                ( abs-ℤ x))
              ( mul-ℕ K (abs-ℤ y)))
        (inv
          ( abs-int-ℕ
            ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))))
    ＝ dist-ℕ
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
            ( x)))
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ y))
      by
        ( ap
          ( λ K →
            dist-ℕ
              ( K)
              ( mul-ℕ
                ( abs-ℤ
                  ( int-ℕ
                    ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)))
                ( abs-ℤ y)))
          ( inv
            ( multiplicative-abs-ℤ
              ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
              ( x))))
    ＝ dist-ℕ
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
            ( x)))
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))
            ( y)))
      by
        ( ap
          ( dist-ℕ
            ( abs-ℤ
              ( mul-ℤ
                ( int-ℕ
                  ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
                ( x))))
          ( inv
            ( multiplicative-abs-ℤ
              ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))
              ( y))))

refactor-pos-cond :
  (x y : ℤ) → (H : is-positive-ℤ x) → (K : is-positive-ℤ y) →
  is-nonzero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))
refactor-pos-cond x y H _ =
  is-nonzero-abs-ℤ x H ∘ is-zero-left-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

bezouts-lemma-refactor-hypotheses :
  (x y : ℤ) (H : is-positive-ℤ x) (K : is-positive-ℤ y) →
  nat-gcd-ℤ x y ＝
  abs-ℤ
    ( diff-ℤ
      ( mul-ℤ
        ( int-ℕ
          ( minimal-positive-distance-x-coeff
            ( abs-ℤ x)
            ( abs-ℤ y)
            ( refactor-pos-cond x y H K)))
        ( x))
    ( mul-ℤ
      ( int-ℕ
        ( minimal-positive-distance-y-coeff
          ( abs-ℤ x)
          ( abs-ℤ y)
          ( refactor-pos-cond x y H K)))
      ( y)))
bezouts-lemma-refactor-hypotheses x y H K =
  equational-reasoning
    nat-gcd-ℤ x y
    ＝ dist-ℕ
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( x)))
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( y)))
      by bezouts-lemma-eqn-to-int x y P
    ＝ dist-ℤ
        ( mul-ℤ
          ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
          ( x))
        ( mul-ℤ
          (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
          ( y))
      by
        dist-abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( x))
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( y))
        x-prod-nonneg y-prod-nonneg
  where
  P : is-nonzero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))
  P = (refactor-pos-cond x y H K)
  x-prod-nonneg :
    is-nonnegative-ℤ
      ( mul-ℤ
        ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
        ( x))
  x-prod-nonneg = is-nonnegative-mul-ℤ
    (is-nonnegative-int-ℕ
      ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
    (is-nonnegative-is-positive-ℤ H)
  y-prod-nonneg :
    is-nonnegative-ℤ
      ( mul-ℤ
        ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
        ( y))
  y-prod-nonneg =
    is-nonnegative-mul-ℤ
      ( is-nonnegative-int-ℕ
        ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
      ( is-nonnegative-is-positive-ℤ K)

bezouts-lemma-pos-ints :
  (x y : ℤ) (H : is-positive-ℤ x) (K : is-positive-ℤ y) →
  Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
bezouts-lemma-pos-ints x y H K =
  sx-ty-nonneg-case-split
    ( decide-is-nonnegative-ℤ {diff-ℤ (mul-ℤ s x) (mul-ℤ t y)})
  where
  s : ℤ
  s = int-ℕ (minimal-positive-distance-x-coeff
    (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))
  t : ℤ
  t = int-ℕ (minimal-positive-distance-y-coeff
    (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))

  sx-ty-nonneg-case-split :
    ( is-nonnegative-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y)) +
      is-nonnegative-ℤ (neg-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y)))) →
    Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
  pr1 (sx-ty-nonneg-case-split (inl pos)) = s
  pr1 (pr2 (sx-ty-nonneg-case-split (inl pos))) = neg-ℤ t
  pr2 (pr2 (sx-ty-nonneg-case-split (inl pos))) =
    inv
    ( equational-reasoning
        gcd-ℤ x y
        ＝ int-ℕ (abs-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y)))
          by ap int-ℕ (bezouts-lemma-refactor-hypotheses x y H K)
        ＝ diff-ℤ (mul-ℤ s x) (mul-ℤ t y)
          by int-abs-is-nonnegative-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y)) pos
        ＝ add-ℤ (mul-ℤ s x) (mul-ℤ (neg-ℤ t) y)
          by ap (λ M → add-ℤ (mul-ℤ s x) M) (inv (left-negative-law-mul-ℤ t y)))

  pr1 (sx-ty-nonneg-case-split (inr neg)) = neg-ℤ s
  pr1 (pr2 (sx-ty-nonneg-case-split (inr neg))) = t
  pr2 (pr2 (sx-ty-nonneg-case-split (inr neg))) =
    inv
      ( equational-reasoning
          gcd-ℤ x y
          ＝ int-ℕ (abs-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y)))
            by ap int-ℕ (bezouts-lemma-refactor-hypotheses x y H K)
          ＝ int-ℕ (abs-ℤ (neg-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y))))
            by ap (int-ℕ) (inv (abs-neg-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y))))
          ＝ neg-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y))
            by
              int-abs-is-nonnegative-ℤ
                ( neg-ℤ (diff-ℤ (mul-ℤ s x) (mul-ℤ t y)))
                ( neg)
          ＝ add-ℤ (neg-ℤ (mul-ℤ s x)) (neg-ℤ (neg-ℤ (mul-ℤ t y)))
            by distributive-neg-add-ℤ (mul-ℤ s x) (neg-ℤ (mul-ℤ t y))
          ＝ add-ℤ (mul-ℤ (neg-ℤ s) x) (neg-ℤ (neg-ℤ (mul-ℤ t y)))
            by ap (λ M → add-ℤ M (neg-ℤ (neg-ℤ (mul-ℤ t y))))
              (inv (left-negative-law-mul-ℤ s x))
          ＝ add-ℤ (mul-ℤ (neg-ℤ s) x) (mul-ℤ t y)
            by ap (λ M → add-ℤ (mul-ℤ (neg-ℤ s) x) M) (neg-neg-ℤ (mul-ℤ t y)))

bezouts-lemma-ℤ :
  (x y : ℤ) → Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
bezouts-lemma-ℤ (inl x) (inl y) = pair (neg-ℤ s) (pair (neg-ℤ t) eqn)
  where
  pos-bezout :
    Σ ( ℤ)
      ( λ s →
        Σ ( ℤ)
          ( λ t →
            ( add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))) ＝
            ( gcd-ℤ (inr (inr x)) (inr (inr y)))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ
  s = pr1 (pos-bezout)
  t : ℤ
  t = pr1 (pr2 (pos-bezout))
  eqn :
    add-ℤ (mul-ℤ (neg-ℤ s) (inl x)) (mul-ℤ (neg-ℤ t) (inl y)) ＝
    gcd-ℤ (inl x) (inl y)
  eqn =
    equational-reasoning
      add-ℤ
        ( mul-ℤ (neg-ℤ s) (neg-ℤ (inr (inr x))))
        ( mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y))))
      ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y))))
        by
          ( ap
            ( λ M → add-ℤ M (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y)))))
            ( double-negative-law-mul-ℤ s (inr (inr x))))
      ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))
        by
          ( ap
            ( add-ℤ (mul-ℤ s (inr (inr x))))
            ( double-negative-law-mul-ℤ t (inr (inr y))))
      ＝ gcd-ℤ (inr (inr x)) (inr (inr y))
        by pr2 (pr2 (pos-bezout))
      ＝ gcd-ℤ (inl x) (inr (inr y))
        by ap (λ M → (int-ℕ (gcd-ℕ M (succ-ℕ y)))) (abs-neg-ℤ (inr (inr x)))
      ＝ gcd-ℤ (inl x) (inl y)
        by ap (λ M → (int-ℕ (gcd-ℕ (succ-ℕ x) M))) (abs-neg-ℤ (inr (inr y)))
bezouts-lemma-ℤ (inl x) (inr (inl star)) = pair neg-one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    add-ℤ (mul-ℤ neg-one-ℤ (inl x)) (mul-ℤ one-ℤ (inr (inl star))) ＝
    gcd-ℤ (inl x) (inr (inl star))
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ neg-one-ℤ (inl x)) (mul-ℤ one-ℤ (inr (inl star)))
      ＝ add-ℤ (inr (inr x)) (mul-ℤ one-ℤ (inr (inl star)))
        by
          ap
            ( λ M → add-ℤ M (mul-ℤ one-ℤ (inr (inl star))))
            ( inv (is-mul-neg-one-neg-ℤ (inl x)))
      ＝ add-ℤ (inr (inr x)) zero-ℤ
        by ap (add-ℤ (inr (inr x))) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inl x))
        by right-unit-law-add-ℤ (inr (inr x))
      ＝ gcd-ℤ (inl x) zero-ℤ
        by inv (is-id-is-gcd-zero-ℤ' {inl x} {gcd-ℤ (inl x) zero-ℤ} refl)
bezouts-lemma-ℤ (inl x) (inr (inr y)) = pair (neg-ℤ s) (pair t eqn)
  where
  pos-bezout :
    Σ ( ℤ)
      ( λ s →
        Σ ( ℤ)
          ( λ t →
            add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y))) ＝
            gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ
  s = pr1 (pos-bezout)
  t : ℤ
  t = pr1 (pr2 (pos-bezout))
  eqn :
    add-ℤ (mul-ℤ (neg-ℤ s) (inl x)) (mul-ℤ t (inr (inr y))) ＝
    gcd-ℤ (inl x) (inr (inr y))
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ (neg-ℤ s) (neg-ℤ (inr (inr x)))) (mul-ℤ t (inr (inr y)))
      ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))
        by ap (λ M → add-ℤ M (mul-ℤ t (inr (inr y))))
          (double-negative-law-mul-ℤ s (inr (inr x)))
      ＝ gcd-ℤ (inr (inr x)) (inr (inr y))
        by pr2 (pr2 (pos-bezout))
      ＝ gcd-ℤ (inl x) (inr (inr y))
        by ap (λ M → (int-ℕ (gcd-ℕ M (succ-ℕ y)))) (abs-neg-ℤ (inr (inr x)))
bezouts-lemma-ℤ (inr (inl star)) (inl y) = pair one-ℤ (pair neg-one-ℤ eqn)
  where
  eqn :
    add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ neg-one-ℤ (inl y)) ＝
    gcd-ℤ (inr (inl star)) (inl y)
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ neg-one-ℤ (inl y))
      ＝ add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (inr (inr y))
        by
          ap
            ( add-ℤ (mul-ℤ one-ℤ (inr (inl star))))
            ( inv (is-mul-neg-one-neg-ℤ (inl y)))
      ＝ add-ℤ zero-ℤ (inr (inr y))
        by ap (λ M → add-ℤ M (inr (inr y))) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inl y))
        by left-unit-law-add-ℤ (inr (inr y))
      ＝ gcd-ℤ zero-ℤ (inl y)
        by inv (is-id-is-gcd-zero-ℤ {inl y} {gcd-ℤ zero-ℤ (inl y)} refl)
bezouts-lemma-ℤ (inr (inl star)) (inr (inl star)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inl star))) ＝
    gcd-ℤ zero-ℤ zero-ℤ
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inl star)))
      ＝ add-ℤ zero-ℤ (mul-ℤ one-ℤ (inr (inl star)))
        by
          ap
            ( λ M → add-ℤ M (mul-ℤ one-ℤ (inr (inl star))))
            ( right-zero-law-mul-ℤ one-ℤ)
      ＝ add-ℤ zero-ℤ zero-ℤ
        by ap (λ M → add-ℤ zero-ℤ M) (right-zero-law-mul-ℤ one-ℤ)
      ＝ gcd-ℤ zero-ℤ zero-ℤ
        by inv (is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl)
bezouts-lemma-ℤ (inr (inl star)) (inr (inr y)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inr y))) ＝
    gcd-ℤ (inr (inl star)) (inr (inr y))
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inr y)))
      ＝ add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (inr (inr y))
        by ap
          ( add-ℤ (mul-ℤ one-ℤ (inr (inl star))))
          ( inv (left-unit-law-mul-ℤ (inr (inr y))))
      ＝ add-ℤ zero-ℤ (inr (inr y))
        by ap (λ M → add-ℤ M (inr (inr y))) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inr (inr y)))
        by left-unit-law-add-ℤ (inr (inr y))
      ＝ gcd-ℤ zero-ℤ (inr (inr y))
        by
          inv
            ( is-id-is-gcd-zero-ℤ
              { inr (inr y)}
              { gcd-ℤ zero-ℤ (inr (inr y))}
              ( refl))
bezouts-lemma-ℤ (inr (inr x)) (inl y) = pair s (pair (neg-ℤ t) eqn)
  where
  pos-bezout :
    Σ ( ℤ)
      ( λ s →
        Σ ( ℤ)
          ( λ t →
            add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y))) ＝
            gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ
  s = pr1 (pos-bezout)
  t : ℤ
  t = pr1 (pr2 (pos-bezout))
  eqn :
    add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ (neg-ℤ t) (inl y)) ＝
    gcd-ℤ (inr (inr x)) (inl y)
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y))))
      ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))
        by ap (λ M → add-ℤ (mul-ℤ s (inr (inr x))) M)
          (double-negative-law-mul-ℤ t (inr (inr y)))
      ＝ gcd-ℤ (inr (inr x)) (inr (inr y))
        by pr2 (pr2 (pos-bezout))
      ＝ gcd-ℤ (inr (inr x)) (inl y)
        by ap (λ M → (int-ℕ (gcd-ℕ (succ-ℕ x) M))) (abs-neg-ℤ (inr (inr y)))
bezouts-lemma-ℤ (inr (inr x)) (inr (inl star)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    add-ℤ (mul-ℤ one-ℤ (inr (inr x))) (mul-ℤ one-ℤ (inr (inl star))) ＝
    gcd-ℤ (inr (inr x)) (inr (inl star))
  eqn =
    equational-reasoning
      add-ℤ (mul-ℤ one-ℤ (inr (inr x))) (mul-ℤ one-ℤ (inr (inl star)))
      ＝ add-ℤ (inr (inr x)) (mul-ℤ one-ℤ (inr (inl star)))
        by
          ap
            ( λ M → add-ℤ M (mul-ℤ one-ℤ (inr (inl star))))
            ( left-unit-law-mul-ℤ (inr (inr x)))
      ＝ add-ℤ (inr (inr x)) zero-ℤ
        by ap (λ M → add-ℤ (inr (inr x)) M) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inr (inr x)))
        by right-unit-law-add-ℤ (inr (inr x))
      ＝ gcd-ℤ (inr (inr x)) zero-ℤ
        by
          inv
            ( is-id-is-gcd-zero-ℤ'
              { inr (inr x)}
              { gcd-ℤ (inr (inr x)) zero-ℤ}
              ( refl))
bezouts-lemma-ℤ (inr (inr x)) (inr (inr y)) =
  bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
```

Now that Bezout's Lemma has been established, we establish a few corollaries of
Bezout.

### If `x | y z` and `gcd-Z x y ＝ 1`, then `x | z`.

```agda
div-right-factor-coprime-ℤ :
  (x y z : ℤ) → (div-ℤ x (mul-ℤ y z)) → (gcd-ℤ x y ＝ one-ℤ) → div-ℤ x z
div-right-factor-coprime-ℤ x y z H K = pair (add-ℤ (mul-ℤ s z) (mul-ℤ t k)) eqn
  where
  bezout-triple :
    Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
  bezout-triple = bezouts-lemma-ℤ x y
  s : ℤ
  s = pr1 bezout-triple
  t : ℤ
  t = pr1 (pr2 bezout-triple)
  bezout-eqn : add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y
  bezout-eqn = pr2 (pr2 bezout-triple)
  k : ℤ
  k = pr1 H
  div-yz : mul-ℤ k x ＝ mul-ℤ y z
  div-yz = pr2 H
  eqn : mul-ℤ (add-ℤ (mul-ℤ s z) (mul-ℤ t k)) x ＝ z
  eqn =
    equational-reasoning
      mul-ℤ (add-ℤ (mul-ℤ s z) (mul-ℤ t k)) x
      ＝ add-ℤ (mul-ℤ (mul-ℤ s z) x) (mul-ℤ (mul-ℤ t k) x)
        by right-distributive-mul-add-ℤ (mul-ℤ s z) (mul-ℤ t k) x
      ＝ add-ℤ (mul-ℤ (mul-ℤ s x) z) (mul-ℤ (mul-ℤ t k) x)
        by ap (λ M → add-ℤ M (mul-ℤ (mul-ℤ t k) x))
        ( equational-reasoning
            mul-ℤ (mul-ℤ s z) x
            ＝ mul-ℤ s (mul-ℤ z x)
              by associative-mul-ℤ s z x
            ＝ mul-ℤ s (mul-ℤ x z)
              by ap (λ P → mul-ℤ s P) (commutative-mul-ℤ z x)
            ＝ mul-ℤ (mul-ℤ s x) z
              by inv (associative-mul-ℤ s x z))
      ＝ add-ℤ (mul-ℤ (mul-ℤ s x) z) (mul-ℤ (mul-ℤ t y) z)
        by ap (λ M → add-ℤ (mul-ℤ (mul-ℤ s x) z) M)
    ( equational-reasoning
        mul-ℤ (mul-ℤ t k) x
        ＝ mul-ℤ t (mul-ℤ k x)
          by associative-mul-ℤ t k x
        ＝ mul-ℤ t (mul-ℤ y z)
          by ap (λ P → mul-ℤ t P) div-yz
        ＝ mul-ℤ (mul-ℤ t y) z
          by inv (associative-mul-ℤ t y z))
    ＝ mul-ℤ (add-ℤ (mul-ℤ s x) (mul-ℤ t y)) z
      by inv (right-distributive-mul-add-ℤ (mul-ℤ s x) (mul-ℤ t y) z)
    ＝ mul-ℤ one-ℤ z
      by ap (λ M → mul-ℤ M z) (bezout-eqn ∙ K)
    ＝ z
      by left-unit-law-mul-ℤ z

div-right-factor-coprime-ℕ :
  (x y z : ℕ) → (div-ℕ x (mul-ℕ y z)) → (gcd-ℕ x y ＝ 1) → div-ℕ x z
div-right-factor-coprime-ℕ x y z H K =
  div-div-int-ℕ
    ( div-right-factor-coprime-ℤ
      ( int-ℕ x)
      ( int-ℕ y)
      ( int-ℕ z)
        ( tr (λ p → div-ℤ (int-ℕ x) p) (inv (mul-int-ℕ y z)) (div-int-div-ℕ H))
      ( eq-gcd-gcd-int-ℕ x y ∙ ap int-ℕ K))
```
