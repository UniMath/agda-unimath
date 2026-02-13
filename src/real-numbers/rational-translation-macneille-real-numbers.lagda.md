# Rational left translation on MacNeille real numbers

```agda
module real-numbers.rational-translation-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-located-macneille-real-numbers
open import real-numbers.addition-lower-dedekind-real-numbers
open import real-numbers.addition-macneille-real-numbers
open import real-numbers.inequalities-addition-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.raising-universe-levels-rational-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Translation laws

```agda
abstract opaque
  unfolding add-macneille-ℝ

  combine-left-add-two-macneille-real-ℚ :
    {l : Level} (p q : ℚ) (x : macneille-ℝ l) →
    add-macneille-ℝ
      ( located-macneille-real-ℚ p)
      ( add-macneille-ℝ (located-macneille-real-ℚ q) x) ＝
    add-macneille-ℝ (located-macneille-real-ℚ (p +ℚ q)) x
  combine-left-add-two-macneille-real-ℚ p q x =
    eq-eq-lower-real-macneille-ℝ
      ( add-macneille-ℝ
        ( located-macneille-real-ℚ p)
        ( add-macneille-ℝ (located-macneille-real-ℚ q) x))
      ( add-macneille-ℝ (located-macneille-real-ℚ (p +ℚ q)) x)
      ( ( inv
          ( associative-add-lower-ℝ
            ( lower-real-macneille-ℝ (macneille-real-ℚ p))
            ( lower-real-macneille-ℝ (macneille-real-ℚ q))
            ( lower-real-macneille-ℝ x))) ∙
        ( ap
          ( λ y → add-lower-ℝ y (lower-real-macneille-ℝ x))
          ( ap lower-real-macneille-ℝ (add-macneille-real-ℚ p q))))

  add-raise-macneille-real-ℚ :
    {l : Level} (p q : ℚ) →
    add-macneille-ℝ
      ( located-raise-macneille-ℝ l (located-macneille-real-ℚ p))
      ( raise-macneille-ℝ l (macneille-real-ℚ q)) ＝
    raise-macneille-ℝ l (macneille-real-ℚ (p +ℚ q))
  add-raise-macneille-real-ℚ {l} p q =
    add-raise-macneille-ℝ ∙ ap (raise-macneille-ℝ l) (add-macneille-real-ℚ p q)

  eq-right-translate-raise-macneille-real-ℚ :
    {l : Level} (q r : ℚ) →
    add-macneille-ℝ
      ( located-macneille-real-ℚ q)
      ( raise-macneille-ℝ l (macneille-real-ℚ r)) ＝
    raise-macneille-ℝ l (macneille-real-ℚ (q +ℚ r))
  eq-right-translate-raise-macneille-real-ℚ {l} q r =
    eq-sim-macneille-ℝ
      ( transitive-sim-macneille-ℝ _ _ _
        ( sim-eq-macneille-ℝ (add-raise-macneille-real-ℚ {l} q r))
        ( preserves-sim-add-macneille-ℝ
          { x = located-macneille-real-ℚ q}
          { x' = located-raise-macneille-ℝ l (located-macneille-real-ℚ q)}
          { y = raise-macneille-ℝ l (macneille-real-ℚ r)}
          { y' = raise-macneille-ℝ l (macneille-real-ℚ r)}
          ( sim-raise-macneille-ℝ l (macneille-real-ℚ q))
          ( refl-sim-macneille-ℝ (raise-macneille-ℝ l (macneille-real-ℚ r)))))

  eq-right-translate-raise-macneille-real-ℚ' :
    {l : Level} (q r : ℚ) →
    add-macneille-ℝ
      ( located-macneille-real-ℚ q)
      ( raise-macneille-real-ℚ l r) ＝
    raise-macneille-real-ℚ l (q +ℚ r)
  eq-right-translate-raise-macneille-real-ℚ' {l} q r =
    ( ap
      ( add-macneille-ℝ (located-macneille-real-ℚ q))
      ( eq-raise-macneille-real-ℚ-raise-macneille-ℝ r)) ∙
    ( eq-right-translate-raise-macneille-real-ℚ {l} q r) ∙
    ( inv (eq-raise-macneille-real-ℚ-raise-macneille-ℝ (q +ℚ r)))

  preserves-leq-left-add-raise-macneille-real-ℚ :
    {l : Level} (x : macneille-ℝ l) (p q : ℚ) →
    leq-ℚ p q →
    leq-macneille-ℝ
      ( add-macneille-ℝ (raise-located-macneille-real-ℚ l p) x)
      ( add-macneille-ℝ (raise-located-macneille-real-ℚ l q) x)
  preserves-leq-left-add-raise-macneille-real-ℚ {l} x p q p≤q =
    preserves-leq-left-add-macneille-ℝ
      ( raise-located-macneille-real-ℚ l p)
      ( raise-located-macneille-real-ℚ l q)
      ( x)
      ( leq-raise-macneille-real-ℚ p q p≤q)
```

```agda
abstract
  left-inverse-right-translate-macneille-real-ℚ :
    {l : Level} (q : ℚ) (x : macneille-ℝ l) →
    add-macneille-ℝ
      ( located-macneille-real-ℚ (neg-ℚ q))
      ( add-macneille-ℝ (located-macneille-real-ℚ q) x) ＝
    x
  left-inverse-right-translate-macneille-real-ℚ q x =
    ( combine-left-add-two-macneille-real-ℚ (neg-ℚ q) q x) ∙
    ( ap
      ( λ z → add-macneille-ℝ z x)
      ( ap located-macneille-real-ℚ (left-inverse-law-add-ℚ q))) ∙
    ( left-unit-law-add-macneille-ℝ x)

  right-inverse-right-translate-macneille-real-ℚ :
    {l : Level} (q : ℚ) (x : macneille-ℝ l) →
    add-macneille-ℝ
      ( located-macneille-real-ℚ q)
      ( add-macneille-ℝ
        ( located-macneille-real-ℚ (neg-ℚ q))
        ( x)) ＝
    x
  right-inverse-right-translate-macneille-real-ℚ q x =
    ( combine-left-add-two-macneille-real-ℚ q (neg-ℚ q) x) ∙
    ( ap
      ( λ z → add-macneille-ℝ z x)
      ( ap located-macneille-real-ℚ (right-inverse-law-add-ℚ q))) ∙
    ( left-unit-law-add-macneille-ℝ x)
```

## Reflection of order

```agda
abstract
  reflects-leq-right-add-macneille-real-ℚ :
    {l : Level} (q : ℚ) (x y : macneille-ℝ l) →
    leq-macneille-ℝ
      ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
      ( add-macneille-ℝ (located-macneille-real-ℚ q) y) →
    leq-macneille-ℝ x y
  reflects-leq-right-add-macneille-real-ℚ q x y q+x≤q+y =
    binary-tr
      leq-macneille-ℝ
      ( left-inverse-right-translate-macneille-real-ℚ q x)
      ( left-inverse-right-translate-macneille-real-ℚ q y)
      ( preserves-leq-right-add-macneille-ℝ
        ( located-macneille-real-ℚ (neg-ℚ q))
        ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
        ( add-macneille-ℝ (located-macneille-real-ℚ q) y)
        ( q+x≤q+y))

  leq-transpose-right-add-macneille-real-ℚ :
    {l : Level} (q : ℚ) (x y : macneille-ℝ l) →
    leq-macneille-ℝ
      ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
      ( y) →
    leq-macneille-ℝ
      ( x)
      ( add-macneille-ℝ (located-macneille-real-ℚ (neg-ℚ q)) y)
  leq-transpose-right-add-macneille-real-ℚ q x y q+x≤y =
    reflects-leq-right-add-macneille-real-ℚ q x
      ( add-macneille-ℝ (located-macneille-real-ℚ (neg-ℚ q)) y)
      ( tr
        ( leq-macneille-ℝ (add-macneille-ℝ (located-macneille-real-ℚ q) x))
        ( inv (right-inverse-right-translate-macneille-real-ℚ q y))
        ( q+x≤y))

iff-translate-right-leq-macneille-real-ℚ :
  {l : Level} (q : ℚ) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y ↔
  leq-macneille-ℝ
    ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
    ( add-macneille-ℝ (located-macneille-real-ℚ q) y)
pr1 (iff-translate-right-leq-macneille-real-ℚ q x y) =
  preserves-leq-right-add-macneille-ℝ (located-macneille-real-ℚ q) x y
pr2 (iff-translate-right-leq-macneille-real-ℚ q x y) =
  reflects-leq-right-add-macneille-real-ℚ q x y
```

## Positive translation contradiction lemmas

```agda
module _
  {l : Level} (x : macneille-ℝ l) (q : ℚ) (0<q : le-ℚ zero-ℚ q)
  where

  abstract
    leq-rational-multiple-right-translate-macneille-real-ℚ :
      (q+x≤x :
        leq-macneille-ℝ
          ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
          ( x)) →
      (n : ℕ) →
      leq-macneille-ℝ
        ( add-macneille-ℝ
          ( located-macneille-real-ℚ (rational-ℕ n *ℚ q))
          ( x))
        ( x)
    leq-rational-multiple-right-translate-macneille-real-ℚ q+x≤x zero-ℕ =
      tr
        ( λ y → leq-macneille-ℝ y x)
        ( inv
          ( ap
            ( λ r → add-macneille-ℝ (located-macneille-real-ℚ r) x)
            ( left-zero-law-mul-ℚ q)))
        ( tr
          ( λ y → leq-macneille-ℝ y x)
          ( inv (left-unit-law-add-macneille-ℝ x))
          ( refl-leq-macneille-ℝ x))
    leq-rational-multiple-right-translate-macneille-real-ℚ q+x≤x (succ-ℕ n) =
      tr
        ( λ y → leq-macneille-ℝ y x)
        ( ap
          ( λ r → add-macneille-ℝ (located-macneille-real-ℚ r) x)
          ( eq-succ-mul-rational-ℕ-right-ℚ n q))
        ( tr
          ( λ y → leq-macneille-ℝ y x)
          ( combine-left-add-two-macneille-real-ℚ q (rational-ℕ n *ℚ q) x)
          ( transitive-leq-macneille-ℝ
            ( add-macneille-ℝ
              ( located-macneille-real-ℚ q)
              ( add-macneille-ℝ
                ( located-macneille-real-ℚ (rational-ℕ n *ℚ q))
                ( x)))
            ( add-macneille-ℝ (located-macneille-real-ℚ q) x)
            ( x)
            ( q+x≤x)
            ( preserves-leq-right-add-macneille-ℝ
              ( located-macneille-real-ℚ q)
              ( add-macneille-ℝ
                ( located-macneille-real-ℚ (rational-ℕ n *ℚ q))
                ( x))
              ( x)
              ( leq-rational-multiple-right-translate-macneille-real-ℚ
                ( q+x≤x)
                ( n)))))

    not-leq-right-translate-positive-macneille-real-ℚ :
      ¬ leq-macneille-ℝ (add-macneille-ℝ (located-macneille-real-ℚ q) x) x
    not-leq-right-translate-positive-macneille-real-ℚ q+x≤x =
      apply-universal-property-trunc-Prop
        ( exists-lesser-rational-macneille-ℝ x)
        ( empty-Prop)
        ( λ (p , p<x) →
          apply-universal-property-trunc-Prop
            ( exists-greater-rational-macneille-ℝ x)
            ( empty-Prop)
            ( λ (r , x<r) →
              let
                (n , r-p<n⋅q) =
                  bound-archimedean-property-ℚ q
                    ( r -ℚ p)
                    ( is-positive-le-zero-ℚ 0<q)

                r≤p+n⋅q =
                  tr
                    ( λ t →
                      leq-ℚ t ( p +ℚ (rational-ℕ n *ℚ q)))
                    ( is-identity-right-conjugation-add-ℚ p r)
                    ( preserves-leq-right-add-ℚ
                      ( p)
                      ( r -ℚ p)
                      ( rational-ℕ n *ℚ q)
                      ( leq-le-ℚ r-p<n⋅q))

                p+n⋅q≤x =
                  tr
                    ( λ y → leq-macneille-ℝ y x)
                    ( add-macneille-real-ℚ (rational-ℕ n *ℚ q) p ∙
                      ( ap
                        ( macneille-real-ℚ)
                        ( commutative-add-ℚ (rational-ℕ n *ℚ q) p)))
                    ( transitive-leq-macneille-ℝ
                      ( add-macneille-ℝ
                        ( located-macneille-real-ℚ (rational-ℕ n *ℚ q))
                        ( macneille-real-ℚ p))
                      ( add-macneille-ℝ
                        ( located-macneille-real-ℚ (rational-ℕ n *ℚ q))
                        ( x))
                      ( x)
                      ( leq-rational-multiple-right-translate-macneille-real-ℚ
                        ( q+x≤x)
                        ( n))
                      ( preserves-leq-right-add-macneille-ℝ
                        ( located-macneille-real-ℚ
                          ( rational-ℕ n *ℚ q))
                        ( macneille-real-ℚ p)
                        ( x)
                        ( leq-le-macneille-ℝ p<x)))

                p+n⋅q<r : le-ℚ (p +ℚ (rational-ℕ n *ℚ q)) r
                p+n⋅q<r =
                  reflects-le-macneille-real-ℚ
                    ( concatenate-leq-le-macneille-ℝ
                      ( macneille-real-ℚ (p +ℚ (rational-ℕ n *ℚ q)))
                      ( x)
                      ( macneille-real-ℚ r)
                      ( p+n⋅q≤x)
                      ( x<r))
              in
              not-leq-le-ℚ (p +ℚ (rational-ℕ n *ℚ q)) r p+n⋅q<r r≤p+n⋅q))
```
