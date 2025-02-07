# Raising the universe levels of real numbers

```agda
module real-numbers.raising-universe-levels-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

Real numbers have designated universe levels. For any real number, we can
construct an equivalent real number in any higher universe.

```agda
module _
  {l1 : Level}
  (l : Level)
  (x : ℝ l1)
  where

  lower-cut-raise-ℝ : subtype (l1 ⊔ l) ℚ
  lower-cut-raise-ℝ = raise-subtype l (lower-cut-ℝ x)

  is-in-lower-cut-raise-ℝ : ℚ → UU (l1 ⊔ l)
  is-in-lower-cut-raise-ℝ = is-in-subtype lower-cut-raise-ℝ

  upper-cut-raise-ℝ : subtype (l1 ⊔ l) ℚ
  upper-cut-raise-ℝ = raise-subtype l (upper-cut-ℝ x)

  is-in-upper-cut-raise-ℝ : ℚ → UU (l1 ⊔ l)
  is-in-upper-cut-raise-ℝ = is-in-subtype upper-cut-raise-ℝ

  is-inhabited-lower-cut-raise-ℝ : exists ℚ lower-cut-raise-ℝ
  is-inhabited-lower-cut-raise-ℝ =
    elim-exists
      (∃ ℚ lower-cut-raise-ℝ)
      (λ q q∈L → intro-exists q (map-raise q∈L))
      (is-inhabited-lower-cut-ℝ x)

  is-inhabited-upper-cut-raise-ℝ : exists ℚ upper-cut-raise-ℝ
  is-inhabited-upper-cut-raise-ℝ =
    elim-exists
      ( ∃ ℚ upper-cut-raise-ℝ)
      ( λ q q∈U → intro-exists q (map-raise q∈U))
      ( is-inhabited-upper-cut-ℝ x)

  is-rounded-lower-cut-raise-ℝ :
    (q : ℚ) →
    is-in-lower-cut-raise-ℝ q ↔
    exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-raise-ℝ r)
  pr1 (is-rounded-lower-cut-raise-ℝ q) (map-raise q∈L) =
    elim-exists
      ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-raise-ℝ r))
      ( λ r (q<r , r∈L) → intro-exists r (q<r , map-raise r∈L))
      ( forward-implication (is-rounded-lower-cut-ℝ x q) q∈L)
  pr2 (is-rounded-lower-cut-raise-ℝ q) =
    elim-exists
      ( lower-cut-raise-ℝ q)
      ( λ r (q<r , r∈L) →
        map-raise
          ( backward-implication
            ( is-rounded-lower-cut-ℝ x q)
            ( intro-exists r (q<r , map-inv-raise r∈L))))

  is-rounded-upper-cut-raise-ℝ :
    (r : ℚ) →
    is-in-upper-cut-raise-ℝ r ↔
    exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-raise-ℝ q)
  pr1 (is-rounded-upper-cut-raise-ℝ r) (map-raise r∈U) =
    elim-exists
      ( ∃ ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-raise-ℝ q))
      ( λ q (q<r , q∈U) → intro-exists q (q<r , map-raise q∈U))
      ( forward-implication (is-rounded-upper-cut-ℝ x r) r∈U)
  pr2 (is-rounded-upper-cut-raise-ℝ r) =
    elim-exists
      ( upper-cut-raise-ℝ r)
      ( λ q (q<r , q∈U) →
        map-raise
          ( backward-implication
            ( is-rounded-upper-cut-ℝ x r)
            ( intro-exists q (q<r , map-inv-raise q∈U))))

  is-disjoint-cut-raise-ℝ :
    (q : ℚ) → ¬ (is-in-lower-cut-raise-ℝ q × is-in-upper-cut-raise-ℝ q)
  is-disjoint-cut-raise-ℝ q (map-raise q∈L , map-raise q∈U) =
    is-disjoint-cut-ℝ x q (q∈L , q∈U)

  is-located-lower-upper-cut-raise-ℝ :
    (q r : ℚ) →
    le-ℚ q r →
    type-disjunction-Prop (lower-cut-raise-ℝ q) (upper-cut-raise-ℝ r)
  is-located-lower-upper-cut-raise-ℝ q r q<r =
    elim-disjunction
      ( lower-cut-raise-ℝ q ∨ upper-cut-raise-ℝ r)
      ( inl-disjunction ∘ map-raise)
      ( inr-disjunction ∘ map-raise)
      ( is-located-lower-upper-cut-ℝ x q r q<r)

  raise-ℝ : ℝ (l1 ⊔ l)
  raise-ℝ =
    real-dedekind-cut
      ( lower-cut-raise-ℝ)
      ( upper-cut-raise-ℝ)
      ( (is-inhabited-lower-cut-raise-ℝ , is-inhabited-upper-cut-raise-ℝ) ,
        (is-rounded-lower-cut-raise-ℝ , is-rounded-upper-cut-raise-ℝ) ,
        is-disjoint-cut-raise-ℝ ,
        is-located-lower-upper-cut-raise-ℝ)
```

## Similarity across universe levels

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  sim-ℝ-Prop : Prop (l1 ⊔ l2)
  sim-ℝ-Prop =
    leq-prop-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) ∧
    leq-prop-subtype (lower-cut-ℝ y) (lower-cut-ℝ x)

  sim-ℝ : UU (l1 ⊔ l2)
  sim-ℝ = type-Prop sim-ℝ-Prop
```

### Similarity is reflexive

```agda
refl-sim-ℝ : {l : Level} → (x : ℝ l) → sim-ℝ x x
pr1 (refl-sim-ℝ x) = refl-leq-subtype (lower-cut-ℝ x)
pr2 (refl-sim-ℝ x) = refl-leq-subtype (lower-cut-ℝ x)
```

### Similarity is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  transitive-sim-ℝ : sim-ℝ y z → sim-ℝ x y → sim-ℝ x z
  pr1 (transitive-sim-ℝ y~z x~y) =
    transitive-leq-subtype
      ( lower-cut-ℝ x)
      ( lower-cut-ℝ y)
      ( lower-cut-ℝ z)
      ( pr1 y~z)
      ( pr1 x~y)
