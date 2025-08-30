# The maximum of finite families of real numbers

```agda
module real-numbers.maximum-finite-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences

open import logic.functoriality-existential-quantification

open import order-theory.join-semilattices
open import order-theory.joins-finite-families-join-semilattices
open import order-theory.upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.suprema-families-real-numbers

open import univalent-combinatorics.counting
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="inhabited finite family, Dedekind real numbers" Agda=max-finite-family-ℝ WD="maximum" WDID=Q10578722}}
of a family of [Dedekind real numbers](real-numbers.dedekind-real-numbers.md)
indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their [least upper bound](order-theory.least-upper-bounds-large-posets.md).

## Definition

### The maximum of a nonempty sequence of real numbers

```agda
module _
  {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n))
  where

  max-fin-sequence-ℝ : ℝ l
  max-fin-sequence-ℝ =
    join-fin-sequence-type-Order-Theoretic-Join-Semilattice
      ( ℝ-Order-Theoretic-Join-Semilattice l)
      ( n)
      ( x)
```

### The maximum of a counted, inhabited family of real numbers

```agda
module _
  {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I)
  (x : I → ℝ l2)
  where

  max-counted-family-ℝ : ℝ l2
  max-counted-family-ℝ =
    join-counted-family-type-Order-Theoretic-Join-Semilattice
      ( ℝ-Order-Theoretic-Join-Semilattice l2)
      ( |I|)
      ( cI)
      ( x)
```

### The maximum of an inhabited finite family of real numbers

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (f : type-Inhabited-Finite-Type I → ℝ l2)
  where

  max-finite-family-ℝ : ℝ l2
  max-finite-family-ℝ =
    join-inhabited-finite-family-Order-Theoretic-Join-Semilattice
      ( ℝ-Order-Theoretic-Join-Semilattice l2)
      ( I)
      ( f)
```

## Properties

### The maximum of a sequence is its supremum

```agda
abstract
  is-upper-bound-max-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-upper-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( max-fin-sequence-ℝ n x)
  is-upper-bound-max-fin-sequence-ℝ zero-ℕ x (inr star) =
    refl-leq-ℝ (x (inr star))
  is-upper-bound-max-fin-sequence-ℝ (succ-ℕ n) x (inr star) =
    leq-right-max-ℝ _ _
  is-upper-bound-max-fin-sequence-ℝ (succ-ℕ n) x (inl i) =
    transitive-leq-ℝ
      ( x (inl i))
      ( max-fin-sequence-ℝ n (x ∘ inl))
      ( max-fin-sequence-ℝ (succ-ℕ n) x)
      ( leq-left-max-ℝ _ _)
      ( is-upper-bound-max-fin-sequence-ℝ n (x ∘ inl) i)

  is-approximated-below-max-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-approximated-below-family-ℝ x (max-fin-sequence-ℝ n x)
  is-approximated-below-max-fin-sequence-ℝ zero-ℕ x ε =
    intro-exists
      ( inr star)
      ( le-diff-real-ℝ⁺ (x (inr star)) (positive-real-ℚ⁺ ε))
  is-approximated-below-max-fin-sequence-ℝ (succ-ℕ n) x ε =
    let
      (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
      motive =
        ∃
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( λ i →
            le-ℝ-Prop (max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε) (x i))
      max-ε₁-ε₂=max-ε =
        equational-reasoning
          max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε₁ -ℝ real-ℚ⁺ ε₂
          ＝
            max-fin-sequence-ℝ (succ-ℕ n) x +ℝ
            (neg-ℝ (real-ℚ⁺ ε₁) -ℝ real-ℚ⁺ ε₂)
            by associative-add-ℝ _ _ _
          ＝
            max-fin-sequence-ℝ (succ-ℕ n) x -ℝ (real-ℚ⁺ ε₁ +ℝ real-ℚ⁺ ε₂)
            by ap-add-ℝ refl (inv (distributive-neg-add-ℝ _ _))
          ＝ max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε
            by ap-diff-ℝ refl (add-real-ℚ _ _ ∙ ap real-ℚ⁺ ε₁+ε₂=ε)
    in
      elim-disjunction
        ( motive)
        ( λ max-ε₁<max-x-inl →
          map-exists
            ( _)
            ( inl)
            ( λ i max-x-inl-ε₂<xᵢ →
              transitive-le-ℝ
                ( max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε)
                ( max-fin-sequence-ℝ n (x ∘ inl) -ℝ real-ℚ⁺ ε₂)
                ( x (inl i))
                ( max-x-inl-ε₂<xᵢ)
                ( tr
                  ( λ y → le-ℝ y (max-fin-sequence-ℝ n (x ∘ inl) -ℝ real-ℚ⁺ ε₂))
                  ( max-ε₁-ε₂=max-ε)
                  ( preserves-le-diff-ℝ
                    ( real-ℚ⁺ ε₂)
                    ( max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε₁)
                    ( max-fin-sequence-ℝ n (x ∘ inl)) max-ε₁<max-x-inl)))
            ( is-approximated-below-max-fin-sequence-ℝ n (x ∘ inl) ε₂))
        ( λ max-ε₁<xₙ →
          intro-exists
            ( inr star)
            ( transitive-le-ℝ
              ( max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε)
              ( max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε₁)
              ( x (inr star))
              ( max-ε₁<xₙ)
              ( tr
                ( λ y → le-ℝ y (max-fin-sequence-ℝ (succ-ℕ n) x -ℝ real-ℚ⁺ ε₁))
                ( max-ε₁-ε₂=max-ε)
                ( le-diff-real-ℝ⁺ _ (positive-real-ℚ⁺ ε₂)))))
        ( approximate-below-max-ℝ
          ( max-fin-sequence-ℝ n (x ∘ inl))
          ( x (inr star))
          ( ε₁))

  is-supremum-max-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-supremum-family-ℝ x (max-fin-sequence-ℝ n x)
  pr1 (is-supremum-max-fin-sequence-ℝ n x) =
    is-upper-bound-max-fin-sequence-ℝ n x
  pr2 (is-supremum-max-fin-sequence-ℝ n x) =
    is-approximated-below-max-fin-sequence-ℝ n x
```

### The maximum of a counted family is its supremum

```agda
abstract
  is-upper-bound-max-counted-family-ℝ :
    {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I) →
    (x : I → ℝ l2) →
    is-upper-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( max-counted-family-ℝ |I| cI x)
  is-upper-bound-max-counted-family-ℝ |I| cI@(zero-ℕ , _) _ =
    ex-falso
      ( is-nonempty-is-inhabited
        ( |I|)
        ( is-empty-is-zero-number-of-elements-count cI refl))
  is-upper-bound-max-counted-family-ℝ |I| cI@(succ-ℕ n , Fin-sn≃I) x i =
    tr
      ( λ j → leq-ℝ (x j) (max-counted-family-ℝ |I| cI x))
      ( is-section-map-inv-equiv Fin-sn≃I i)
      ( is-upper-bound-max-fin-sequence-ℝ
        ( n)
        ( x ∘ map-equiv Fin-sn≃I)
        ( map-inv-equiv Fin-sn≃I i))

  is-approximated-below-max-counted-family-ℝ :
    {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I) →
    (x : I → ℝ l2) →
    is-approximated-below-family-ℝ
      ( x)
      ( max-counted-family-ℝ |I| cI x)
  is-approximated-below-max-counted-family-ℝ |I| cI@(zero-ℕ , _) _ =
    ex-falso
      ( is-nonempty-is-inhabited
        ( |I|)
        ( is-empty-is-zero-number-of-elements-count cI refl))
  is-approximated-below-max-counted-family-ℝ |I| cI@(succ-ℕ n , Fin-sn≃I) x ε =
    map-exists _
      ( map-equiv Fin-sn≃I)
      ( λ i → id)
      ( is-approximated-below-max-fin-sequence-ℝ n (x ∘ map-equiv Fin-sn≃I) ε)

  is-supremum-max-counted-family-ℝ :
    {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I) →
    (x : I → ℝ l2) →
    is-supremum-family-ℝ x (max-counted-family-ℝ |I| cI x)
  pr1 (is-supremum-max-counted-family-ℝ |I| cI x) =
    is-upper-bound-max-counted-family-ℝ |I| cI x
  pr2 (is-supremum-max-counted-family-ℝ |I| cI x) =
    is-approximated-below-max-counted-family-ℝ |I| cI x
```

### The maximum of a finite family is its supremum

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (x : type-Inhabited-Finite-Type I → ℝ l2)
  where

  abstract
    is-supremum-max-finite-family-ℝ :
      is-supremum-family-ℝ x (max-finite-family-ℝ I x)
    is-supremum-max-finite-family-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-supremum-prop-family-ℝ x (max-finite-family-ℝ I x))
      in do
        cI ← is-finite-Inhabited-Finite-Type I
        inv-tr
          ( is-supremum-family-ℝ x)
          ( eq-join-inhabited-finite-family-join-counted-family-Order-Theoretic-Join-Semilattice
            ( ℝ-Order-Theoretic-Join-Semilattice l2)
            ( I)
            ( cI)
            ( x))
          ( is-supremum-max-counted-family-ℝ
            ( is-inhabited-type-Inhabited-Finite-Type I)
            ( cI)
            ( x))

    is-upper-bound-max-finite-family-ℝ :
      is-upper-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( max-finite-family-ℝ I x)
    is-upper-bound-max-finite-family-ℝ =
      is-upper-bound-is-supremum-family-ℝ
        ( x)
        ( max-finite-family-ℝ I x)
        ( is-supremum-max-finite-family-ℝ)

    is-approximated-below-max-finite-family-ℝ :
      is-approximated-below-family-ℝ
        ( x)
        ( max-finite-family-ℝ I x)
    is-approximated-below-max-finite-family-ℝ =
      is-approximated-below-is-supremum-family-ℝ
        ( x)
        ( max-finite-family-ℝ I x)
        ( is-supremum-max-finite-family-ℝ)
```
