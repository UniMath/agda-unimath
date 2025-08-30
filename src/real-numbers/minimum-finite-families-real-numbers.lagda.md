# The minimum of finite families of real numbers

```agda
module real-numbers.minimum-finite-families-real-numbers where
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

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.lower-bounds-large-posets
open import order-theory.meet-semilattices
open import order-theory.meets-finite-families-meet-semilattices

open import real-numbers.addition-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers

open import univalent-combinatorics.counting
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="inhabited finite family, Dedekind real numbers" Agda=min-finite-family-ℝ WD="minimum" WDID=Q10578722}}
of a family of [Dedekind real numbers](real-numbers.dedekind-real-numbers.md)
indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md).

## Definition

### The minimum of a nonempty sequence of real numbers

```agda
module _
  {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n))
  where

  min-fin-sequence-ℝ : ℝ l
  min-fin-sequence-ℝ =
    meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
      ( ℝ-Order-Theoretic-Meet-Semilattice l)
      ( n)
      ( x)
```

### The minimum of a counted, inhabited family of real numbers

```agda
module _
  {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I)
  (x : I → ℝ l2)
  where

  min-counted-family-ℝ : ℝ l2
  min-counted-family-ℝ =
    meet-counted-family-type-Order-Theoretic-Meet-Semilattice
      ( ℝ-Order-Theoretic-Meet-Semilattice l2)
      ( |I|)
      ( cI)
      ( x)
```

### The minimum of an inhabited finite family of real numbers

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (f : type-Inhabited-Finite-Type I → ℝ l2)
  where

  min-finite-family-ℝ : ℝ l2
  min-finite-family-ℝ =
    meet-inhabited-finite-family-Order-Theoretic-Meet-Semilattice
      ( ℝ-Order-Theoretic-Meet-Semilattice l2)
      ( I)
      ( f)
```

## Properties

### The minimum of a sequence is its infimum

```agda
abstract
  is-lower-bound-min-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-lower-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( min-fin-sequence-ℝ n x)
  is-lower-bound-min-fin-sequence-ℝ zero-ℕ x (inr star) =
    refl-leq-ℝ (x (inr star))
  is-lower-bound-min-fin-sequence-ℝ (succ-ℕ n) x (inr star) =
    leq-right-min-ℝ _ _
  is-lower-bound-min-fin-sequence-ℝ (succ-ℕ n) x (inl i) =
    transitive-leq-ℝ
      ( min-fin-sequence-ℝ (succ-ℕ n) x)
      ( min-fin-sequence-ℝ n (x ∘ inl))
      ( x (inl i))
      ( is-lower-bound-min-fin-sequence-ℝ n (x ∘ inl) i)
      ( leq-left-min-ℝ _ _)

  is-approximated-above-min-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-approximated-above-family-ℝ x (min-fin-sequence-ℝ n x)
  is-approximated-above-min-fin-sequence-ℝ zero-ℕ x ε =
    intro-exists
      ( inr star)
      ( le-left-add-real-ℝ⁺ (x (inr star)) (positive-real-ℚ⁺ ε))
  is-approximated-above-min-fin-sequence-ℝ (succ-ℕ n) x ε =
    let
      (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
      motive =
        ∃
          ( Fin (succ-ℕ (succ-ℕ n)))
          ( λ i →
            le-ℝ-Prop (x i) (min-fin-sequence-ℝ (succ-ℕ n) x +ℝ real-ℚ⁺ ε))
      min+ε₁+ε₂=min+ε =
        associative-add-ℝ _ _ _ ∙
        ap-add-ℝ refl (add-real-ℚ _ _ ∙ ap real-ℚ⁺ ε₁+ε₂=ε)
    in
      elim-disjunction
        ( motive)
        ( λ min-x-inl<min+ε₁ →
          map-exists _
            ( inl)
            ( λ i →
              transitive-le-ℝ
                ( x (inl i))
                ( min-fin-sequence-ℝ n (x ∘ inl) +ℝ real-ℚ⁺ ε₂)
                ( min-fin-sequence-ℝ (succ-ℕ n) x +ℝ real-ℚ⁺ ε)
                ( tr
                  ( le-ℝ (min-fin-sequence-ℝ n (x ∘ inl) +ℝ real-ℚ⁺ ε₂))
                  ( min+ε₁+ε₂=min+ε)
                  ( preserves-le-right-add-ℝ
                    ( real-ℚ⁺ ε₂)
                    ( _)
                    ( _)
                    ( min-x-inl<min+ε₁))))
            ( is-approximated-above-min-fin-sequence-ℝ n (x ∘ inl) ε₂))
        ( λ xₙ<min+ε₁ →
          intro-exists
            ( inr star)
            ( transitive-le-ℝ
              ( x (inr star))
              ( min-fin-sequence-ℝ (succ-ℕ n) x +ℝ real-ℚ⁺ ε₁)
              ( min-fin-sequence-ℝ (succ-ℕ n) x +ℝ real-ℚ⁺ ε)
              ( tr
                ( le-ℝ (min-fin-sequence-ℝ (succ-ℕ n) x +ℝ real-ℚ⁺ ε₁))
                ( min+ε₁+ε₂=min+ε)
                ( le-left-add-real-ℝ⁺ _ (positive-real-ℚ⁺ ε₂)))
              ( xₙ<min+ε₁)))
        ( approximate-above-min-ℝ
          ( min-fin-sequence-ℝ n (x ∘ inl))
          ( x (inr star))
          ( ε₁))

  is-infimum-min-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-infimum-family-ℝ x (min-fin-sequence-ℝ n x)
  pr1 (is-infimum-min-fin-sequence-ℝ n x) =
    is-lower-bound-min-fin-sequence-ℝ n x
  pr2 (is-infimum-min-fin-sequence-ℝ n x) =
    is-approximated-above-min-fin-sequence-ℝ n x
```

### The minimum of a counted family is its infimum

```agda
abstract
  is-lower-bound-min-counted-family-ℝ :
    {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I) →
    (x : I → ℝ l2) →
    is-lower-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( min-counted-family-ℝ |I| cI x)
  is-lower-bound-min-counted-family-ℝ |I| cI@(zero-ℕ , _) _ =
    ex-falso
      ( is-nonempty-is-inhabited
        ( |I|)
        ( is-empty-is-zero-number-of-elements-count cI refl))
  is-lower-bound-min-counted-family-ℝ |I| cI@(succ-ℕ n , Fin-sn≃I) x i =
    tr
      ( λ j → leq-ℝ (min-counted-family-ℝ |I| cI x) (x j))
      ( is-section-map-inv-equiv Fin-sn≃I i)
      ( is-lower-bound-min-fin-sequence-ℝ
        ( n)
        ( x ∘ map-equiv Fin-sn≃I)
        ( map-inv-equiv Fin-sn≃I i))

  is-approximated-above-min-counted-family-ℝ :
    {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I) →
    (x : I → ℝ l2) →
    is-approximated-above-family-ℝ
      ( x)
      ( min-counted-family-ℝ |I| cI x)
  is-approximated-above-min-counted-family-ℝ |I| cI@(zero-ℕ , _) _ =
    ex-falso
      ( is-nonempty-is-inhabited
        ( |I|)
        ( is-empty-is-zero-number-of-elements-count cI refl))
  is-approximated-above-min-counted-family-ℝ |I| cI@(succ-ℕ n , Fin-sn≃I) x ε =
    map-exists _
      ( map-equiv Fin-sn≃I)
      ( λ i → id)
      ( is-approximated-above-min-fin-sequence-ℝ n (x ∘ map-equiv Fin-sn≃I) ε)

  is-infimum-min-counted-family-ℝ :
    {l1 l2 : Level} {I : UU l1} (|I| : is-inhabited I) (cI : count I) →
    (x : I → ℝ l2) →
    is-infimum-family-ℝ x (min-counted-family-ℝ |I| cI x)
  pr1 (is-infimum-min-counted-family-ℝ |I| cI x) =
    is-lower-bound-min-counted-family-ℝ |I| cI x
  pr2 (is-infimum-min-counted-family-ℝ |I| cI x) =
    is-approximated-above-min-counted-family-ℝ |I| cI x
```

### The minimum of a finite family is its infimum

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (x : type-Inhabited-Finite-Type I → ℝ l2)
  where

  abstract
    is-infimum-min-finite-family-ℝ :
      is-infimum-family-ℝ x (min-finite-family-ℝ I x)
    is-infimum-min-finite-family-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-infimum-prop-family-ℝ x (min-finite-family-ℝ I x))
      in do
        cI ← is-finite-Inhabited-Finite-Type I
        inv-tr
          ( is-infimum-family-ℝ x)
          ( eq-meet-inhabited-finite-family-meet-counted-family-Order-Theoretic-Meet-Semilattice
            ( ℝ-Order-Theoretic-Meet-Semilattice l2)
            ( I)
            ( cI)
            ( x))
          ( is-infimum-min-counted-family-ℝ
            ( is-inhabited-type-Inhabited-Finite-Type I)
            ( cI)
            ( x))

    is-lower-bound-min-finite-family-ℝ :
      is-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( min-finite-family-ℝ I x)
    is-lower-bound-min-finite-family-ℝ =
      is-lower-bound-is-infimum-family-ℝ
        ( x)
        ( min-finite-family-ℝ I x)
        ( is-infimum-min-finite-family-ℝ)

    is-approximated-above-min-finite-family-ℝ :
      is-approximated-above-family-ℝ
        ( x)
        ( min-finite-family-ℝ I x)
    is-approximated-above-min-finite-family-ℝ =
      is-approximated-above-is-infimum-family-ℝ
        ( x)
        ( min-finite-family-ℝ I x)
        ( is-infimum-min-finite-family-ℝ)
```

### The minimum of a finite family is its greatest lower bound

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (x : type-Inhabited-Finite-Type I → ℝ l2)
  where

  abstract
    is-greatest-lower-bound-min-finite-family-ℝ :
      is-greatest-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( min-finite-family-ℝ I x)
    is-greatest-lower-bound-min-finite-family-ℝ =
      is-greatest-lower-bound-is-infimum-family-ℝ
        ( x)
        ( min-finite-family-ℝ I x)
        ( is-infimum-min-finite-family-ℝ I x)
```
