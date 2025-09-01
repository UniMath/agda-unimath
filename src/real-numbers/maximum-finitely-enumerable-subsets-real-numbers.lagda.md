# The maximum of finitely enumerable subsets of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-finitely-enumerable-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.finitely-enumerable-subsets-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-finite-families-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.suprema-families-real-numbers

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="finitely enumerable subset of Dedekind real numbers" Agda=max-inhabited-finitely-enumerable-subset-ℝ WD="maximum" WDID=Q10578722}}
of a
[finitely enumerable subset of the real numbers](real-numbers.finitely-enumerable-subsets-real-numbers.md)
is their [supremum](real-numbers.suprema-families-real-numbers.md).

## Subsets with finite enumerations

### Definition

```agda
opaque
  max-is-inhabited-finite-enumeration-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) →
    finite-enumeration-subtype S → is-inhabited-subtype S →
    ℝ l2
  max-is-inhabited-finite-enumeration-subset-ℝ S eS@(zero-ℕ , _) |S| =
    ex-falso
      ( is-nonempty-is-inhabited
        ( |S|)
        ( is-empty-is-zero-finite-enumeration
          ( eS)
          ( refl)))
  max-is-inhabited-finite-enumeration-subset-ℝ
    S eS@(succ-ℕ n , Fin-sn↠S) |S| =
      max-fin-sequence-ℝ n (inclusion-subset-ℝ S ∘ map-surjection Fin-sn↠S)
```

### Properties

#### The maximum is an upper bound

```agda
opaque
  unfolding max-is-inhabited-finite-enumeration-subset-ℝ

  is-upper-bound-max-is-inhabited-finite-enumeration-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) →
    (eS : finite-enumeration-subtype S) (|S| : is-inhabited-subtype S) →
    is-upper-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( inclusion-subset-ℝ S)
      ( max-is-inhabited-finite-enumeration-subset-ℝ S eS |S|)
  is-upper-bound-max-is-inhabited-finite-enumeration-subset-ℝ
    S eS@(zero-ℕ , _) |S| =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |S|)
          ( is-empty-is-zero-finite-enumeration
            ( eS)
            ( refl)))
  is-upper-bound-max-is-inhabited-finite-enumeration-subset-ℝ
    S eS@(succ-ℕ n , Fin-sn↠S) |S| (s , s∈S) =
      let
        open
          do-syntax-trunc-Prop
            ( leq-ℝ-Prop
              ( s)
              ( max-is-inhabited-finite-enumeration-subset-ℝ S eS |S|))
      in do
        (i , fi=s) ← is-surjective-map-surjection Fin-sn↠S (s , s∈S)
        tr
          ( λ x →
            leq-ℝ
              ( inclusion-subset-ℝ S x)
              ( max-is-inhabited-finite-enumeration-subset-ℝ S eS |S|))
          ( fi=s)
          ( is-upper-bound-max-fin-sequence-ℝ
            ( n)
            ( inclusion-subset-ℝ S ∘ map-surjection Fin-sn↠S)
            ( i))
```

#### The maximum is approximated below

```agda
opaque
  unfolding max-is-inhabited-finite-enumeration-subset-ℝ

  is-approximated-below-max-is-inhabited-finite-enumeration-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) →
    (eS : finite-enumeration-subtype S) (|S| : is-inhabited-subtype S) →
    is-approximated-below-family-ℝ
      ( inclusion-subset-ℝ S)
      ( max-is-inhabited-finite-enumeration-subset-ℝ S eS |S|)
  is-approximated-below-max-is-inhabited-finite-enumeration-subset-ℝ
    S eS@(zero-ℕ , _) |S| _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |S|)
          ( is-empty-is-zero-finite-enumeration
            ( eS)
            ( refl)))
  is-approximated-below-max-is-inhabited-finite-enumeration-subset-ℝ
    S (succ-ℕ n , Fin-sn↠S) |S| ε =
      map-exists _
        ( map-surjection Fin-sn↠S)
        ( λ _ → id)
        ( is-approximated-below-max-fin-sequence-ℝ
          ( n)
          ( inclusion-subset-ℝ S ∘ map-surjection Fin-sn↠S)
          ( ε))
```

#### The maximum is a supremum

```agda
abstract
  is-supremum-max-is-inhabited-finite-enumeration-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) →
    (eS : finite-enumeration-subtype S) (|S| : is-inhabited-subtype S) →
    is-supremum-subset-ℝ
      ( S)
      ( max-is-inhabited-finite-enumeration-subset-ℝ S eS |S|)
  is-supremum-max-is-inhabited-finite-enumeration-subset-ℝ S eS |S| =
    ( is-upper-bound-max-is-inhabited-finite-enumeration-subset-ℝ S eS |S| ,
      is-approximated-below-max-is-inhabited-finite-enumeration-subset-ℝ
        ( S)
        ( eS)
        ( |S|))
```

#### Inhabited subsets of ℝ with finite enumerations have a supremum

```agda
has-supremum-is-inhabited-finite-enumeration-subset-ℝ :
  {l1 l2 : Level} → (S : subset-ℝ l1 l2) →
  (eS : finite-enumeration-subtype S) (|S| : is-inhabited-subtype S) →
  has-supremum-subset-ℝ S l2
has-supremum-is-inhabited-finite-enumeration-subset-ℝ S eS |S| =
  ( max-is-inhabited-finite-enumeration-subset-ℝ S eS |S| ,
    is-supremum-max-is-inhabited-finite-enumeration-subset-ℝ S eS |S|)
```

## Finitely enumerable subsets of ℝ

### Definition

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    has-supremum-inhabited-finitely-enumerable-subset-ℝ :
      has-supremum-subset-ℝ (subset-finitely-enumerable-subset-ℝ S) l2
    has-supremum-inhabited-finitely-enumerable-subset-ℝ =
      rec-trunc-Prop
        ( has-supremum-prop-subset-ℝ (subset-finitely-enumerable-subset-ℝ S) l2)
        ( λ eS →
          has-supremum-is-inhabited-finite-enumeration-subset-ℝ
            ( subset-finitely-enumerable-subset-ℝ S)
            ( eS)
            ( |S|))
        ( is-finitely-enumerable-finitely-enumerable-subset-ℝ S)

  opaque
    max-inhabited-finitely-enumerable-subset-ℝ : ℝ l2
    max-inhabited-finitely-enumerable-subset-ℝ =
      pr1 has-supremum-inhabited-finitely-enumerable-subset-ℝ
```

### Properties

#### The maximum is a supremum

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  opaque
    unfolding max-inhabited-finitely-enumerable-subset-ℝ

    is-supremum-max-inhabited-finitely-enumerable-subset-ℝ :
      is-supremum-subset-ℝ
        ( subset-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-supremum-max-inhabited-finitely-enumerable-subset-ℝ =
      pr2 (has-supremum-inhabited-finitely-enumerable-subset-ℝ S |S|)
```

#### The maximum is a least upper bound

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    is-least-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ :
      is-least-upper-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-least-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ =
      is-least-upper-bound-is-supremum-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
        ( is-supremum-max-inhabited-finitely-enumerable-subset-ℝ S |S|)
```

#### The maximum is approximated below

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    is-approximated-below-max-inhabited-finitely-enumerable-subset-ℝ :
      is-approximated-below-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-approximated-below-max-inhabited-finitely-enumerable-subset-ℝ =
      is-approximated-below-is-supremum-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
        ( is-supremum-max-inhabited-finitely-enumerable-subset-ℝ S |S|)
```

#### The maximum is an upper bound

```agda
module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  (|S| : is-inhabited-finitely-enumerable-subset-ℝ S)
  where

  abstract
    is-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ :
      is-upper-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
    is-upper-bound-max-inhabited-finitely-enumerable-subset-ℝ =
      is-upper-bound-is-supremum-family-ℝ
        ( inclusion-finitely-enumerable-subset-ℝ S)
        ( max-inhabited-finitely-enumerable-subset-ℝ S |S|)
        ( is-supremum-max-inhabited-finitely-enumerable-subset-ℝ S |S|)
```
