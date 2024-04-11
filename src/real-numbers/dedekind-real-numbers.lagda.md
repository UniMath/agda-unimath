# Dedekind real numbers

```agda
module real-numbers.dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.complements-subtypes
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.universe-levels

open import foundation-core.truncation-levels
```

</details>

## Idea

A
{{#concept "Dedekind cut" Agda=is-dedekind-cut WD="dedekind cut" WDID=Q851333}}
consists of a [pair](foundation.dependent-pair-types.md) `(L , U)` of
[subtypes](foundation-core.subtypes.md) of
[the rational numbers](elementary-number-theory.rational-numbers.md) `ℚ`,
satisfying the following four conditions

1. _Inhabitedness_. Both `L` and `U` are
   [inhabited](foundation.inhabited-subtypes.md) subtypes of `ℚ`.
2. _Roundedness_. A rational number `q` is in `L`
   [if and only if](foundation.logical-equivalences.md) there
   [exists](foundation.existential-quantification.md) `q < r` such that `r ∈ L`,
   and a rational number `r` is in `U` if and only if there exists `q < r` such
   that `q ∈ U`.
3. _Disjointness_. `L` and `U` are disjoint subsets of `ℚ`.
4. _Locatedness_. If `q < r` then `q ∈ L` or `r ∈ U`.

The type of {{#concept "Dedekind real numbers" Agda=ℝ}} is the type of all
Dedekind cuts. The Dedekind real numbers will be taken as the standard
definition of the real numbers in the `agda-unimath` library.

## Definition

### Dedekind cuts

```agda
module _
  {l1 l2 : Level} (L : subtype l1 ℚ) (U : subtype l2 ℚ)
  where

  is-dedekind-cut-Prop : Prop (l1 ⊔ l2)
  is-dedekind-cut-Prop =
    product-Prop
      ( product-Prop (exists-Prop ℚ L) (exists-Prop ℚ U))
      ( product-Prop
        ( product-Prop
          ( Π-Prop ℚ
            ( λ q →
              iff-Prop
                ( L q)
                ( exists-Prop ℚ (λ r → product-Prop (le-ℚ-Prop q r) (L r)))))
          ( Π-Prop ℚ
            ( λ r →
              iff-Prop
                ( U r)
                ( exists-Prop ℚ (λ q → product-Prop (le-ℚ-Prop q r) (U q))))))
        ( product-Prop
          ( Π-Prop ℚ (λ q → neg-Prop (product-Prop (L q) (U q))))
          ( Π-Prop ℚ
            ( λ q →
              Π-Prop ℚ
                ( λ r →
                  implication-Prop
                    ( le-ℚ-Prop q r)
                    ( disjunction-Prop (L q) (U r)))))))

  is-dedekind-cut : UU (l1 ⊔ l2)
  is-dedekind-cut = type-Prop is-dedekind-cut-Prop

  is-prop-is-dedekind-cut : is-prop is-dedekind-cut
  is-prop-is-dedekind-cut = is-prop-type-Prop is-dedekind-cut-Prop
```

### The Dedekind real numbers

```agda
ℝ : (l : Level) → UU (lsuc l)
ℝ l = Σ (subtype l ℚ) (λ L → Σ (subtype l ℚ) (is-dedekind-cut L))

real-dedekind-cut : {l : Level} (L U : subtype l ℚ) → is-dedekind-cut L U → ℝ l
real-dedekind-cut L U H = L , U , H

module _
  {l : Level} (x : ℝ l)
  where

  lower-cut-ℝ : subtype l ℚ
  lower-cut-ℝ = pr1 x

  upper-cut-ℝ : subtype l ℚ
  upper-cut-ℝ = pr1 (pr2 x)

  is-in-lower-cut-ℝ : ℚ → UU l
  is-in-lower-cut-ℝ = is-in-subtype lower-cut-ℝ

  is-in-upper-cut-ℝ : ℚ → UU l
  is-in-upper-cut-ℝ = is-in-subtype upper-cut-ℝ

  is-dedekind-cut-cut-ℝ : is-dedekind-cut lower-cut-ℝ upper-cut-ℝ
  is-dedekind-cut-cut-ℝ = pr2 (pr2 x)

  is-inhabited-lower-cut-ℝ : exists ℚ lower-cut-ℝ
  is-inhabited-lower-cut-ℝ = pr1 (pr1 is-dedekind-cut-cut-ℝ)

  is-inhabited-upper-cut-ℝ : exists ℚ upper-cut-ℝ
  is-inhabited-upper-cut-ℝ = pr2 (pr1 is-dedekind-cut-cut-ℝ)

  is-rounded-lower-cut-ℝ :
    (q : ℚ) →
    is-in-lower-cut-ℝ q ↔ ∃ ℚ (λ r → (le-ℚ q r) × (is-in-lower-cut-ℝ r))
  is-rounded-lower-cut-ℝ =
    pr1 (pr1 (pr2 is-dedekind-cut-cut-ℝ))

  is-rounded-upper-cut-ℝ :
    (r : ℚ) →
    is-in-upper-cut-ℝ r ↔ ∃ ℚ (λ q → (le-ℚ q r) × (is-in-upper-cut-ℝ q))
  is-rounded-upper-cut-ℝ =
    pr2 (pr1 (pr2 is-dedekind-cut-cut-ℝ))

  is-disjoint-cut-ℝ : (q : ℚ) → ¬ (is-in-lower-cut-ℝ q × is-in-upper-cut-ℝ q)
  is-disjoint-cut-ℝ =
    pr1 (pr2 (pr2 is-dedekind-cut-cut-ℝ))

  is-located-lower-upper-cut-ℝ :
    (q r : ℚ) → le-ℚ q r → (lower-cut-ℝ q) ∨ (upper-cut-ℝ r)
  is-located-lower-upper-cut-ℝ =
    pr2 (pr2 (pr2 is-dedekind-cut-cut-ℝ))

  cut-ℝ : subtype l ℚ
  cut-ℝ q =
    coproduct-Prop
      ( lower-cut-ℝ q)
      ( upper-cut-ℝ q)
      ( ev-pair ( is-disjoint-cut-ℝ q))

  is-in-cut-ℝ : ℚ → UU l
  is-in-cut-ℝ = is-in-subtype cut-ℝ
```

## Properties

### The Dedekind real numbers form a set

```agda
abstract
  is-set-ℝ : (l : Level) → is-set (ℝ l)
  is-set-ℝ l =
    is-set-Σ
      ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
      ( λ x →
        ( is-set-Σ
          ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
          ( λ y →
            ( is-set-is-prop
              ( is-prop-type-Prop
                ( is-dedekind-cut-Prop x y))))))

ℝ-Set : (l : Level) → Set (lsuc l)
pr1 (ℝ-Set l) = ℝ l
pr2 (ℝ-Set l) = is-set-ℝ l
```

## Properties of lower/upper Dedekind cuts

### Lower and upper Dedekind cuts are closed under the standard ordering on the rationals

```agda
module _
  {l : Level} (x : ℝ l) (p q : ℚ)
  where

  le-lower-cut-ℝ :
    le-ℚ p q →
    is-in-lower-cut-ℝ x q →
    is-in-lower-cut-ℝ x p
  le-lower-cut-ℝ H H' =
    ind-trunc-Prop
      ( λ s → lower-cut-ℝ x p)
      ( rec-coproduct
          ( id)
          ( λ I → ex-falso (is-disjoint-cut-ℝ x q (H' , I))))
      ( is-located-lower-upper-cut-ℝ x p q H)

  leq-lower-cut-ℝ :
    leq-ℚ p q →
    is-in-lower-cut-ℝ x q →
    is-in-lower-cut-ℝ x p
  leq-lower-cut-ℝ H H' =
    rec-coproduct
      ( λ s → le-lower-cut-ℝ s H')
      ( λ I →
        tr
          ( is-in-lower-cut-ℝ x)
          ( antisymmetric-leq-ℚ q p I H)
          ( H'))
      ( decide-le-leq-ℚ p q)

  le-upper-cut-ℝ :
    le-ℚ p q →
    is-in-upper-cut-ℝ x p →
    is-in-upper-cut-ℝ x q
  le-upper-cut-ℝ H H' =
    ind-trunc-Prop
      ( λ s → upper-cut-ℝ x q)
      ( rec-coproduct
        ( λ I → ex-falso (is-disjoint-cut-ℝ x p ( I , H')))
        ( id))
      ( is-located-lower-upper-cut-ℝ x p q H)

  leq-upper-cut-ℝ :
    leq-ℚ p q →
    is-in-upper-cut-ℝ x p →
    is-in-upper-cut-ℝ x q
  leq-upper-cut-ℝ H H' =
    rec-coproduct
      ( λ s → le-upper-cut-ℝ s H')
      ( λ I →
        tr
          ( is-in-upper-cut-ℝ x)
          ( antisymmetric-leq-ℚ p q H I)
          ( H'))
      ( decide-le-leq-ℚ p q)
```

### Elements of the lower cut are lower bounds of the upper cut

```agda
module _
  {l : Level} (x : ℝ l) (p q : ℚ)
  where

  le-lower-upper-cut-ℝ :
    is-in-lower-cut-ℝ x p →
    is-in-upper-cut-ℝ x q →
    le-ℚ p q
  le-lower-upper-cut-ℝ H H' =
    rec-coproduct
      ( id)
      ( λ I →
        ex-falso
          ( is-disjoint-cut-ℝ x p
              ( H , leq-upper-cut-ℝ x q p I H')))
      ( decide-le-leq-ℚ p q)
```

### Characterisation of each cut by the other

#### The lower cut is the subtype of rationals bounded above by some element of the complement of the upper cut

```agda
module _
  {l : Level} (x : ℝ l)
  where

  is-lower-complement-upper-cut-ℝ-Prop : (p q : ℚ) → Prop l
  is-lower-complement-upper-cut-ℝ-Prop p q =
    product-Prop
      ( le-ℚ-Prop p q)
      ( neg-Prop ( upper-cut-ℝ x q))

  lower-complement-upper-cut-ℝ : subtype l ℚ
  lower-complement-upper-cut-ℝ p =
    exists-Prop ℚ (is-lower-complement-upper-cut-ℝ-Prop p)
```

```agda
module _
  {l : Level} (x : ℝ l)
  where

  subset-lower-cut-lower-complement-upper-cut-ℝ :
    lower-complement-upper-cut-ℝ x ⊆ lower-cut-ℝ x
  subset-lower-cut-lower-complement-upper-cut-ℝ p =
    elim-exists-Prop
      ( is-lower-complement-upper-cut-ℝ-Prop x p)
      ( lower-cut-ℝ x p)
      ( λ q I →
        map-right-unit-law-disjunction-is-empty-Prop
          ( lower-cut-ℝ x p)
          ( upper-cut-ℝ x q)
          ( pr2 I)
          ( is-located-lower-upper-cut-ℝ x p q ( pr1 I)))

  subset-lower-complement-upper-cut-lower-cut-ℝ :
    lower-cut-ℝ x ⊆ lower-complement-upper-cut-ℝ x
  subset-lower-complement-upper-cut-lower-cut-ℝ p H =
    elim-exists-Prop
      ( λ q → product-Prop (le-ℚ-Prop p q) (lower-cut-ℝ x q))
      ( lower-complement-upper-cut-ℝ x p)
      ( λ q I →
        intro-exists
          ( is-lower-complement-upper-cut-ℝ-Prop x p)
          ( q)
          ( map-product
            ( id)
            ( λ L U → is-disjoint-cut-ℝ x q (L , U))
            ( I)))
      ( pr1 (is-rounded-lower-cut-ℝ x p) H)

  eq-lower-cut-lower-complement-upper-cut-ℝ :
    lower-complement-upper-cut-ℝ x ＝ lower-cut-ℝ x
  eq-lower-cut-lower-complement-upper-cut-ℝ =
    antisymmetric-leq-subtype
      ( lower-complement-upper-cut-ℝ x)
      ( lower-cut-ℝ x)
      ( subset-lower-cut-lower-complement-upper-cut-ℝ)
      ( subset-lower-complement-upper-cut-lower-cut-ℝ)
```

#### The upper cut is the subtype of rationals bounded below by some element of the complement of the lower cut

```agda
module _
  {l : Level} (x : ℝ l)
  where

  is-upper-complement-lower-cut-ℝ-Prop : (q p : ℚ) → Prop l
  is-upper-complement-lower-cut-ℝ-Prop q p =
    product-Prop
      ( le-ℚ-Prop p q)
      ( neg-Prop ( lower-cut-ℝ x p))

  upper-complement-lower-cut-ℝ : subtype l ℚ
  upper-complement-lower-cut-ℝ q =
    exists-Prop ℚ (is-upper-complement-lower-cut-ℝ-Prop q)
```

```agda
module _
  {l : Level} (x : ℝ l)
  where

  subset-upper-cut-upper-complement-lower-cut-ℝ :
    upper-complement-lower-cut-ℝ x ⊆ upper-cut-ℝ x
  subset-upper-cut-upper-complement-lower-cut-ℝ q =
    elim-exists-Prop
      ( is-upper-complement-lower-cut-ℝ-Prop x q)
      ( upper-cut-ℝ x q)
      ( λ p I →
        map-left-unit-law-disjunction-is-empty-Prop
          ( lower-cut-ℝ x p)
          ( upper-cut-ℝ x q)
          ( pr2 I)
          ( is-located-lower-upper-cut-ℝ x p q ( pr1 I)))

  subset-upper-complement-lower-cut-upper-cut-ℝ :
    upper-cut-ℝ x ⊆ upper-complement-lower-cut-ℝ x
  subset-upper-complement-lower-cut-upper-cut-ℝ q H =
    elim-exists-Prop
      ( λ p → product-Prop (le-ℚ-Prop p q) (upper-cut-ℝ x p))
      ( upper-complement-lower-cut-ℝ x q)
      ( λ p I →
        intro-exists
          ( is-upper-complement-lower-cut-ℝ-Prop x q)
          ( p)
          ( map-product
            ( id)
            ( λ U L → is-disjoint-cut-ℝ x p (L , U))
            ( I)))
      ( pr1 (is-rounded-upper-cut-ℝ x q) H)

  eq-upper-cut-upper-complement-lower-cut-ℝ :
    upper-complement-lower-cut-ℝ x ＝ upper-cut-ℝ x
  eq-upper-cut-upper-complement-lower-cut-ℝ =
    antisymmetric-leq-subtype
      ( upper-complement-lower-cut-ℝ x)
      ( upper-cut-ℝ x)
      ( subset-upper-cut-upper-complement-lower-cut-ℝ)
      ( subset-upper-complement-lower-cut-upper-cut-ℝ)
```

### The lower/upper cut of a real determines the other

```agda
module _
  {l : Level} (x y : ℝ l)
  where

  subset-lower-cut-upper-cut-ℝ :
    upper-cut-ℝ y ⊆ upper-cut-ℝ x → lower-cut-ℝ x ⊆ lower-cut-ℝ y
  subset-lower-cut-upper-cut-ℝ H =
    binary-tr
      ( _⊆_)
      ( eq-lower-cut-lower-complement-upper-cut-ℝ x)
      ( eq-lower-cut-lower-complement-upper-cut-ℝ y)
      ( λ p →
        elim-exists-Prop
          ( is-lower-complement-upper-cut-ℝ-Prop x p)
          ( lower-complement-upper-cut-ℝ y p)
          ( λ q → intro-∃ q ∘ tot (λ _ K → K ∘ H q)))

  subset-upper-cut-lower-cut-ℝ :
    lower-cut-ℝ x ⊆ lower-cut-ℝ y → upper-cut-ℝ y ⊆ upper-cut-ℝ x
  subset-upper-cut-lower-cut-ℝ H =
    binary-tr
      ( _⊆_)
      ( eq-upper-cut-upper-complement-lower-cut-ℝ y)
      ( eq-upper-cut-upper-complement-lower-cut-ℝ x)
      ( λ q →
        elim-exists-Prop
          ( is-upper-complement-lower-cut-ℝ-Prop y q)
          ( upper-complement-lower-cut-ℝ x q)
          ( λ p → intro-∃ p ∘ tot (λ _ K → K ∘ H p)))

module _
  {l : Level} (x y : ℝ l)
  where

  eq-lower-cut-eq-upper-cut-ℝ :
    upper-cut-ℝ x ＝ upper-cut-ℝ y → lower-cut-ℝ x ＝ lower-cut-ℝ y
  eq-lower-cut-eq-upper-cut-ℝ H =
    antisymmetric-leq-subtype
      ( lower-cut-ℝ x)
      ( lower-cut-ℝ y)
      ( subset-lower-cut-upper-cut-ℝ x y
        ( pr2 ∘ has-same-elements-eq-subtype
          ( upper-cut-ℝ x)
          ( upper-cut-ℝ y)
          ( H)))
      ( subset-lower-cut-upper-cut-ℝ y x
        ( pr1 ∘ has-same-elements-eq-subtype
          ( upper-cut-ℝ x)
          ( upper-cut-ℝ y)
          ( H)))

  eq-upper-cut-eq-lower-cut-ℝ :
    lower-cut-ℝ x ＝ lower-cut-ℝ y → upper-cut-ℝ x ＝ upper-cut-ℝ y
  eq-upper-cut-eq-lower-cut-ℝ H =
    antisymmetric-leq-subtype
      ( upper-cut-ℝ x)
      ( upper-cut-ℝ y)
      ( subset-upper-cut-lower-cut-ℝ y x
        ( pr2 ∘ has-same-elements-eq-subtype
          ( lower-cut-ℝ x)
          ( lower-cut-ℝ y)
          ( H)))
      ( subset-upper-cut-lower-cut-ℝ x y
        ( pr1 ∘ has-same-elements-eq-subtype
          ( lower-cut-ℝ x)
          ( lower-cut-ℝ y)
          ( H)))
```

### The map from a real number to its lower cut is an embedding

```agda
module _
  {l : Level} (L : subtype l ℚ)
  where

  has-upper-cut-Prop : Prop (lsuc l)
  has-upper-cut-Prop =
    pair
      ( Σ (subtype l ℚ) (is-dedekind-cut L))
      ( is-prop-all-elements-equal
        ( λ U U' →
          eq-type-subtype
            ( is-dedekind-cut-Prop L)
            ( eq-upper-cut-eq-lower-cut-ℝ
              ( pair L U)
              ( pair L U')
              ( refl))))

is-emb-lower-cut : {l : Level} → is-emb (lower-cut-ℝ {l})
is-emb-lower-cut = is-emb-inclusion-subtype has-upper-cut-Prop
```

### Two real numbers with the same lower/upper cut are equal

```agda
module _
  {l : Level} (x y : ℝ l)
  where

  eq-eq-lower-cut-ℝ : lower-cut-ℝ x ＝ lower-cut-ℝ y → x ＝ y
  eq-eq-lower-cut-ℝ = eq-type-subtype has-upper-cut-Prop

  eq-eq-upper-cut-ℝ : upper-cut-ℝ x ＝ upper-cut-ℝ y → x ＝ y
  eq-eq-upper-cut-ℝ = eq-eq-lower-cut-ℝ ∘ (eq-lower-cut-eq-upper-cut-ℝ x y)
```

## References

This page follows parts of Section 11.2 in {{#cite UF13}}.

{{#bibliography}}

## External links

- [DedekindReals.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/DedekindReals.Type.html)
  at TypeTopology
- [Dedekind cut](https://ncatlab.org/nlab/show/Dedekind+cut) at $n$Lab
- [Dedekind cut](https://en.wikipedia.org/wiki/Dedekind_cut) at Wikipedia
- [Construction of the real numbers by Dedekind cuts](https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_by_Dedekind_cuts)
  at Wikipedia
- [Dedekind cut](https://www.britannica.com/science/Dedekind-cut) at Britannica
