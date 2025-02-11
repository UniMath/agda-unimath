# Dedekind real numbers

```agda
module real-numbers.dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
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
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.truncation-levels

open import logic.functoriality-existential-quantification

open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

A Dedekind real number
consists of a [pair](foundation.dependent-pair-types.md) `(lx , uy)` of a
[lower Dedekind real](real-numbers.lower-dedekind-real-numbers) and an
[upper Dedekind real](real-numbers.upper-dedekind-real-numbers) that also satisfy
the following conditions:

1. _Disjointness_. The cuts of `lx` and `uy` are disjoint subsets of `ℚ`.
2. _Locatedness_. If `q < r` then `q` is in the cut of `lx` or `r` is in the cut
    of `uy`.

The Dedekind real numbers will be taken as the standard
definition of the real numbers in the agda-unimath library.

## Definition

### Dedekind real numbers

```agda
module _
  {l1 l2 : Level} (lx : lower-ℝ l1) (uy : upper-ℝ l2)
  where

  is-disjoint-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-disjoint-prop-lower-upper-ℝ =
    ∀' ℚ (λ q → ¬' (cut-lower-ℝ lx q ∧ cut-upper-ℝ uy q))

  is-disjoint-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-disjoint-lower-upper-ℝ = type-Prop is-disjoint-prop-lower-upper-ℝ

  is-located-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-located-prop-lower-upper-ℝ = ∀'
    ( ℚ)
    ( λ q → ∀' ℚ (λ r → le-ℚ-Prop q r ⇒ (cut-lower-ℝ lx q ∨ cut-upper-ℝ uy r)))

  is-located-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-located-lower-upper-ℝ = type-Prop is-located-prop-lower-upper-ℝ

  is-dedekind-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  is-dedekind-prop-lower-upper-ℝ =
    is-disjoint-prop-lower-upper-ℝ ∧ is-located-prop-lower-upper-ℝ

  is-dedekind-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-dedekind-lower-upper-ℝ = type-Prop is-dedekind-prop-lower-upper-ℝ
```

### The Dedekind real numbers

```agda
ℝ : (l : Level) → UU (lsuc l)
ℝ l = Σ (lower-ℝ l) (λ lx → Σ (upper-ℝ l) (is-dedekind-lower-upper-ℝ lx))

real-lower-upper-ℝ :
  {l : Level} →
  (lx : lower-ℝ l) (uy : upper-ℝ l) →
  is-disjoint-lower-upper-ℝ lx uy →
  is-located-lower-upper-ℝ lx uy →
  ℝ l
real-lower-upper-ℝ lx uy H K =
  lx , uy , H , K

module _
  {l : Level} (x : ℝ l)
  where

  lower-real-ℝ : lower-ℝ l
  lower-real-ℝ = pr1 x

  upper-real-ℝ : upper-ℝ l
  upper-real-ℝ = pr1 (pr2 x)

  lower-cut-ℝ : subtype l ℚ
  lower-cut-ℝ = cut-lower-ℝ lower-real-ℝ

  upper-cut-ℝ : subtype l ℚ
  upper-cut-ℝ = cut-upper-ℝ upper-real-ℝ

  is-in-lower-cut-ℝ : ℚ → UU l
  is-in-lower-cut-ℝ = is-in-subtype lower-cut-ℝ

  is-in-upper-cut-ℝ : ℚ → UU l
  is-in-upper-cut-ℝ = is-in-subtype upper-cut-ℝ

  is-dedekind-ℝ : is-dedekind-lower-upper-ℝ lower-real-ℝ upper-real-ℝ
  is-dedekind-ℝ = pr2 (pr2 x)

  is-inhabited-lower-cut-ℝ : exists ℚ lower-cut-ℝ
  is-inhabited-lower-cut-ℝ = is-inhabited-cut-lower-ℝ lower-real-ℝ

  is-inhabited-upper-cut-ℝ : exists ℚ upper-cut-ℝ
  is-inhabited-upper-cut-ℝ = is-inhabited-cut-upper-ℝ upper-real-ℝ

  is-rounded-lower-cut-ℝ :
    (q : ℚ) →
    is-in-lower-cut-ℝ q ↔
    exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-ℝ r))
  is-rounded-lower-cut-ℝ = is-rounded-cut-lower-ℝ lower-real-ℝ

  is-rounded-upper-cut-ℝ :
    (r : ℚ) →
    is-in-upper-cut-ℝ r ↔
    exists ℚ (λ q → (le-ℚ-Prop q r) ∧ (upper-cut-ℝ q))
  is-rounded-upper-cut-ℝ = is-rounded-cut-upper-ℝ upper-real-ℝ

  is-disjoint-cut-ℝ : (q : ℚ) → ¬ (is-in-lower-cut-ℝ q × is-in-upper-cut-ℝ q)
  is-disjoint-cut-ℝ = pr1 (pr2 (pr2 x))

  is-located-lower-upper-cut-ℝ :
    (q r : ℚ) → le-ℚ q r →
    type-disjunction-Prop (lower-cut-ℝ q) (upper-cut-ℝ r)
  is-located-lower-upper-cut-ℝ = pr2 (pr2 (pr2 x))

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
      ( is-set-lower-ℝ l)
      ( λ x →
        is-set-Σ
          ( is-set-upper-ℝ l)
          ( λ y →
            ( is-set-is-prop
              ( is-prop-type-Prop
                ( is-dedekind-prop-lower-upper-ℝ x y)))))

ℝ-Set : (l : Level) → Set (lsuc l)
ℝ-Set l = ℝ l , is-set-ℝ l
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
  le-lower-cut-ℝ = le-cut-lower-ℝ (lower-real-ℝ x) p q

  leq-lower-cut-ℝ :
    leq-ℚ p q →
    is-in-lower-cut-ℝ x q →
    is-in-lower-cut-ℝ x p
  leq-lower-cut-ℝ = leq-cut-lower-ℝ (lower-real-ℝ x) p q

  le-upper-cut-ℝ :
    le-ℚ p q →
    is-in-upper-cut-ℝ x p →
    is-in-upper-cut-ℝ x q
  le-upper-cut-ℝ = le-cut-upper-ℝ (upper-real-ℝ x) p q

  leq-upper-cut-ℝ :
    leq-ℚ p q →
    is-in-upper-cut-ℝ x p →
    is-in-upper-cut-ℝ x q
  leq-upper-cut-ℝ = leq-cut-upper-ℝ (upper-real-ℝ x) p q
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
    ( le-ℚ-Prop p q) ∧ (¬' (upper-cut-ℝ x q))

  lower-complement-upper-cut-ℝ : subtype l ℚ
  lower-complement-upper-cut-ℝ p =
    ∃ ℚ (is-lower-complement-upper-cut-ℝ-Prop p)
```

```agda
module _
  {l : Level} (x : ℝ l)
  where

  subset-lower-cut-lower-complement-upper-cut-ℝ :
    lower-complement-upper-cut-ℝ x ⊆ lower-cut-ℝ x
  subset-lower-cut-lower-complement-upper-cut-ℝ p =
    elim-exists
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
    map-tot-exists
      ( λ q → map-product id (λ L U → is-disjoint-cut-ℝ x q (L , U)))
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
    (le-ℚ-Prop p q) ∧ (¬' (lower-cut-ℝ x p))

  upper-complement-lower-cut-ℝ : subtype l ℚ
  upper-complement-lower-cut-ℝ q =
    ∃ ℚ (is-upper-complement-lower-cut-ℝ-Prop q)
```

```agda
module _
  {l : Level} (x : ℝ l)
  where

  subset-upper-cut-upper-complement-lower-cut-ℝ :
    upper-complement-lower-cut-ℝ x ⊆ upper-cut-ℝ x
  subset-upper-cut-upper-complement-lower-cut-ℝ q =
    elim-exists
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
    map-tot-exists
      ( λ p → map-product id (λ U L → is-disjoint-cut-ℝ x p (L , U)))
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
      ( λ p → map-tot-exists (λ q → tot (λ _ K → K ∘ H q)))

  subset-upper-cut-lower-cut-ℝ :
    lower-cut-ℝ x ⊆ lower-cut-ℝ y → upper-cut-ℝ y ⊆ upper-cut-ℝ x
  subset-upper-cut-lower-cut-ℝ H =
    binary-tr
      ( _⊆_)
      ( eq-upper-cut-upper-complement-lower-cut-ℝ y)
      ( eq-upper-cut-upper-complement-lower-cut-ℝ x)
      ( λ q → map-tot-exists (λ p → tot (λ _ K → K ∘ H p)))

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

### The map from a real number to its lower real is an embedding

```agda
module _
  {l : Level}
  (lx : lower-ℝ l)
  where

  has-upper-real-Prop : Prop (lsuc l)
  pr1 has-upper-real-Prop = Σ (upper-ℝ l) (is-dedekind-lower-upper-ℝ lx)
  pr2 has-upper-real-Prop =
    ( is-prop-all-elements-equal)
    ( λ uy uy' →
      eq-type-subtype
        ( is-dedekind-prop-lower-upper-ℝ lx)
        ( eq-eq-cut-upper-ℝ
          ( pr1 uy)
          ( pr1 uy')
          ( eq-upper-cut-eq-lower-cut-ℝ (lx , uy) (lx , uy') refl)))

is-emb-lower-real : {l : Level} → is-emb (lower-real-ℝ {l})
is-emb-lower-real = is-emb-inclusion-subtype has-upper-real-Prop
```

### The map from a real number to its upper real is an embedding

```agda
module _
  {l : Level}
  (uy : upper-ℝ l)
  where

  has-lower-real-Prop : Prop (lsuc l)
  pr1 has-lower-real-Prop =
    Σ (lower-ℝ l) (λ lx → is-dedekind-lower-upper-ℝ lx uy)
  pr2 has-lower-real-Prop =
    ( is-prop-all-elements-equal)
    ( λ lx lx' →
      eq-type-subtype
        ( λ l → is-dedekind-prop-lower-upper-ℝ l uy)
        ( eq-eq-cut-lower-ℝ
          ( pr1 lx)
          ( pr1 lx')
          ( eq-lower-cut-eq-upper-cut-ℝ
            ( pr1 lx , uy , pr2 lx)
            ( pr1 lx' , uy , pr2 lx')
            ( refl))))

is-emb-upper-real : {l : Level} → is-emb (upper-real-ℝ {l})
pr1 (pr1 (is-emb-upper-real (lx , ux , Hx) (ly , uy , Hy))) ux=uy =
  ap
    ( λ (uz , lz , Hz) → (lz , uz , Hz))
    ( pr1
      ( pr1
        ( is-emb-inclusion-subtype
          ( has-lower-real-Prop)
          ( ux , lx , Hx)
          ( uy , ly , Hy)))
      ( ux=uy))
pr2 (pr1 (is-emb-upper-real (lx , ux , Hx) (ly , uy , Hy))) ux=uy =
  {! (pr2 (pr1 (is-emb-inclusion-subtype has-lower-real-Prop (ux , lx , Hx) (uy , ly , Hy))) ux=uy) !}
pr1 (pr2 (is-emb-upper-real (lx , ux , Hx) (ly , uy , Hy))) ux=uy =
  ap
    ( λ (uz , lz , Hz) → (lz , uz , Hz))
    ( pr1
      (pr2
        (is-emb-inclusion-subtype
          ( has-lower-real-Prop)
          ( ux , lx , Hx)
          ( uy , ly , Hy)))
      ux=uy)
pr2 (pr2 (is-emb-upper-real (lx , ux , Hx) (ly , uy , Hy))) x=y =
  {! pr2 (pr2 (is-emb-inclusion-subtype has-lower-real-Prop (ux , lx , Hx) (uy , ly , Hy))) (ap (λ (lz , uz , Hz) → (uz , lz , Hz)) x=y) !}
```

### The map from a real number to its lower cut is an embedding

```agda
{- module _
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
is-emb-lower-cut = is-emb-inclusion-subtype has-upper-cut-Prop -}
```

### Two real numbers with the same lower/upper cut are equal

```agda
{- module _
  {l : Level} (x y : ℝ l)
  where

  eq-eq-lower-cut-ℝ : lower-cut-ℝ x ＝ lower-cut-ℝ y → x ＝ y
  eq-eq-lower-cut-ℝ = eq-type-subtype has-upper-cut-Prop

  eq-eq-upper-cut-ℝ : upper-cut-ℝ x ＝ upper-cut-ℝ y → x ＝ y
  eq-eq-upper-cut-ℝ = eq-eq-lower-cut-ℝ ∘ (eq-lower-cut-eq-upper-cut-ℝ x y) -}
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
