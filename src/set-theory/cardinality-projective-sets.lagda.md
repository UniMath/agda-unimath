# Cardinality-projective sets

```agda
module set-theory.cardinality-projective-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.distributivity-of-set-truncation-over-projective-products
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.postcomposition-functions
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.truncated-types
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import set-theory.cardinals
open import set-theory.equality-cardinals

open import univalent-combinatorics.counting
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [set](foundation-core.sets.md) $I$ is
{{#concept "cardinality-projective" Disamibguation="sets" Agda=Cardinality-Projective-Set}}
if the [postcomposition map](foundation-core.postcomposition-functions.md)
$${\cardinality} ∘ {-} : (I → \Set) → (I → \Cardinal)$$ is
0-[connected](foundation.connected-maps.md).

**Terminology.** This terminology is not established in the literature and may
be subject to change.

## Definitions

### The predicate of being cardinality-projective at a universe level

```agda
module _
  {l1 : Level} (l2 : Level) (I : Set l1)
  where

  is-cardinality-projective-set-Level : UU (l1 ⊔ lsuc l2)
  is-cardinality-projective-set-Level =
    is-connected-map zero-𝕋 (postcomp (type-Set I) (cardinality {l2}))

  is-prop-is-cardinality-projective-set-Level :
    is-prop is-cardinality-projective-set-Level
  is-prop-is-cardinality-projective-set-Level =
    is-prop-is-connected-map zero-𝕋 (postcomp (type-Set I) cardinality)

  is-cardinality-projective-set-prop-Level : Prop (l1 ⊔ lsuc l2)
  is-cardinality-projective-set-prop-Level =
    ( is-cardinality-projective-set-Level ,
      is-prop-is-cardinality-projective-set-Level)
```

### The universe of cardinality-projective sets at a universe level

```agda
Cardinality-Projective-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cardinality-Projective-Set l1 l2 =
  Σ (Set l1) (is-cardinality-projective-set-Level l2)

module _
  {l1 l2 : Level} (I : Cardinality-Projective-Set l1 l2)
  where

  set-Cardinality-Projective-Set : Set l1
  set-Cardinality-Projective-Set = pr1 I

  type-Cardinality-Projective-Set : UU l1
  type-Cardinality-Projective-Set = type-Set set-Cardinality-Projective-Set

  is-set-type-Cardinality-Projective-Set :
    is-set type-Cardinality-Projective-Set
  is-set-type-Cardinality-Projective-Set =
    is-set-type-Set set-Cardinality-Projective-Set

  is-cardinality-projective-Cardinality-Projective-Set :
    is-cardinality-projective-set-Level l2 set-Cardinality-Projective-Set
  is-cardinality-projective-Cardinality-Projective-Set = pr2 I

  is-set-equivalence-postcomp-cardinality-type-Cardinality-Projective-Set :
    is-truncation-equivalence zero-𝕋
      ( postcomp type-Cardinality-Projective-Set (cardinality {l2}))
  is-set-equivalence-postcomp-cardinality-type-Cardinality-Projective-Set =
    is-truncation-equivalence-is-connected-map
      ( postcomp type-Cardinality-Projective-Set cardinality)
      ( is-cardinality-projective-Cardinality-Projective-Set)

  ind-Cardinality-Projective-Set :
    {l3 : Level}
    (P : (type-Cardinality-Projective-Set → Cardinal l2) → Set l3) →
    ( (Y : type-Cardinality-Projective-Set → Set l2) →
      type-Set (P (cardinality ∘ Y))) →
    (X : type-Cardinality-Projective-Set → Cardinal l2) → type-Set (P X)
  ind-Cardinality-Projective-Set =
    ind-is-connected-map is-cardinality-projective-Cardinality-Projective-Set

  compute-ind-Cardinality-Projective-Set :
    {l3 : Level}
    (P : (type-Cardinality-Projective-Set → Cardinal l2) → Set l3)
    (T :
      (Y : type-Cardinality-Projective-Set → Set l2) →
      type-Set (P (cardinality ∘ Y)))
    (Y : type-Cardinality-Projective-Set → Set l2) →
    ind-Cardinality-Projective-Set P T (cardinality ∘ Y) ＝ T Y
  compute-ind-Cardinality-Projective-Set =
    compute-ind-is-connected-map
      ( is-cardinality-projective-Cardinality-Projective-Set)

  apply-twice-ind-Cardinality-Projective-Set :
    {l3 : Level}
    (P : (X Y : type-Cardinality-Projective-Set → Cardinal l2) → Set l3) →
    ( (X Y : type-Cardinality-Projective-Set → Set l2) →
      type-Set (P (cardinality ∘ X) (cardinality ∘ Y))) →
    (X Y : type-Cardinality-Projective-Set → Cardinal l2) → type-Set (P X Y)
  apply-twice-ind-Cardinality-Projective-Set P h X =
    ind-Cardinality-Projective-Set
      ( P X)
      ( λ Y →
        ind-Cardinality-Projective-Set
          ( λ X → P X (cardinality ∘ Y))
          ( λ X → h X Y)
          ( X))

  constr-Cardinality-Projective-Set :
    {l : Level} →
    ((type-Cardinality-Projective-Set → Set l2) → Cardinal l) →
    (type-Cardinality-Projective-Set → Cardinal l2) →
    Cardinal l
  constr-Cardinality-Projective-Set {l} =
    rec-is-truncation-equivalence
      ( is-set-equivalence-postcomp-cardinality-type-Cardinality-Projective-Set)
      ( Cardinal-Set l)

  compute-constr-Cardinality-Projective-Set :
    {l : Level} →
    (T : (type-Cardinality-Projective-Set → Set l2) → Cardinal l)
    (Y : type-Cardinality-Projective-Set → Set l2) →
    constr-Cardinality-Projective-Set T (cardinality ∘ Y) ＝ T Y
  compute-constr-Cardinality-Projective-Set {l} =
    compute-rec-is-truncation-equivalence
      ( is-set-equivalence-postcomp-cardinality-type-Cardinality-Projective-Set)
      ( Cardinal-Set l)
```

## Properties

### Distributive property of cardinality-projective sets

A set `I` is cardinality-projective if and only if the distributive map

```text
  ║I → Set║₀ → (I → Cardinal)
```

is an equivalence.

**Proof.** We have the commuting triangle

```text
            (I → Set)
            /       \
           /         \
          ∨           ∨
  ║I → Set║₀ -----> (I → Cardinal)
```

where the left vertical map is 0-connected hence by the cancellation/composition
property of 0-connected maps, `I` is cardinality-projective if and only if the
bottom horizontal map is. But the horizontal map is a map between sets, and so
is 0-connected if and only if it is an equivalence. ∎

```agda
module _
  {l1 l2 : Level} (I : Set l1)
  where

  is-set-equivalence-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set :
    is-truncation-equivalence zero-𝕋
      ( postcomp (type-Set I) (cardinality {l2})) →
    is-truncation-equivalence zero-𝕋
      ( map-distributive-trunc-function-type zero-𝕋 (type-Set I) (Set l2))
  is-set-equivalence-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set
    H =
    is-truncation-equivalence-right-map-triangle
      ( postcomp (type-Set I) cardinality)
      ( map-distributive-trunc-function-type zero-𝕋 (type-Set I) (Set l2))
      ( unit-trunc-Set)
      ( λ f → inv (eq-htpy (compute-distributive-trunc-function-type zero-𝕋 f)))
      ( H)
      ( is-truncation-equivalence-unit-trunc)

  is-equiv-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set :
    is-truncation-equivalence zero-𝕋
      ( postcomp (type-Set I) (cardinality {l2})) →
    is-equiv (map-distributive-trunc-function-type zero-𝕋 (type-Set I) (Set l2))
  is-equiv-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set
    H =
    is-equiv-is-truncation-equivalence
      ( is-set-type-trunc-Set)
      ( is-set-function-type is-set-Cardinal)
      ( is-set-equivalence-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set
        ( H))

  is-equiv-map-distributive-trunc-set-is-cardinality-projective-set :
    is-cardinality-projective-set-Level l2 I →
    is-equiv (map-distributive-trunc-function-type zero-𝕋 (type-Set I) (Set l2))
  is-equiv-map-distributive-trunc-set-is-cardinality-projective-set H =
    is-equiv-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set
      ( is-truncation-equivalence-is-connected-map _ H)

  is-cardinality-projective-set-is-is-equiv-map-distributive-trunc-set :
    is-equiv
      ( map-distributive-trunc-function-type zero-𝕋 (type-Set I) (Set l2)) →
    is-cardinality-projective-set-Level l2 I
  is-cardinality-projective-set-is-is-equiv-map-distributive-trunc-set H =
    is-connected-map-left-map-triangle
      ( postcomp (type-Set I) cardinality)
      ( map-distributive-trunc-function-type zero-𝕋 (type-Set I) (Set l2))
      ( unit-trunc-Set)
      ( λ f → inv (eq-htpy (compute-distributive-trunc-function-type zero-𝕋 f)))
      ( is-connected-map-unit-trunc zero-𝕋)
      ( is-connected-map-is-equiv H)
```

### The unit map of a cardinality-projective set

We call the inverse map to the distributive law the "unit map" of the
cardinality-projective set, and this map gives an induction principle for
constructing cardinals over $I$.

```agda
module _
  {l1 l2 : Level} (I : Cardinality-Projective-Set l1 l2)
  (let I' = type-Cardinality-Projective-Set I)
  where

  unit-Cardinality-Projective-Set :
    (I' → Cardinal l2) → ║ (I' → Set l2) ║₀
  unit-Cardinality-Projective-Set =
    map-inv-is-equiv
      ( is-equiv-map-distributive-trunc-set-is-cardinality-projective-set
        ( set-Cardinality-Projective-Set I)
        ( is-cardinality-projective-Cardinality-Projective-Set I))

  is-retraction-unit-Cardinality-Projective-Set :
    is-retraction
      ( map-distributive-trunc-function-type zero-𝕋 I' (Set l2))
      ( unit-Cardinality-Projective-Set)
  is-retraction-unit-Cardinality-Projective-Set =
    is-retraction-map-inv-is-equiv
      ( is-equiv-map-distributive-trunc-set-is-cardinality-projective-set
        ( set-Cardinality-Projective-Set I)
        ( is-cardinality-projective-Cardinality-Projective-Set I))

  compute-unit-Cardinality-Projective-Set :
    (K : I' → Set l2) →
    unit-Cardinality-Projective-Set (cardinality ∘ K) ＝ unit-trunc-Set K
  compute-unit-Cardinality-Projective-Set K =
    ( ap
      ( unit-Cardinality-Projective-Set)
      ( inv (eq-htpy (compute-distributive-trunc-function-type zero-𝕋 K)))) ∙
    ( is-retraction-unit-Cardinality-Projective-Set (unit-trunc-Set K))
```

### A set is cardinality-projective if the postcomposition map is a set-equivalence

```agda
module _
  {l1 l2 : Level} (I : Set l1)
  where

  is-cardinality-projective-set-is-set-equivalence-postcomp-cardinality-Set :
    is-truncation-equivalence zero-𝕋
      ( postcomp (type-Set I) (cardinality {l2})) →
    is-cardinality-projective-set-Level l2 I
  is-cardinality-projective-set-is-set-equivalence-postcomp-cardinality-Set
    H =
    is-cardinality-projective-set-is-is-equiv-map-distributive-trunc-set I
    ( is-equiv-map-distributive-trunc-set-is-set-equivalence-postcomp-cardinality-Set
      ( I)
      ( H))
```

### Projective sets are cardinality-projective

```agda
cardinality-projective-set-Projective-Set :
  {l1 l2 : Level} →
  Projective-Set l1 (lsuc l2) →
  Cardinality-Projective-Set l1 l2
cardinality-projective-set-Projective-Set {l1} {l2} X =
  ( set-Projective-Set X ,
    is-cardinality-projective-set-is-is-equiv-map-distributive-trunc-set
      ( set-Projective-Set X)
      ( is-equiv-map-distributive-trunc-Π-is-projective-Level
        ( type-Set (set-Projective-Set X))
        ( λ _ → Set l2)
        ( is-projective-Projective-Set X)))
```

### The standard finite sets are cardinality-projective

```agda
module _
  {l : Level} (n : ℕ)
  where

  abstract
    is-cardinality-projective-Fin :
      is-cardinality-projective-set-Level l (Fin-Set n)
    is-cardinality-projective-Fin =
      is-connected-map-left-map-triangle
        ( postcomp (Fin n) cardinality)
        ( map-equiv-distributive-trunc-Π-Fin-Set n (λ _ → Set l))
        ( unit-trunc-Set)
        ( inv-htpy (triangle-distributive-trunc-Π-Fin-Set n (λ _ → Set l)))
        ( is-connected-map-unit-trunc zero-𝕋)
        ( is-connected-map-is-equiv
          ( is-equiv-map-equiv-distributive-trunc-Π-Fin-Set n (λ _ → Set l)))

  cardinality-projective-set-Fin : Cardinality-Projective-Set lzero l
  cardinality-projective-set-Fin = (Fin-Set n , is-cardinality-projective-Fin)
```

### Sets equipped with counting are cardinality-projective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (c : count A)
  where

  abstract
    is-cardinality-projective-set-count :
      is-cardinality-projective-set-Level l2 (set-type-count c)
    is-cardinality-projective-set-count =
      is-connected-map-left-map-triangle
        ( postcomp A cardinality)
        ( map-equiv-distributive-trunc-Π-count-Set c (λ _ → Set l2))
        ( unit-trunc-Set)
        ( inv-htpy (triangle-distributive-trunc-Π-count-Set c (λ _ → Set l2)))
        ( is-connected-map-unit-trunc zero-𝕋)
        ( is-connected-map-is-equiv
          ( is-equiv-map-equiv-distributive-trunc-Π-count-Set c (λ _ → Set l2)))

  cardinality-projective-set-count : Cardinality-Projective-Set l1 l2
  cardinality-projective-set-count =
    ( set-type-count c , is-cardinality-projective-set-count)
```

### Finite sets are cardinality-projective

```agda
module _
  {l1 l2 : Level} (A : Finite-Type l1)
  where

  abstract
    is-cardinality-projective-set-Finite-Type :
      is-cardinality-projective-set-Level l2 (set-Finite-Type A)
    is-cardinality-projective-set-Finite-Type =
      rec-trunc-Prop
        ( is-cardinality-projective-set-prop-Level l2 (set-Finite-Type A))
        ( is-cardinality-projective-set-count)
        ( is-finite-type-Finite-Type A)

  cardinality-projective-set-Finite-Type : Cardinality-Projective-Set l1 l2
  cardinality-projective-set-Finite-Type =
    ( set-Finite-Type A , is-cardinality-projective-set-Finite-Type)
```

## See also

- In
  [Distributivity of set truncation over finite products](univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.md)
  it is demonstrated that finite types are cardinality-projective.
