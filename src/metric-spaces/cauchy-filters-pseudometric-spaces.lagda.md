# Cauchy filters on pseudometric spaces

```agda
module metric-spaces.cauchy-filters-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces
open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
```

</details>

## Idea

A
{{#concept "Cauchy filter" Disambiguation="on a pseudometric space" Agda=cauchy-filter-Pseudometric-Space}}
on a [pseudometric space](metric-spaces.pseudometric-spaces.md) `M` is a
[proper](metric-spaces.proper-rational-neighborhood-subtypes.md),
[saturated](metric-spaces.saturated-rational-neighborhood-subtypes.md) and
[local](metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces.md)
[rational neighborhood subtype](metric-spaces.rational-neighborhood-subtypes.md)
on `M`.

In other words, it's a
[ℚ⁺](elementary-number-theory.positive-rational-numbers.md)-indexed family of
subsets

```text
  U : ℚ⁺ → M → Prop l
```

with the following properties:

- _properness_: `∀ (ε : ℚ⁺) → ∃ (x : M) | U ε x`
- _saturation_: for any `(ε : ℚ⁺)` and `(x : M)`,

  ```text
    (∀ (δ : ℚ⁺) → U (ε + δ) x) ⇒ U ε x
  ```

- _locality_: for any `(ε δ : ℚ⁺)` and `(x y : M)`,
  - `(U ε x) ∧ (U δ y) ⇒ N (ε + δ) x y`
  - `(U ε x) ∧ (N δ x y) ⇒ U (ε + δ) y`

where `N` denotes the
[neighborhood relation](metric-spaces.rational-neighborhood-relations.md) on
`M`.

The _locality_ condition can be interpreted as follows:

- for any `x` in `Uε`, the subset `Uδ` is contained in the
  `(ε + δ)`-neighborhood of `x`;
- for any `x` in `Uε`, the `δ`-neighborhood of `x` is contained in `U(ε + δ)`;
  in other words, the `δ`-neighborhood of `Uε` is contained in `U(ε + δ)`.

NB: The _saturation_ property ensures that the subsets `Uε` are "as big as they
could be": `Uε` contains the intersection of all `Uδ` for `ε < δ`:

```text
  ∀ (ε : ℚ⁺) → ∩ (ε < δ) Uδ ⊆ Uε
```

In the same way as neighborhoods in metric spaces are assumed
[saturated](metric-spaces.saturated-rational-neighborhood-relations.md) to
remove the ambiguity between _open_ or _closed_ neighborhoods (we consider
**closed** neighborhoods), we restrict this construction to saturated families
of subsets.

The type of Cauchy filters is equipped with a unit map `η : M → F(M)`; it can be
[equipped with a metric structure](metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces.md)
turning `F(M)` into a
[complete metric space](metric-spaces.complete-metric-spaces.md) where `η` is an
[isometry](metric-spaces.isometries-pseudometric-spaces.md).

## Definitions

### The type of Cauchy filters on a pseudometric space

Cauchy filters are proper saturated local rational neighborhood subtypes on a
pseudometric space.

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  (U : Rational-Neighborhood-Subtype l (type-Pseudometric-Space M))
  where

  is-cauchy-filter-prop-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l)
  is-cauchy-filter-prop-Pseudometric-Space =
    is-proper-prop-Rational-Neighborhood-Subtype U ∧
    is-saturated-prop-Rational-Neighborhood-Subtype U ∧
    is-local-prop-neighborhood-subtype-Pseudometric-Space M U

  is-cauchy-filter-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l)
  is-cauchy-filter-Pseudometric-Space =
    type-Prop is-cauchy-filter-prop-Pseudometric-Space

  is-prop-is-cauchy-filter-Pseudometric-Space :
    is-prop is-cauchy-filter-Pseudometric-Space
  is-prop-is-cauchy-filter-Pseudometric-Space =
    is-prop-type-Prop is-cauchy-filter-prop-Pseudometric-Space

module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where

  cauchy-filter-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ lsuc l)
  cauchy-filter-Pseudometric-Space =
    type-subtype (is-cauchy-filter-prop-Pseudometric-Space l M)
```

### Components of Cauchy filters

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : cauchy-filter-Pseudometric-Space l M)
  where

  neighborhood-subtype-cauchy-filter-Pseudometric-Space :
    Rational-Neighborhood-Subtype l (type-Pseudometric-Space M)
  neighborhood-subtype-cauchy-filter-Pseudometric-Space = pr1 U

  is-in-cauchy-filter-Pseudometric-Space : ℚ⁺ → type-Pseudometric-Space M → UU l
  is-in-cauchy-filter-Pseudometric-Space =
    is-in-Rational-Neighborhood-Subtype
      ( neighborhood-subtype-cauchy-filter-Pseudometric-Space)

  abstract
    is-cauchy-filter-neighborhood-subtype-cauchy-filter-Pseudometric-Space :
      is-cauchy-filter-Pseudometric-Space
        ( l)
        ( M)
        ( neighborhood-subtype-cauchy-filter-Pseudometric-Space)
    is-cauchy-filter-neighborhood-subtype-cauchy-filter-Pseudometric-Space =
      pr2 U

    is-proper-cauchy-filter-Pseudometric-Space :
      is-proper-Rational-Neighborhood-Subtype
        neighborhood-subtype-cauchy-filter-Pseudometric-Space
    is-proper-cauchy-filter-Pseudometric-Space =
      pr1 is-cauchy-filter-neighborhood-subtype-cauchy-filter-Pseudometric-Space

    is-saturated-cauchy-filter-Pseudometric-Space :
      is-saturated-Rational-Neighborhood-Subtype
        neighborhood-subtype-cauchy-filter-Pseudometric-Space
    is-saturated-cauchy-filter-Pseudometric-Space =
      pr1
        ( pr2
          is-cauchy-filter-neighborhood-subtype-cauchy-filter-Pseudometric-Space)

    is-local-cauchy-filter-Pseudometric-Space :
      is-local-neighborhood-subtype-Pseudometric-Space
        ( M)
        ( neighborhood-subtype-cauchy-filter-Pseudometric-Space)
    is-local-cauchy-filter-Pseudometric-Space =
      pr2
        ( pr2
          is-cauchy-filter-neighborhood-subtype-cauchy-filter-Pseudometric-Space)

    is-bounded-cauchy-filter-Pseudometric-Space :
      (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M) →
      is-in-cauchy-filter-Pseudometric-Space ε x →
      is-in-cauchy-filter-Pseudometric-Space δ y →
      neighborhood-Pseudometric-Space M (ε +ℚ⁺ δ) x y
    is-bounded-cauchy-filter-Pseudometric-Space ε δ x y Ux Uy =
      pr1 (is-local-cauchy-filter-Pseudometric-Space (ε , δ , x , y)) (Ux , Uy)

    is-enclosing-cauchy-filter-Pseudometric-Space :
      (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M) →
      is-in-cauchy-filter-Pseudometric-Space ε x →
      neighborhood-Pseudometric-Space M δ x y →
      is-in-cauchy-filter-Pseudometric-Space (ε +ℚ⁺ δ) y
    is-enclosing-cauchy-filter-Pseudometric-Space ε δ x y Ux Nxy =
      pr2 (is-local-cauchy-filter-Pseudometric-Space (ε , δ , x , y)) (Ux , Nxy)
```

### The unit map of Cauchy filters

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  map-unit-cauchy-filter-Pseudometric-Space :
    type-Pseudometric-Space M → cauchy-filter-Pseudometric-Space l2 M
  map-unit-cauchy-filter-Pseudometric-Space x =
    ( ( λ d y → neighborhood-prop-Pseudometric-Space M d x y) ,
      ( λ d → intro-exists x (refl-neighborhood-Pseudometric-Space M d x)) ,
      ( λ (ε , y) → saturated-neighborhood-Pseudometric-Space M ε x y) ,
      ( λ (ε , δ , y , z) →
        ( λ (Nxy , Nxz) →
          triangular-neighborhood-Pseudometric-Space M y x z ε δ
            ( Nxz)
            ( symmetric-neighborhood-Pseudometric-Space M ε x y Nxy)) ,
        ( λ (Nxy , Nyz) →
          triangular-neighborhood-Pseudometric-Space M x y z ε δ Nyz Nxy)))
```

## Properties

### Cauchy filters are monotonic

For any Cauchy filter `U` and `ε δ : ℚ⁺` with `ε < δ`, `Uε ⊆ Uδ`.

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : cauchy-filter-Pseudometric-Space l M)
  where abstract

  is-monotonic-cauchy-filter-Pseudometric-Space :
    ( x : type-Pseudometric-Space M) →
    ( ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-cauchy-filter-Pseudometric-Space M U ε x →
    is-in-cauchy-filter-Pseudometric-Space M U δ x
  is-monotonic-cauchy-filter-Pseudometric-Space x ε δ H Ux =
    tr
      ( λ d → is-in-cauchy-filter-Pseudometric-Space M U d x)
      ( right-diff-law-add-ℚ⁺ ε δ H)
      ( is-enclosing-cauchy-filter-Pseudometric-Space
        ( M)
        ( U)
        ( ε)
        ( le-diff-ℚ⁺ ε δ H)
        ( x)
        ( x)
        ( Ux)
        ( refl-neighborhood-Pseudometric-Space M _ x))
```

### Any point is in the filter of its image by the unit map

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where abstract

  is-in-filter-map-unit-cauchy-filter-Pseudometric-Space :
    ( ε : ℚ⁺) →
    ( x : type-Pseudometric-Space M) →
    is-in-cauchy-filter-Pseudometric-Space
      ( M)
      ( map-unit-cauchy-filter-Pseudometric-Space M x)
      ( ε)
      ( x)
  is-in-filter-map-unit-cauchy-filter-Pseudometric-Space ε x =
    refl-neighborhood-Pseudometric-Space M ε x
```

## See also

- The
  [metric space of Cauchy filters on a pseudometric space](metric-spaces.metric-space-of-cauchy-filters-pseudometric-spaces.md);
- the
  [complete metric space of Cauchy filters on a pseudometric space](metric-spaces.complete-metric-space-of-cauchy-filters-pseudometric-spaces.md).

## References

This definition essentially corresponds to "Cauchy filters of formal balls" as
described in {{#cite Vickers2005localic}}, with **closed** (i.e. saturated)
formal balls.

{{#bibliography}}
