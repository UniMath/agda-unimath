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

open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy filter" Disambiguation="on a pseudometric space" Agda=cauchy-filter-Pseudometric-Space}}
on a [pseudometric space](metric-spaces.pseudometric-spaces.md) `M` is a
[proper](metric-spaces.proper-rational-neighborhood-subtypes.md) and
[saturated](metric-spaces.saturated-rational-neighborhood-subtypes.md)
[rational neighborhood subtype](metric-spaces.rational-neighborhood-subtypes.md)
on `M`,

```text
  U : ℚ⁺ → M → Prop l
```

with the following coherence properties with respect to the
[neighborhood relation](metric-spaces.rational-neighborhood-relations.md) `N` on
`M`:

- _boundedness_: `Uε`-points and `Uδ`-points are at distance at most `ε + δ`;
  for any `(ε δ : ℚ⁺)` and `(x y : M)`,

  ```text
    (U ε x) ∧ (U δ y) ⇒ N (ε + δ) x y
  ```

- _enclosure_: points at distance at most `δ` from `Uε`-points are
  `U(ε+δ)`-points; for any `(ε δ : ℚ⁺)` and `(x y : M)`,

  ```text
    (U ε x) ∧ (N δ x y) ⇒ U (ε + δ) y
  ```

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
equipped with a metric structure turning `F(M)` into a
[complete metric space](metric-spaces.complete-metric-spaces.md) where `η` is an
isometry.

## Definitions

### Filters in pseudometric spaces

A _filter_ in a pseudometric space is a rational neighborhood families of
subsets of its carrier type.

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where

  filter-Pseudometric-Space : UU (l1 ⊔ lsuc l)
  filter-Pseudometric-Space =
    Rational-Neighborhood-Subtype l (type-Pseudometric-Space M)

module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : filter-Pseudometric-Space l M)
  where

  is-in-filter-Pseudometric-Space : ℚ⁺ → type-Pseudometric-Space M → UU l
  is-in-filter-Pseudometric-Space =
    is-in-filter-Rational-Neighborhood-Subtype U

  is-prop-is-in-filter-Pseudometric-Space :
    (ε : ℚ⁺) (x : type-Pseudometric-Space M) →
    is-prop (is-in-filter-Pseudometric-Space ε x)
  is-prop-is-in-filter-Pseudometric-Space =
    is-prop-is-in-filter-Rational-Neighborhood-Subtype U
```

### Local filters on pseudometric spaces

A filter in a pseudometric space `M` is _local_ if it is **bounded** and
**enclosing** with respect to the nieghborhood relation: for any `ε δ : ℚ⁺` and
`x y : M`,

- `(U ε x) ∧ (U δ y) ⇒ N (ε + δ) x y`;
- `(U ε x) ∧ (N δ x y) ⇒ U (ε + δ) y`.

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : filter-Pseudometric-Space l M)
  (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M)
  where

  is-bounded-prop-filter-Pseudometric-Space : Prop (l2 ⊔ l)
  is-bounded-prop-filter-Pseudometric-Space =
    (U ε x ∧ U δ y) ⇒ neighborhood-prop-Pseudometric-Space M (ε +ℚ⁺ δ) x y

  is-bounded-filter-Pseudometric-Space : UU (l2 ⊔ l)
  is-bounded-filter-Pseudometric-Space =
    type-Prop
      is-bounded-prop-filter-Pseudometric-Space

  is-prop-is-bounded-filter-Pseudometric-Space :
    is-prop is-bounded-filter-Pseudometric-Space
  is-prop-is-bounded-filter-Pseudometric-Space =
    is-prop-type-Prop is-bounded-prop-filter-Pseudometric-Space

  is-enclosing-prop-filter-Pseudometric-Space : Prop (l2 ⊔ l)
  is-enclosing-prop-filter-Pseudometric-Space =
    (U ε x ∧ neighborhood-prop-Pseudometric-Space M δ x y) ⇒ U (ε +ℚ⁺ δ) y

  is-enclosing-filter-Pseudometric-Space : UU (l2 ⊔ l)
  is-enclosing-filter-Pseudometric-Space =
    type-Prop
      is-enclosing-prop-filter-Pseudometric-Space

  is-prop-is-enclosing-filter-Pseudometric-Space :
    is-prop is-enclosing-filter-Pseudometric-Space
  is-prop-is-enclosing-filter-Pseudometric-Space =
    is-prop-type-Prop is-enclosing-prop-filter-Pseudometric-Space

module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : filter-Pseudometric-Space l M)
  where

  is-local-prop-filter-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l)
  is-local-prop-filter-Pseudometric-Space =
    Π-Prop
      ( ℚ⁺ × ℚ⁺ × type-Pseudometric-Space M × type-Pseudometric-Space M)
      ( λ ( ε , δ , x , y) →
          ( is-bounded-prop-filter-Pseudometric-Space M U ε δ x y) ∧
          ( is-enclosing-prop-filter-Pseudometric-Space M U ε δ x y))

  is-local-filter-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l)
  is-local-filter-Pseudometric-Space =
    type-Prop is-local-prop-filter-Pseudometric-Space

  is-prop-is-local-filter-Pseudometric-Space :
    is-prop is-local-filter-Pseudometric-Space
  is-prop-is-local-filter-Pseudometric-Space =
    is-prop-type-Prop is-local-prop-filter-Pseudometric-Space
```

### The type of Cauchy filters on a pseudometric space

Cauchy filters are proper saturated local filters on a pseudometric space.

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  (U : filter-Pseudometric-Space l M)
  where

  is-cauchy-prop-filter-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l)
  is-cauchy-prop-filter-Pseudometric-Space =
    is-proper-prop-Rational-Neighborhood-Subtype U ∧
    is-saturated-prop-Rational-Neighborhood-Subtype U ∧
    is-local-prop-filter-Pseudometric-Space M U

  is-cauchy-filter-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l)
  is-cauchy-filter-Pseudometric-Space =
    type-Prop is-cauchy-prop-filter-Pseudometric-Space

  is-prop-is-cauchy-filter-Pseudometric-Space :
    is-prop is-cauchy-filter-Pseudometric-Space
  is-prop-is-cauchy-filter-Pseudometric-Space =
    is-prop-type-Prop is-cauchy-prop-filter-Pseudometric-Space

module _
  {l1 l2 : Level} (l : Level) (M : Pseudometric-Space l1 l2)
  where

  cauchy-filter-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ lsuc l)
  cauchy-filter-Pseudometric-Space =
    type-subtype (is-cauchy-prop-filter-Pseudometric-Space l M)
```

### Components of Cauchy filters

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : cauchy-filter-Pseudometric-Space l M)
  where

  filter-cauchy-filter-Pseudometric-Space : filter-Pseudometric-Space l M
  filter-cauchy-filter-Pseudometric-Space = pr1 U

  is-in-cauchy-filter-Pseudometric-Space : ℚ⁺ → type-Pseudometric-Space M → UU l
  is-in-cauchy-filter-Pseudometric-Space =
    is-in-filter-Pseudometric-Space M filter-cauchy-filter-Pseudometric-Space

  is-cauchy-filter-cauchy-filter-Pseudometric-Space :
    is-cauchy-filter-Pseudometric-Space
      ( l)
      ( M)
      ( filter-cauchy-filter-Pseudometric-Space)
  is-cauchy-filter-cauchy-filter-Pseudometric-Space = pr2 U

  is-proper-cauchy-filter-Pseudometric-Space :
    is-proper-Rational-Neighborhood-Subtype
      filter-cauchy-filter-Pseudometric-Space
  is-proper-cauchy-filter-Pseudometric-Space =
    pr1 is-cauchy-filter-cauchy-filter-Pseudometric-Space

  is-saturated-cauchy-filter-Pseudometric-Space :
    is-saturated-Rational-Neighborhood-Subtype
      filter-cauchy-filter-Pseudometric-Space
  is-saturated-cauchy-filter-Pseudometric-Space =
    pr1 (pr2 is-cauchy-filter-cauchy-filter-Pseudometric-Space)

  is-local-cauchy-filter-Pseudometric-Space :
    is-local-filter-Pseudometric-Space
      ( M)
      ( filter-cauchy-filter-Pseudometric-Space)
  is-local-cauchy-filter-Pseudometric-Space =
    pr2 (pr2 is-cauchy-filter-cauchy-filter-Pseudometric-Space)

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
  where

  is-monotonic-filter-cauchy-filter-Pseudometric-Space :
    ( x : type-Pseudometric-Space M) →
    ( ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-cauchy-filter-Pseudometric-Space M U ε x →
    is-in-cauchy-filter-Pseudometric-Space M U δ x
  is-monotonic-filter-cauchy-filter-Pseudometric-Space x ε δ H Ux =
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
  where

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

## References

This definition essentially corresponds to "Cauchy filters of formal balls" as
described in {{#cite Vickers2005localic}}, with **closed** (i.e. saturated)
formal balls.

{{#bibliography}}
