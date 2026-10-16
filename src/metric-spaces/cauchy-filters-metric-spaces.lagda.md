# Cauchy filters on metric spaces

```agda
module metric-spaces.cauchy-filters-metric-spaces where
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

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy filter" Disambiguation="on a metric space" Agda=cauchy-filter-Metric-Space}}
on a [metric space](metric-spaces.metric-spaces.md) `M` is a
[ℚ⁺](elementary-number-theory.positive-rational-numbers.md)-indexed family of
[subspaces](metric-spaces.subspaces-metric-spaces.md)

```text
  R : ℚ⁺ → M → Prop l
```

with the following properties:

- _properness_: `∀ (ε : ℚ⁺) → ∃ (x : M) | R ε x`
- _saturation_: for any `(ε : ℚ⁺)` and `(x : M)`,

  ```text
    (∀ (δ : ℚ⁺) → R (ε + δ) x) ⇒ R ε x
  ```

- _locality_: for any `(ε δ : ℚ⁺)` and `(x y : M)`,
  - `(R ε x) ∧ (R δ y) ⇒ N (ε + δ) x y`
  - `(R ε x) ∧ (N δ x y) ⇒ R (ε + δ) y`

where `N` denotes the
[neighborhood relation](metric-spaces.rational-neighborhood-relations.md) on
`M`.

## Definitions

### Rational families of subsets of metric spaces

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  where

  ℚ⁺-subset-Metric-Space : UU (l1 ⊔ lsuc l)
  ℚ⁺-subset-Metric-Space = ℚ⁺ → subset-Metric-Space l M

module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (R : ℚ⁺-subset-Metric-Space l M)
  where

  is-in-ℚ⁺-subset-Metric-Space : ℚ⁺ → type-Metric-Space M → UU l
  is-in-ℚ⁺-subset-Metric-Space d x = type-Prop (R d x)

  is-prop-is-in-ℚ⁺-subset-Metric-Space :
    (d : ℚ⁺) (x : type-Metric-Space M) →
    is-prop (is-in-ℚ⁺-subset-Metric-Space d x)
  is-prop-is-in-ℚ⁺-subset-Metric-Space d x = is-prop-type-Prop (R d x)
```

### The type of Cauchy filters on metric a space

#### Proper rational families of subsets of metric spaces

A rational family of subsets `R` is **proper** if it is inhabited for all radius
`ε`:

```text
  ∀ (ε : ℚ⁺) → ∃ (x : M) | R ε x`
```

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (R : ℚ⁺-subset-Metric-Space l M)
  where

  is-proper-prop-ℚ⁺-subset-Metric-Space : Prop (l1 ⊔ l)
  is-proper-prop-ℚ⁺-subset-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        ∃ (type-Metric-Space M)
          ( λ x → R d x))

  is-proper-ℚ⁺-subset-Metric-Space : UU (l1 ⊔ l)
  is-proper-ℚ⁺-subset-Metric-Space =
    type-Prop is-proper-prop-ℚ⁺-subset-Metric-Space

  is-prop-is-proper-ℚ⁺-subset-Metric-Space :
    is-prop is-proper-ℚ⁺-subset-Metric-Space
  is-prop-is-proper-ℚ⁺-subset-Metric-Space =
    is-prop-type-Prop is-proper-prop-ℚ⁺-subset-Metric-Space
```

#### Saturated rational families of subsets of metric spaces

A rational family of subsets `R` is **saturated** if it is closed on the right:
for any `ε : ℚ⁺` and `x : M`,

```text
  (∀ (δ : ℚ⁺) → R (ε + δ) x) ⇒ R ε x
```

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (R : ℚ⁺-subset-Metric-Space l M)
  where

  is-saturated-prop-ℚ⁺-subset-Metric-Space : Prop (l1 ⊔ l)
  is-saturated-prop-ℚ⁺-subset-Metric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-Metric-Space M)
          ( λ x →
            ( Π-Prop
              ( ℚ⁺)
              ( λ δ → R (ε +ℚ⁺ δ) x)) ⇒
            ( R ε x)))

  is-saturated-ℚ⁺-subset-Metric-Space : UU (l1 ⊔ l)
  is-saturated-ℚ⁺-subset-Metric-Space =
    type-Prop is-saturated-prop-ℚ⁺-subset-Metric-Space

  is-prop-is-saturated-ℚ⁺-subset-Metric-Space :
    is-prop is-saturated-ℚ⁺-subset-Metric-Space
  is-prop-is-saturated-ℚ⁺-subset-Metric-Space =
    is-prop-type-Prop is-saturated-prop-ℚ⁺-subset-Metric-Space
```

#### Local rational families of subsets of metric spaces

```agda
module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (R : ℚ⁺-subset-Metric-Space l M)
  where

  neighborhood-conjunction-prop-ℚ⁺-subset-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) → Prop (l2 ⊔ l)
  neighborhood-conjunction-prop-ℚ⁺-subset-Metric-Space ε δ x y =
    (R ε x ∧ R δ y) ⇒ neighborhood-prop-Metric-Space M (ε +ℚ⁺ δ) x y

  neighborhood-conjunction-ℚ⁺-subset-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) → UU (l2 ⊔ l)
  neighborhood-conjunction-ℚ⁺-subset-Metric-Space ε δ x y =
    type-Prop (neighborhood-conjunction-prop-ℚ⁺-subset-Metric-Space ε δ x y)

  is-prop-neighborhood-conjunction-ℚ⁺-subset-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-prop
      ( neighborhood-conjunction-ℚ⁺-subset-Metric-Space ε δ x y)
  is-prop-neighborhood-conjunction-ℚ⁺-subset-Metric-Space ε δ x y =
    is-prop-type-Prop
      ( neighborhood-conjunction-prop-ℚ⁺-subset-Metric-Space ε δ x y)

  is-in-ℚ⁺-subset-neighborhood-prop-ℚ⁺-subset-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) → Prop (l2 ⊔ l)
  is-in-ℚ⁺-subset-neighborhood-prop-ℚ⁺-subset-Metric-Space ε δ x y =
    (R ε x ∧ neighborhood-prop-Metric-Space M δ x y) ⇒ R (ε +ℚ⁺ δ) y

  is-in-ℚ⁺-subset-neighborhood-ℚ⁺-subset-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) → UU (l2 ⊔ l)
  is-in-ℚ⁺-subset-neighborhood-ℚ⁺-subset-Metric-Space ε δ x y =
    type-Prop
      ( is-in-ℚ⁺-subset-neighborhood-prop-ℚ⁺-subset-Metric-Space ε δ x y)

  is-prop-is-in-ℚ⁺-subset-neighborhood-ℚ⁺-subset-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-prop
      ( is-in-ℚ⁺-subset-neighborhood-ℚ⁺-subset-Metric-Space ε δ x y)
  is-prop-is-in-ℚ⁺-subset-neighborhood-ℚ⁺-subset-Metric-Space ε δ x y =
    is-prop-type-Prop
      ( is-in-ℚ⁺-subset-neighborhood-prop-ℚ⁺-subset-Metric-Space ε δ x y)

  is-local-prop-ℚ⁺-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l)
  is-local-prop-ℚ⁺-subset-Metric-Space =
    Π-Prop
      ( ℚ⁺ × ℚ⁺ × type-Metric-Space M × type-Metric-Space M)
      ( λ ( ε , δ , x , y) →
          ( neighborhood-conjunction-prop-ℚ⁺-subset-Metric-Space ε δ x y) ∧
          ( is-in-ℚ⁺-subset-neighborhood-prop-ℚ⁺-subset-Metric-Space ε δ x y))

  is-local-ℚ⁺-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l)
  is-local-ℚ⁺-subset-Metric-Space =
    type-Prop is-local-prop-ℚ⁺-subset-Metric-Space

  is-prop-is-local-ℚ⁺-subset-Metric-Space :
    is-prop is-local-ℚ⁺-subset-Metric-Space
  is-prop-is-local-ℚ⁺-subset-Metric-Space =
    is-prop-type-Prop is-local-prop-ℚ⁺-subset-Metric-Space
```

#### Proper saturated local families of subsets

```agda
module _
  {l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  (R : ℚ⁺-subset-Metric-Space l M)
  where

  is-cauchy-prop-ℚ⁺-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l)
  is-cauchy-prop-ℚ⁺-subset-Metric-Space =
    is-proper-prop-ℚ⁺-subset-Metric-Space M R ∧
    is-saturated-prop-ℚ⁺-subset-Metric-Space M R ∧
    is-local-prop-ℚ⁺-subset-Metric-Space M R

  is-cauchy-ℚ⁺-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l)
  is-cauchy-ℚ⁺-subset-Metric-Space =
    type-Prop is-cauchy-prop-ℚ⁺-subset-Metric-Space

  is-prop-is-cauchy-ℚ⁺-subset-Metric-Space :
    is-prop is-cauchy-ℚ⁺-subset-Metric-Space
  is-prop-is-cauchy-ℚ⁺-subset-Metric-Space =
    is-prop-type-Prop is-cauchy-prop-ℚ⁺-subset-Metric-Space

module _
  {l1 l2 : Level} (l : Level) (M : Metric-Space l1 l2)
  where

  cauchy-filter-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l)
  cauchy-filter-Metric-Space =
    type-subtype (is-cauchy-prop-ℚ⁺-subset-Metric-Space l M)

module _
  {l1 l2 l : Level} (M : Metric-Space l1 l2)
  (C : cauchy-filter-Metric-Space l M)
  where

  ℚ⁺-subset-cauchy-filter-Metric-Space : ℚ⁺-subset-Metric-Space l M
  ℚ⁺-subset-cauchy-filter-Metric-Space = pr1 C

  is-in-filter-cauchy-filter-Metric-Space : ℚ⁺ → type-Metric-Space M → UU l
  is-in-filter-cauchy-filter-Metric-Space =
    is-in-ℚ⁺-subset-Metric-Space M ℚ⁺-subset-cauchy-filter-Metric-Space

  is-cauchy-ℚ⁺-subset-cauchy-filter-Metric-Space :
    is-cauchy-ℚ⁺-subset-Metric-Space l M ℚ⁺-subset-cauchy-filter-Metric-Space
  is-cauchy-ℚ⁺-subset-cauchy-filter-Metric-Space = pr2 C

  is-proper-cauchy-filter-Metric-Space :
    is-proper-ℚ⁺-subset-Metric-Space M ℚ⁺-subset-cauchy-filter-Metric-Space
  is-proper-cauchy-filter-Metric-Space =
    pr1 is-cauchy-ℚ⁺-subset-cauchy-filter-Metric-Space

  is-saturated-cauchy-filter-Metric-Space :
    is-saturated-ℚ⁺-subset-Metric-Space M ℚ⁺-subset-cauchy-filter-Metric-Space
  is-saturated-cauchy-filter-Metric-Space =
    pr1 (pr2 is-cauchy-ℚ⁺-subset-cauchy-filter-Metric-Space)

  is-local-cauchy-filter-Metric-Space :
    is-local-ℚ⁺-subset-Metric-Space M ℚ⁺-subset-cauchy-filter-Metric-Space
  is-local-cauchy-filter-Metric-Space =
    pr2 (pr2 is-cauchy-ℚ⁺-subset-cauchy-filter-Metric-Space)

  neighborhood-is-in-filter-cauchy-filter-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-in-filter-cauchy-filter-Metric-Space ε x →
    is-in-filter-cauchy-filter-Metric-Space δ y →
    neighborhood-Metric-Space M (ε +ℚ⁺ δ) x y
  neighborhood-is-in-filter-cauchy-filter-Metric-Space ε δ x y Rx Ry =
    pr1 (is-local-cauchy-filter-Metric-Space (ε , δ , x , y)) (Rx , Ry)

  is-in-filter-neighborhood-cauchy-filter-Metric-Space :
    (ε δ : ℚ⁺) (x y : type-Metric-Space M) →
    is-in-filter-cauchy-filter-Metric-Space ε x →
    neighborhood-Metric-Space M δ x y →
    is-in-filter-cauchy-filter-Metric-Space (ε +ℚ⁺ δ) y
  is-in-filter-neighborhood-cauchy-filter-Metric-Space ε δ x y Rx Nxy =
    pr2 (is-local-cauchy-filter-Metric-Space (ε , δ , x , y)) (Rx , Nxy)

  is-monotonic-filter-cauchy-filter-Metric-Space :
    ( x : type-Metric-Space M) →
    ( ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-filter-cauchy-filter-Metric-Space ε x →
    is-in-filter-cauchy-filter-Metric-Space δ x
  is-monotonic-filter-cauchy-filter-Metric-Space x ε δ H Rx =
    tr
      ( λ d → is-in-filter-cauchy-filter-Metric-Space d x)
      ( right-diff-law-add-ℚ⁺ ε δ H)
      ( is-in-filter-neighborhood-cauchy-filter-Metric-Space
        ( ε)
        ( le-diff-ℚ⁺ ε δ H)
        ( x)
        ( x)
        ( Rx)
        ( refl-neighborhood-Metric-Space M _ x))
```

### The unit map of Cauchy filters

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  map-unit-cauchy-filter-Metric-Space :
    type-Metric-Space M → cauchy-filter-Metric-Space l2 M
  map-unit-cauchy-filter-Metric-Space x =
    ( ( λ d y → neighborhood-prop-Metric-Space M d x y) ,
      ( λ d → intro-exists x (refl-neighborhood-Metric-Space M d x)) ,
      ( λ ε → saturated-neighborhood-Metric-Space M ε x) ,
      ( λ (ε , δ , y , z) →
        ( λ (Nxy , Nxz) →
          triangular-neighborhood-Metric-Space M y x z ε δ
            ( Nxz)
            ( symmetric-neighborhood-Metric-Space M ε x y Nxy)) ,
        ( λ (Nxy , Nyz) →
          triangular-neighborhood-Metric-Space M x y z ε δ Nyz Nxy)))
```

## Properties

### Any point is in the filter of its image by the unit point

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  is-in-filter-map-unit-cauchy-filter-Metric-Space :
    ( ε : ℚ⁺) →
    ( x : type-Metric-Space M) →
    is-in-filter-cauchy-filter-Metric-Space
      ( M)
      ( map-unit-cauchy-filter-Metric-Space M x)
      ( ε)
      ( x)
  is-in-filter-map-unit-cauchy-filter-Metric-Space ε x =
    refl-neighborhood-Metric-Space M ε x
```
