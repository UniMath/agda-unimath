# Local rational neighborhood subtypes on pseudometric spaces

```agda
module metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-subtypes
```

</details>

## Idea

A
[rational neighborhood subtype](metric-spaces.rational-neighborhood-subtypes.md)
`U` on a [pseudometric space](metric-spaces.pseudometric-spaces.md) `M` is
called
{{#concept "local" Disambiguation="rational neighborhood subtype of pseudometric space" Agda=is-local-neighborhood-subtype-Pseudometric-Space}}
if it satisfies the following coherence properties with respect to the
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

## Definitions

### Bounded rational neighborhood subtypes on pseudometric spaces

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : Rational-Neighborhood-Subtype l (type-Pseudometric-Space M))
  (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M)
  where

  is-bounded-prop-neighborhood-subtype-Pseudometric-Space :
    Prop (l2 ⊔ l)
  is-bounded-prop-neighborhood-subtype-Pseudometric-Space =
    (U ε x ∧ U δ y) ⇒ neighborhood-prop-Pseudometric-Space M (ε +ℚ⁺ δ) x y

  is-bounded-neighborhood-subtype-Pseudometric-Space : UU (l2 ⊔ l)
  is-bounded-neighborhood-subtype-Pseudometric-Space =
    type-Prop
      is-bounded-prop-neighborhood-subtype-Pseudometric-Space

  is-prop-is-bounded-neighborhood-subtype-Pseudometric-Space :
    is-prop is-bounded-neighborhood-subtype-Pseudometric-Space
  is-prop-is-bounded-neighborhood-subtype-Pseudometric-Space =
    is-prop-type-Prop
      is-bounded-prop-neighborhood-subtype-Pseudometric-Space
```

### Enclosing rational neighborhood subtypes on pseudometric spaces

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : Rational-Neighborhood-Subtype l (type-Pseudometric-Space M))
  (ε δ : ℚ⁺) (x y : type-Pseudometric-Space M)
  where

  is-enclosing-prop-neighborhood-subtype-Pseudometric-Space :
    Prop (l2 ⊔ l)
  is-enclosing-prop-neighborhood-subtype-Pseudometric-Space =
    (U ε x ∧ neighborhood-prop-Pseudometric-Space M δ x y) ⇒ U (ε +ℚ⁺ δ) y

  is-enclosing-neighborhood-subtype-Pseudometric-Space : UU (l2 ⊔ l)
  is-enclosing-neighborhood-subtype-Pseudometric-Space =
    type-Prop
      is-enclosing-prop-neighborhood-subtype-Pseudometric-Space

  is-prop-is-enclosing-neighborhood-subtype-Pseudometric-Space :
    is-prop is-enclosing-neighborhood-subtype-Pseudometric-Space
  is-prop-is-enclosing-neighborhood-subtype-Pseudometric-Space =
    is-prop-type-Prop
      is-enclosing-prop-neighborhood-subtype-Pseudometric-Space
```

### Local rational neighborhood subtypes on pseudometric spaces

```agda
module _
  {l1 l2 l : Level} (M : Pseudometric-Space l1 l2)
  (U : Rational-Neighborhood-Subtype l (type-Pseudometric-Space M))
  where

  is-local-prop-neighborhood-subtype-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l)
  is-local-prop-neighborhood-subtype-Pseudometric-Space =
    Π-Prop
      ( ℚ⁺ × ℚ⁺ × type-Pseudometric-Space M × type-Pseudometric-Space M)
      ( λ ( ε , δ , x , y) →
          ( is-bounded-prop-neighborhood-subtype-Pseudometric-Space
            ( M)
            ( U)
            ( ε)
            ( δ)
            ( x)
            ( y)) ∧
          ( is-enclosing-prop-neighborhood-subtype-Pseudometric-Space
            ( M)
            ( U)
            ( ε)
            ( δ)
            ( x)
            ( y)))

  is-local-neighborhood-subtype-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l)
  is-local-neighborhood-subtype-Pseudometric-Space =
    type-Prop is-local-prop-neighborhood-subtype-Pseudometric-Space

  is-prop-is-local-neighborhood-subtype-Pseudometric-Space :
    is-prop is-local-neighborhood-subtype-Pseudometric-Space
  is-prop-is-local-neighborhood-subtype-Pseudometric-Space =
    is-prop-type-Prop is-local-prop-neighborhood-subtype-Pseudometric-Space
```
