# The circle

```agda
module synthetic-homotopy-theory.circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import higher-group-theory.higher-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.spheres
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-cover-circle
open import synthetic-homotopy-theory.universal-property-circle

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

**The circle** is the initial type equipped with a base point and a
[loop](synthetic-homotopy-theory.loop-spaces.md).

## Postulates

```agda
postulate
  𝕊¹ : UU lzero

postulate
  base-𝕊¹ : 𝕊¹

postulate
  loop-𝕊¹ : base-𝕊¹ ＝ base-𝕊¹

free-loop-𝕊¹ : free-loop 𝕊¹
free-loop-𝕊¹ = base-𝕊¹ , loop-𝕊¹

𝕊¹-Pointed-Type : Pointed-Type lzero
𝕊¹-Pointed-Type = 𝕊¹ , base-𝕊¹

postulate
  ind-𝕊¹ : induction-principle-circle free-loop-𝕊¹
```

## Properties

### The dependent universal property of the circle

```agda
dependent-universal-property-𝕊¹ :
  dependent-universal-property-circle free-loop-𝕊¹
dependent-universal-property-𝕊¹ =
  dependent-universal-property-induction-principle-circle free-loop-𝕊¹ ind-𝕊¹

uniqueness-dependent-universal-property-𝕊¹ :
  {l : Level} {P : 𝕊¹ → UU l} (k : free-dependent-loop free-loop-𝕊¹ P) →
  is-contr
    ( Σ ( (x : 𝕊¹) → P x)
        ( λ h →
          Eq-free-dependent-loop free-loop-𝕊¹ P
            ( ev-free-loop-Π free-loop-𝕊¹ P h) k))
uniqueness-dependent-universal-property-𝕊¹ {l} {P} =
  uniqueness-dependent-universal-property-circle
    free-loop-𝕊¹
    dependent-universal-property-𝕊¹

module _
  {l : Level} (P : 𝕊¹ → UU l) (p0 : P base-𝕊¹) (α : tr P loop-𝕊¹ p0 ＝ p0)
  where

  Π-𝕊¹ : UU l
  Π-𝕊¹ =
    Σ ( (x : 𝕊¹) → P x)
      ( λ h →
        Eq-free-dependent-loop free-loop-𝕊¹ P
          ( ev-free-loop-Π free-loop-𝕊¹ P h) (p0 , α))

  apply-dependent-universal-property-𝕊¹ : Π-𝕊¹
  apply-dependent-universal-property-𝕊¹ =
    center (uniqueness-dependent-universal-property-𝕊¹ (p0 , α))

  function-apply-dependent-universal-property-𝕊¹ : (x : 𝕊¹) → P x
  function-apply-dependent-universal-property-𝕊¹ =
    pr1 apply-dependent-universal-property-𝕊¹

  base-dependent-universal-property-𝕊¹ :
    function-apply-dependent-universal-property-𝕊¹ base-𝕊¹ ＝ p0
  base-dependent-universal-property-𝕊¹ =
    pr1 (pr2 apply-dependent-universal-property-𝕊¹)

  loop-dependent-universal-property-𝕊¹ :
    ( apd function-apply-dependent-universal-property-𝕊¹ loop-𝕊¹ ∙
      base-dependent-universal-property-𝕊¹) ＝
    ( ap (tr P loop-𝕊¹) base-dependent-universal-property-𝕊¹ ∙ α)
  loop-dependent-universal-property-𝕊¹ =
    pr2 (pr2 apply-dependent-universal-property-𝕊¹)
```

### The universal property of the circle

```agda
universal-property-𝕊¹ : universal-property-circle free-loop-𝕊¹
universal-property-𝕊¹ =
  universal-property-dependent-universal-property-circle
    ( free-loop-𝕊¹)
    ( dependent-universal-property-𝕊¹)

uniqueness-universal-property-𝕊¹ :
  {l : Level} {X : UU l} (α : free-loop X) →
  is-contr
    ( Σ ( 𝕊¹ → X)
        ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) α))
uniqueness-universal-property-𝕊¹ {l} {X} =
  uniqueness-universal-property-circle free-loop-𝕊¹ universal-property-𝕊¹ X

module _
  {l : Level} {X : UU l} (x : X) (α : x ＝ x)
  where

  Map-𝕊¹ : UU l
  Map-𝕊¹ =
    Σ ( 𝕊¹ → X)
      ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) (x , α))

  apply-universal-property-𝕊¹ : Map-𝕊¹
  apply-universal-property-𝕊¹ =
    center (uniqueness-universal-property-𝕊¹ (x , α))

  map-apply-universal-property-𝕊¹ : 𝕊¹ → X
  map-apply-universal-property-𝕊¹ =
    pr1 apply-universal-property-𝕊¹

  base-universal-property-𝕊¹ :
    map-apply-universal-property-𝕊¹ base-𝕊¹ ＝ x
  base-universal-property-𝕊¹ =
    pr1 (pr2 apply-universal-property-𝕊¹)

  loop-universal-property-𝕊¹ :
    ap map-apply-universal-property-𝕊¹ loop-𝕊¹ ∙ base-universal-property-𝕊¹ ＝
    base-universal-property-𝕊¹ ∙ α
  loop-universal-property-𝕊¹ =
    pr2 (pr2 apply-universal-property-𝕊¹)
```

### The loop of the circle is nontrivial

```agda
is-nontrivial-loop-𝕊¹ : loop-𝕊¹ ≠ refl
is-nontrivial-loop-𝕊¹ =
  is-nontrivial-loop-dependent-universal-property-circle
    ( free-loop-𝕊¹)
    ( dependent-universal-property-𝕊¹)
```

### The circle is 0-connected

```agda
mere-eq-𝕊¹ : (x y : 𝕊¹) → mere-eq x y
mere-eq-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → (y : 𝕊¹) → mere-eq x y)
    ( function-apply-dependent-universal-property-𝕊¹
      ( mere-eq base-𝕊¹)
      ( refl-mere-eq base-𝕊¹)
      ( eq-is-prop is-prop-type-trunc-Prop))
    ( eq-is-prop (is-prop-Π (λ y → is-prop-type-trunc-Prop)))

is-0-connected-𝕊¹ : is-0-connected 𝕊¹
is-0-connected-𝕊¹ = is-0-connected-mere-eq base-𝕊¹ (mere-eq-𝕊¹ base-𝕊¹)
```

### The circle as a higher group

```agda
𝕊¹-∞-Group : ∞-Group lzero
pr1 𝕊¹-∞-Group = 𝕊¹-Pointed-Type
pr2 𝕊¹-∞-Group = is-0-connected-𝕊¹
```

### The circle is equivalent to the 1-sphere

The [1-sphere](synthetic-homotopy-theory.spheres.md) is defined as the
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) of the
[0-sphere](synthetic-homotopy-theory.spheres.md). We may understand this as the
1-sphere having two points `N` and `S` and two
[identifications](foundation-core.identity-types.md) (meridians) `e, w : N = S`
between them. The following shows that the 1-sphere and the circle are
[equivalent](foundation-core.equivalences.md).

#### The map from the circle to the 1-sphere

The map from the circle to the 1-sphere is defined by mapping the basepoint to
`N` and the loop to the composite of `e` and the inverse of `w`, which forms a
loop at `N`. The choice of which meridian to start with is arbitrary, but
informs the rest of the construction hereafter.

```agda
north-sphere-1-loop : north-sphere 1 ＝ north-sphere 1
north-sphere-1-loop =
  ( meridian-sphere 0 (zero-Fin 1)) ∙
  ( inv (meridian-sphere 0 (one-Fin 1)))

sphere-1-circle : 𝕊¹ → sphere 1
sphere-1-circle =
  map-apply-universal-property-𝕊¹ (north-sphere 1) north-sphere-1-loop

sphere-1-circle-base-𝕊¹-eq-north-sphere-1 :
  sphere-1-circle base-𝕊¹ ＝ north-sphere 1
sphere-1-circle-base-𝕊¹-eq-north-sphere-1 =
  base-universal-property-𝕊¹ (north-sphere 1) north-sphere-1-loop

sphere-1-circle-base-𝕊¹-eq-south-sphere-1 :
  sphere-1-circle base-𝕊¹ ＝ south-sphere 1
sphere-1-circle-base-𝕊¹-eq-south-sphere-1 =
  ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1) ∙
  ( meridian-sphere 0 (one-Fin 1))
```

#### The map from the 1-sphere to the circle

The map from the 1-sphere to the circle is defined by mapping both `N` and `S`
to the basepoint, `e` to the loop and `w` to `refl` at the basepoint. Were we to
map both meridians to the loop, we would wrap the 1-sphere twice around the
circle, which would not form an equivalence.

```agda
map-sphere-0-eq-base-𝕊¹ : (sphere 0) → base-𝕊¹ ＝ base-𝕊¹
map-sphere-0-eq-base-𝕊¹ (inl n) = loop-𝕊¹
map-sphere-0-eq-base-𝕊¹ (inr n) = refl

suspension-structure-sphere-0-𝕊¹ :
  suspension-structure (sphere 0) 𝕊¹
pr1 suspension-structure-sphere-0-𝕊¹ = base-𝕊¹
pr1 (pr2 suspension-structure-sphere-0-𝕊¹) = base-𝕊¹
pr2 (pr2 suspension-structure-sphere-0-𝕊¹) = map-sphere-0-eq-base-𝕊¹

circle-sphere-1 : sphere 1 → 𝕊¹
circle-sphere-1 =
  cogap-suspension
    ( suspension-structure-sphere-0-𝕊¹)

circle-sphere-1-north-sphere-1-eq-base-𝕊¹ :
  circle-sphere-1 (north-sphere 1) ＝ base-𝕊¹
circle-sphere-1-north-sphere-1-eq-base-𝕊¹ =
  compute-north-cogap-suspension
    ( suspension-structure-sphere-0-𝕊¹)

circle-sphere-1-south-sphere-1-eq-base-𝕊¹ :
  circle-sphere-1 (south-sphere 1) ＝ base-𝕊¹
circle-sphere-1-south-sphere-1-eq-base-𝕊¹ =
  compute-south-cogap-suspension
    ( suspension-structure-sphere-0-𝕊¹)
```

#### The map from the circle to the 1-sphere has a section

Some care needs to be taken when proving this part of the equivalence. The point
`N` is mapped to the basepoint and then back to `N`, but so is the point `S`. It
needs to be further identified back with `S` using the meridian `w`. The
meridian `w` is thus mapped to `refl` and then back to `w ∙ refl = w`, while the
meridian `e` is mapped to the loop and then back to `w ∙ w⁻¹∙ e = e`.

```agda
sphere-1-circle-sphere-1-north-sphere-1 :
    ( sphere-1-circle (circle-sphere-1 (north-sphere 1))) ＝ ( north-sphere 1)
sphere-1-circle-sphere-1-north-sphere-1 =
  ( ap sphere-1-circle circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
  ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)

sphere-1-circle-sphere-1-south-sphere-1 :
    ( sphere-1-circle (circle-sphere-1 (south-sphere 1))) ＝ ( south-sphere 1)
sphere-1-circle-sphere-1-south-sphere-1 =
  ( ap sphere-1-circle circle-sphere-1-south-sphere-1-eq-base-𝕊¹) ∙
  ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)

apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1 :
  ( n : Fin 2) →
  coherence-square-identifications
    ( ap
      ( sphere-1-circle)
      ( ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹) ∙
        ( map-sphere-0-eq-base-𝕊¹ n)))
    ( ap sphere-1-circle (ap circle-sphere-1 (meridian-suspension n)))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1)
apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1
  n =
  ( inv
    ( assoc
      ( ap sphere-1-circle (ap circle-sphere-1 (meridian-suspension n)))
      ( ap sphere-1-circle circle-sphere-1-south-sphere-1-eq-base-𝕊¹)
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1))) ∙
  ( right-whisker-concat
    ( inv
      ( ap-concat
        ( sphere-1-circle)
        ( ap circle-sphere-1 (meridian-sphere 0 n))
        ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹)))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)) ∙
  ( ap
    ( λ x →
      ( ap sphere-1-circle x) ∙
      ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1))
    ( compute-meridian-cogap-suspension
      ( suspension-structure-sphere-0-𝕊¹)
      ( n)))

apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1 :
  coherence-square-identifications
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
    ( ap sphere-1-circle loop-𝕊¹)
    ( meridian-sphere 0 (zero-Fin 1))
    ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)
apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1 =
  ( inv
    ( assoc
      ( ap sphere-1-circle loop-𝕊¹)
      ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
      ( meridian-sphere 0 (one-Fin 1)))) ∙
  ( right-whisker-concat
    ( loop-universal-property-𝕊¹
      ( north-sphere 1)
      ( north-sphere-1-loop))
    ( meridian-sphere 0 (one-Fin 1))) ∙
  ( assoc
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
    ( north-sphere-1-loop)
    ( meridian-sphere 0 (one-Fin 1))) ∙
  ( left-whisker-concat
    ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
    ( is-section-inv-concat'
      ( meridian-sphere 0 (one-Fin 1))
      ( meridian-sphere 0 (zero-Fin 1))))

map-sphere-1-circle-sphere-1-meridian :
  ( n : Fin 2) →
  ( dependent-identification
    ( λ x → (sphere-1-circle (circle-sphere-1 x)) ＝ x)
    ( meridian-suspension-structure
      ( suspension-structure-suspension (Fin 2))
      ( n))
    ( sphere-1-circle-sphere-1-north-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1))
map-sphere-1-circle-sphere-1-meridian (inl (inr n)) =
  map-compute-dependent-identification-eq-value-comp-id
    ( sphere-1-circle)
    ( circle-sphere-1)
    ( meridian-sphere 0 (inl (inr n)))
    ( sphere-1-circle-sphere-1-north-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1)
    ( ( apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1
        ( inl (inr n))) ∙
      ( right-whisker-concat
        ( ap-concat
          ( sphere-1-circle)
          ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
          ( loop-𝕊¹))
        ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)) ∙
      ( assoc
        ( ap sphere-1-circle (circle-sphere-1-north-sphere-1-eq-base-𝕊¹))
        ( ap sphere-1-circle loop-𝕊¹)
        ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1)) ∙
      ( left-whisker-concat
        ( ap sphere-1-circle (circle-sphere-1-north-sphere-1-eq-base-𝕊¹))
        ( apply-loop-universal-property-𝕊¹-sphere-1-circle-sphere-1)) ∙
      ( inv
        ( assoc
          ( ap sphere-1-circle (circle-sphere-1-north-sphere-1-eq-base-𝕊¹))
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
          ( meridian-sphere 0 (zero-Fin 1)))))
map-sphere-1-circle-sphere-1-meridian (inr n) =
  map-compute-dependent-identification-eq-value-comp-id
    ( sphere-1-circle)
    ( circle-sphere-1)
    ( meridian-sphere 0 (inr n))
    ( sphere-1-circle-sphere-1-north-sphere-1)
    ( sphere-1-circle-sphere-1-south-sphere-1)
    ( ( apply-up-suspension-meridian-suspension-sphere-1-circle-sphere-1
        ( inr n)) ∙
      ( ap
        ( λ x →
          ( ap sphere-1-circle x) ∙
          ( sphere-1-circle-base-𝕊¹-eq-south-sphere-1))
        ( right-unit {p = circle-sphere-1-north-sphere-1-eq-base-𝕊¹})) ∙
      ( inv
        ( assoc
          ( ap sphere-1-circle circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
          ( meridian-sphere 0 (one-Fin 1)))))

dependent-suspension-structure-sphere-1-circle-sphere-1 :
  dependent-suspension-structure
    ( λ x → (sphere-1-circle (circle-sphere-1 x)) ＝ x)
    ( suspension-structure-suspension (Fin 2))
pr1 dependent-suspension-structure-sphere-1-circle-sphere-1 =
  sphere-1-circle-sphere-1-north-sphere-1
pr1 (pr2 dependent-suspension-structure-sphere-1-circle-sphere-1) =
  sphere-1-circle-sphere-1-south-sphere-1
pr2 (pr2 dependent-suspension-structure-sphere-1-circle-sphere-1) =
  map-sphere-1-circle-sphere-1-meridian

sphere-1-circle-sphere-1 : section sphere-1-circle
pr1 sphere-1-circle-sphere-1 = circle-sphere-1
pr2 sphere-1-circle-sphere-1 =
  dependent-cogap-suspension
    ( λ x → (sphere-1-circle (circle-sphere-1 x)) ＝ x)
    ( dependent-suspension-structure-sphere-1-circle-sphere-1)
```

#### The map from the circle to the 1-sphere has a retraction

The basepoint is mapped to `N` and then back to the basepoint, while the loop is
mapped to `w⁻¹∙ e` and then back to `refl⁻¹ ∙ loop = loop`.

```agda
circle-sphere-1-circle-base-𝕊¹ :
  circle-sphere-1 (sphere-1-circle base-𝕊¹) ＝ base-𝕊¹
circle-sphere-1-circle-base-𝕊¹ =
  ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1) ∙
  ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)

apply-up-suspension-meridian-one-suspension-circle-sphere-1-circle :
  coherence-square-identifications
    ( refl)
    ( ap circle-sphere-1 (inv (meridian-sphere 0 (one-Fin 1))))
    ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹)
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
apply-up-suspension-meridian-one-suspension-circle-sphere-1-circle =
  ( right-whisker-concat
    ( ap-inv
      ( circle-sphere-1)
      ( meridian-suspension (one-Fin 1)))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( inv right-unit) ∙
  ( assoc
    ( inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
    ( refl)) ∙
  ( left-whisker-concat
    ( inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
    ( inv
      ( compute-meridian-cogap-suspension
          ( suspension-structure-sphere-0-𝕊¹)
          ( one-Fin 1)))) ∙
  ( inv
    ( assoc
      ( inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
      ( ap circle-sphere-1 (meridian-suspension (one-Fin 1)))
      ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹))) ∙
  ( right-whisker-concat
    ( left-inv (ap circle-sphere-1 (meridian-suspension (one-Fin 1))))
    ( circle-sphere-1-south-sphere-1-eq-base-𝕊¹))

apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circle :
  coherence-square-identifications
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
    ( ap (circle-sphere-1) (north-sphere-1-loop))
    ( loop-𝕊¹)
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circle =
  ( right-whisker-concat
    ( ap-concat
      ( circle-sphere-1)
      ( meridian-sphere 0 (zero-Fin 1))
      ( inv (meridian-suspension (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( assoc
    ( ap circle-sphere-1 (meridian-suspension (zero-Fin 1)))
    ( ap circle-sphere-1 (inv ( meridian-sphere 0 (one-Fin 1))))
    ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
  ( left-whisker-concat
    ( ap circle-sphere-1 (meridian-suspension (zero-Fin 1)))
    ( apply-up-suspension-meridian-one-suspension-circle-sphere-1-circle)) ∙
  ( compute-meridian-cogap-suspension
    ( suspension-structure-sphere-0-𝕊¹)
    ( zero-Fin 1))

circle-sphere-1-circle-loop-𝕊¹ :
  coherence-square-identifications
    ( circle-sphere-1-circle-base-𝕊¹)
    ( ap circle-sphere-1 (ap sphere-1-circle loop-𝕊¹))
    ( loop-𝕊¹)
    ( circle-sphere-1-circle-base-𝕊¹)
circle-sphere-1-circle-loop-𝕊¹ =
  ( inv
    ( assoc
      ( ap circle-sphere-1 (ap sphere-1-circle loop-𝕊¹))
      ( ap
        ( circle-sphere-1)
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
    ( right-whisker-concat
      ( inv
        ( ap-concat
          ( circle-sphere-1)
          ( ap sphere-1-circle loop-𝕊¹)
          ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
    ( right-whisker-concat
      ( ap
        ( ap circle-sphere-1)
        ( loop-universal-property-𝕊¹
          ( north-sphere 1)
          ( north-sphere-1-loop)))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
    ( right-whisker-concat
      ( ap-concat
        ( circle-sphere-1)
        ( sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
        ( north-sphere-1-loop))
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
    ( assoc
      ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
      ( ap circle-sphere-1 north-sphere-1-loop)
      ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)) ∙
    ( left-whisker-concat
      ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
      ( apply-up-suspension-meridian-zero-suspension-circle-sphere-1-circle)) ∙
    ( inv
      ( assoc
        ( ap circle-sphere-1 sphere-1-circle-base-𝕊¹-eq-north-sphere-1)
        ( circle-sphere-1-north-sphere-1-eq-base-𝕊¹)
        ( loop-𝕊¹))))

circle-sphere-1-circle : retraction sphere-1-circle
pr1 circle-sphere-1-circle = circle-sphere-1
pr2 circle-sphere-1-circle =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → (circle-sphere-1 (sphere-1-circle x)) ＝ x)
    ( circle-sphere-1-circle-base-𝕊¹)
    ( map-compute-dependent-identification-eq-value-comp-id
      ( circle-sphere-1)
      ( sphere-1-circle)
      ( loop-𝕊¹)
      ( circle-sphere-1-circle-base-𝕊¹)
      ( circle-sphere-1-circle-base-𝕊¹)
      ( circle-sphere-1-circle-loop-𝕊¹))
```

#### The equivalence between the circle and the 1-sphere

```agda
is-equiv-sphere-1-circle : is-equiv sphere-1-circle
pr1 is-equiv-sphere-1-circle =
  sphere-1-circle-sphere-1
pr2 is-equiv-sphere-1-circle =
  circle-sphere-1-circle

equiv-sphere-1-circle : 𝕊¹ ≃ sphere 1
pr1 equiv-sphere-1-circle = sphere-1-circle
pr2 equiv-sphere-1-circle = is-equiv-sphere-1-circle
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
