# Premetric structures on types

```agda
module metric-spaces.premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "premetric" Disambiguation="structure on a type" Agda=Premetric}}
is a type family of
[proposition-valued binary relations](foundation.binary-relations.md) indexed by
the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

Given a premetric `B` on `A` and some
positive rational number `d : ℚ⁺` such that `B d x y` holds for some pair of points `x y : A`, we interpret `d` as an {{#concept "upper bound" Disambiguation="on distance in with respect to a premetric structure"}}
on the distance between `x` and `y` with respect to the premetric.

## Definitions

### Premetric structures

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Premetric : UU (l1 ⊔ lsuc l2)
  Premetric = ℚ⁺ → Relation-Prop l2 A
```

### Closeness relation in a premetric

Two points `x` and `y` in a type `A` are in a
{{#concept "`d`-neighborhood" Disambiguation="in a premetric" Agda=neighborhood-Premetric}}
in a premetric `B` for some positive rational numvber `d` if `B d x y` holds.

In this case, `d` is called an
{{#concept "upper bound" Disambiguation="on the distance in a premetric" Agda=is-upper-bound-dist-Premetric}}
on the distance between `x` and `y` in the premetric `B`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  neighborhood-Premetric : ℚ⁺ → A → A → UU l2
  neighborhood-Premetric d = type-Relation-Prop (B d)

  is-prop-neighborhood-Premetric :
    (d : ℚ⁺) (x y : A) → is-prop (neighborhood-Premetric d x y)
  is-prop-neighborhood-Premetric d = is-prop-type-Relation-Prop (B d)

  is-upper-bound-dist-Premetric : A → A → ℚ⁺ → UU l2
  is-upper-bound-dist-Premetric x y d = neighborhood-Premetric d x y

  is-prop-is-upper-bound-dist-Premetric :
    (x y : A) (d : ℚ⁺) → is-prop (is-upper-bound-dist-Premetric x y d)
  is-prop-is-upper-bound-dist-Premetric x y d =
    is-prop-neighborhood-Premetric d x y
```

### Indistinguishable elements with respect to a premetric

Two elements `x` and `y` are
{{#concept "indistinguishable" Disambiguation="with respect to a premetric" Agda=is-indistinguishable-Premetric}}
in a premetric if `x` and `y` are `d`-neighbors for any positive rational `d`
i.e. if their distance is bounded by any positive rational.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-indistinguishable-prop-Premetric : Prop l2
  is-indistinguishable-prop-Premetric =
    Π-Prop ℚ⁺ (λ (d : ℚ⁺) → B d x y)

  is-indistinguishable-Premetric : UU l2
  is-indistinguishable-Premetric =
    type-Prop is-indistinguishable-prop-Premetric

  is-prop-is-indistinguishable-Premetric :
    is-prop is-indistinguishable-Premetric
  is-prop-is-indistinguishable-Premetric =
    is-prop-type-Prop is-indistinguishable-prop-Premetric
```

### Separation relation with respect to a premetric

Two points `x` and `y` are
{{#concept "separated" Disambiguation="with respect to a premetric" Agda=is-separated-pt-Premetric}}
in a premetric if there exists some positive rational `d` such that `x` and `y`
are not `d`-neighbors.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-separated-pt-prop-Premetric : Prop l2
  is-separated-pt-prop-Premetric =
    ∃ ℚ⁺ (λ d → neg-Prop (B d x y))

  is-separated-pt-Premetric : UU l2
  is-separated-pt-Premetric =
    type-Prop is-separated-pt-prop-Premetric

  is-prop-is-separated-pt-Premetric :
    is-prop is-separated-pt-Premetric
  is-prop-is-separated-pt-Premetric =
    is-prop-type-Prop is-separated-pt-prop-Premetric
```

## Properties

### Points separated by a premetric structure are not indistinguishable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-not-indistinguishable-is-separated-pt-Premetric :
    is-separated-pt-Premetric B x y → ¬ (is-indistinguishable-Premetric B x y)
  is-not-indistinguishable-is-separated-pt-Premetric S I =
    elim-exists
      ( empty-Prop)
      ( λ d H → H (I d))
      ( S)
```

### Equality of premetric structures

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Premetric l2 A)
  where

  Eq-prop-Premetric : Premetric l2 A → Prop (l1 ⊔ l2)
  Eq-prop-Premetric N' =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y → N d x y ⇔ N' d x y)))

  Eq-Premetric : Premetric l2 A → UU (l1 ⊔ l2)
  Eq-Premetric N' = type-Prop (Eq-prop-Premetric N')

  is-prop-Eq-Premetric : (N' : Premetric l2 A) → is-prop (Eq-Premetric N')
  is-prop-Eq-Premetric N' = is-prop-type-Prop (Eq-prop-Premetric N')

  refl-Eq-Premetric : Eq-Premetric N
  refl-Eq-Premetric d x y = id-iff

  Eq-eq-Premetric : (N' : Premetric l2 A) → (N ＝ N') → Eq-Premetric N'
  Eq-eq-Premetric .N refl = refl-Eq-Premetric

  eq-Eq-Premetric : (N' : Premetric l2 A) → Eq-Premetric N' → N ＝ N'
  eq-Eq-Premetric N' H =
    eq-htpy
      ( λ d →
        eq-htpy
        ( λ x →
          eq-htpy
          ( λ y →
            eq-iff' (N d x y) (N' d x y) (H d x y))))

  is-torsorial-Eq-Premetric : is-torsorial Eq-Premetric
  is-torsorial-Eq-Premetric =
    ( N , refl-Eq-Premetric) ,
    ( λ (N' , e) →
      eq-type-subtype
        ( Eq-prop-Premetric)
        ( eq-Eq-Premetric N' e))

  is-fiberwise-equiv-Eq-eq-Premetric :
    (N' : Premetric l2 A) → is-equiv (Eq-eq-Premetric N')
  is-fiberwise-equiv-Eq-eq-Premetric =
    fundamental-theorem-id is-torsorial-Eq-Premetric Eq-eq-Premetric

  equiv-Eq-eq-Premetric :
    (N' : Premetric l2 A) → (N ＝ N') ≃ (Eq-Premetric N')
  equiv-Eq-eq-Premetric N' =
    Eq-eq-Premetric N' , is-fiberwise-equiv-Eq-eq-Premetric N'
```

### Characterization of the transport of premetric structures along equality of types

```agda
module _
  {l1 l2 : Level} (A : UU l1)
  where

  eq-map-eq-tr-Premetric :
    (B : UU l1) (e : A ＝ B) (S : Premetric l2 A) →
    Eq-Premetric S (λ d x y → tr (Premetric l2) e S d (map-eq e x) (map-eq e y))
  eq-map-eq-tr-Premetric .A refl S = refl-Eq-Premetric S

  eq-map-inv-eq-tr-Premetric :
    (B : UU l1) (e : A ＝ B) (S : Premetric l2 A) →
    Eq-Premetric
      (tr (Premetric l2) e S)
      (λ d x y → S d (map-inv-eq e x) (map-inv-eq e y))
  eq-map-inv-eq-tr-Premetric .A refl S = refl-Eq-Premetric S
```

## References

Our definition of a premetric follows Definition 4.5.2 from {{#cite Booij2020PhD}}.

{{#bibliography}}

## See also

- [Booij premetric spaces](https://ncatlab.org/nlab/show/Booij+premetric+space)
  at $n$Lab.
