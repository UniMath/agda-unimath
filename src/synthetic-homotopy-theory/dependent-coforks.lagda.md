# Dependent coforks

```agda
module synthetic-homotopy-theory.dependent-coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.constant-type-families
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-spans
```

</details>

## Idea

Given a [double arrow](foundation.double-arrows.md) `f, g : A → B`, a
[cofork](synthetic-homotopy-theory.coforks.md) `e : B → X` with vertex `X`, and
a type family `P : X → 𝒰` over `X`, we may construct _dependent_ coforks on `P`
over `e`.

A
{{#concept "dependent cofork" Disambiguation="of types" Agda=dependent-cofork}}
on `P` over `e` consists of a dependent map

```text
k : (b : B) → P (e b)
```

and a family of
[dependent identifications](foundation.dependent-identifications.md) indexed by
`A`

```text
(a : A) → dependent-identification P (H a) (k (f a)) (k (g a)).
```

Dependent coforks are an analog of
[dependent cocones under spans](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
for double arrows.

## Definitions

### Dependent coforks

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X) (P : X → UU l4)
  where

  dependent-cofork : UU (l1 ⊔ l2 ⊔ l4)
  dependent-cofork =
    Σ ( (b : codomain-double-arrow a) → P (map-cofork a e b))
      ( λ k →
        (x : domain-double-arrow a) →
        dependent-identification P
          ( coh-cofork a e x)
          ( k (left-map-double-arrow a x))
          ( k (right-map-double-arrow a x)))

module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  {e : cofork a X} (P : X → UU l4)
  (k : dependent-cofork a e P)
  where

  map-dependent-cofork : (b : codomain-double-arrow a) → P (map-cofork a e b)
  map-dependent-cofork = pr1 k

  coherence-dependent-cofork :
    (x : domain-double-arrow a) →
    dependent-identification P
      ( coh-cofork a e x)
      ( map-dependent-cofork (left-map-double-arrow a x))
      ( map-dependent-cofork (right-map-double-arrow a x))
  coherence-dependent-cofork = pr2 k
```

### Homotopies of dependent coforks

A homotopy between dependent coforks is a homotopy between the underlying maps,
together with a coherence condition.

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  {e : cofork a X} (P : X → UU l4)
  where

  coherence-htpy-dependent-cofork :
    (k k' : dependent-cofork a e P) →
    (K : map-dependent-cofork a P k ~ map-dependent-cofork a P k') →
    UU (l1 ⊔ l4)
  coherence-htpy-dependent-cofork k k' K =
    ( (coherence-dependent-cofork a P k) ∙h (K ·r right-map-double-arrow a)) ~
    ( ( (λ {x} → tr P (coh-cofork a e x)) ·l (K ·r left-map-double-arrow a)) ∙h
      ( coherence-dependent-cofork a P k'))

  htpy-dependent-cofork :
    (k k' : dependent-cofork a e P) →
    UU (l1 ⊔ l2 ⊔ l4)
  htpy-dependent-cofork k k' =
    Σ ( map-dependent-cofork a P k ~ map-dependent-cofork a P k')
      ( coherence-htpy-dependent-cofork k k')
```

### Obtaining dependent coforks as postcomposition of coforks with dependent maps

One way to obtains dependent coforks is to postcompose the underlying cofork by
a dependent map, according to the diagram

```text
     g
   ----->     e              h
 A -----> B -----> (x : X) -----> (P x)
     f
```

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X)
  where

  dependent-cofork-map :
    {l : Level} {P : X → UU l} → ((x : X) → P x) → dependent-cofork a e P
  pr1 (dependent-cofork-map h) = h ∘ map-cofork a e
  pr2 (dependent-cofork-map h) = apd h ∘ coh-cofork a e
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  {e : cofork a X} (P : X → UU l4)
  where

  refl-htpy-dependent-cofork :
    (k : dependent-cofork a e P) →
    htpy-dependent-cofork a P k k
  pr1 (refl-htpy-dependent-cofork k) = refl-htpy
  pr2 (refl-htpy-dependent-cofork k) = right-unit-htpy

  htpy-dependent-cofork-eq :
    (k k' : dependent-cofork a e P) →
    (k ＝ k') → htpy-dependent-cofork a P k k'
  htpy-dependent-cofork-eq k .k refl = refl-htpy-dependent-cofork k

  abstract
    is-torsorial-htpy-dependent-cofork :
      (k : dependent-cofork a e P) →
      is-torsorial (htpy-dependent-cofork a P k)
    is-torsorial-htpy-dependent-cofork k =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-dependent-cofork a P k))
        ( map-dependent-cofork a P k , refl-htpy)
        ( is-torsorial-htpy
          ( coherence-dependent-cofork a P k ∙h refl-htpy))

    is-equiv-htpy-dependent-cofork-eq :
      (k k' : dependent-cofork a e P) →
      is-equiv (htpy-dependent-cofork-eq k k')
    is-equiv-htpy-dependent-cofork-eq k =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cofork k)
        ( htpy-dependent-cofork-eq k)

  eq-htpy-dependent-cofork :
    (k k' : dependent-cofork a e P) →
    htpy-dependent-cofork a P k k' → k ＝ k'
  eq-htpy-dependent-cofork k k' =
    map-inv-is-equiv (is-equiv-htpy-dependent-cofork-eq k k')
```

### Dependent coforks on constant type families are equivalent to nondependent coforks

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X) (Y : UU l4)
  where

  compute-dependent-cofork-constant-family :
    dependent-cofork a e (λ _ → Y) ≃ cofork a Y
  compute-dependent-cofork-constant-family =
    equiv-tot
      ( λ h →
        equiv-Π-equiv-family
          ( λ x →
            equiv-concat
              ( inv
                ( tr-constant-type-family
                  ( coh-cofork a e x)
                  ( h (left-map-double-arrow a x))))
              ( h (right-map-double-arrow a x))))

  map-compute-dependent-cofork-constant-family :
    dependent-cofork a e (λ _ → Y) → cofork a Y
  map-compute-dependent-cofork-constant-family =
    map-equiv compute-dependent-cofork-constant-family

  triangle-compute-dependent-cofork-constant-family :
    coherence-triangle-maps
      ( cofork-map a e)
      ( map-compute-dependent-cofork-constant-family)
      ( dependent-cofork-map a e)
  triangle-compute-dependent-cofork-constant-family h =
    eq-htpy-cofork a
      ( cofork-map a e h)
      ( map-compute-dependent-cofork-constant-family
        ( dependent-cofork-map a e h))
      ( ( refl-htpy) ,
        ( right-unit-htpy ∙h
          ( λ x →
            left-transpose-eq-concat _ _ _
              ( inv (apd-constant-type-family h (coh-cofork a e x))))))
```

### Dependent coforks are special cases of dependent cocones under spans

The type of dependent coforks on `P` over `e` is equivalent to the type of
[dependent cocones](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
on `P` over a cocone corresponding to `e` via `cocone-codiagonal-cofork`.

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X)
  where

  module _
    {l4 : Level} (P : X → UU l4)
    where

    dependent-cofork-dependent-cocone-codiagonal :
      dependent-cocone
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e)
        ( P) →
      dependent-cofork a e P
    pr1 (dependent-cofork-dependent-cocone-codiagonal k) =
      vertical-map-dependent-cocone
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e)
        ( P)
        ( k)
    pr2 (dependent-cofork-dependent-cocone-codiagonal k) x =
      inv
        ( ap
          ( tr P (coh-cofork a e x))
          ( coherence-square-dependent-cocone
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e)
            ( P)
            ( k)
            ( inl x))) ∙
      coherence-square-dependent-cocone
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e)
        ( P)
        ( k)
        ( inr x)

    dependent-cocone-codiagonal-dependent-cofork :
      dependent-cofork a e P →
      dependent-cocone
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e)
        ( P)
    pr1 (dependent-cocone-codiagonal-dependent-cofork k) =
      map-dependent-cofork a P k ∘ left-map-double-arrow a
    pr1 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) =
      map-dependent-cofork a P k
    pr2 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) (inl a) =
      refl
    pr2 (pr2 (dependent-cocone-codiagonal-dependent-cofork k)) (inr x) =
      coherence-dependent-cofork a P k x

    abstract
      is-section-dependent-cocone-codiagonal-dependent-cofork :
        ( ( dependent-cofork-dependent-cocone-codiagonal) ∘
          ( dependent-cocone-codiagonal-dependent-cofork)) ~
        ( id)
      is-section-dependent-cocone-codiagonal-dependent-cofork k =
        eq-htpy-dependent-cofork a P
          ( dependent-cofork-dependent-cocone-codiagonal
            ( dependent-cocone-codiagonal-dependent-cofork k))
          ( k)
          ( refl-htpy , right-unit-htpy)

      is-retraction-dependent-cocone-codiagonal-dependent-cofork :
        ( ( dependent-cocone-codiagonal-dependent-cofork) ∘
          ( dependent-cofork-dependent-cocone-codiagonal)) ~
        ( id)
      is-retraction-dependent-cocone-codiagonal-dependent-cofork d =
        eq-htpy-dependent-cocone
          ( vertical-map-span-cocone-cofork a)
          ( horizontal-map-span-cocone-cofork a)
          ( cocone-codiagonal-cofork a e)
          ( P)
          ( dependent-cocone-codiagonal-dependent-cofork
            ( dependent-cofork-dependent-cocone-codiagonal d))
          ( d)
          ( inv-htpy
            ( ( coherence-square-dependent-cocone
                ( vertical-map-span-cocone-cofork a)
                ( horizontal-map-span-cocone-cofork a)
                ( cocone-codiagonal-cofork a e)
                ( P)
                ( d)) ∘
              ( inl)) ,
            ( refl-htpy) ,
            ( right-unit-htpy ∙h
              ( λ where
                (inl x) →
                  inv
                    ( ( right-whisker-concat
                        ( ap-id
                          ( inv
                            ( coherence-square-dependent-cocone
                              ( vertical-map-span-cocone-cofork a)
                              ( horizontal-map-span-cocone-cofork a)
                              ( cocone-codiagonal-cofork a e)
                              ( P)
                              ( d)
                              ( inl x))))
                        ( coherence-square-dependent-cocone
                          ( vertical-map-span-cocone-cofork a)
                          ( horizontal-map-span-cocone-cofork a)
                          ( cocone-codiagonal-cofork a e)
                          ( P)
                          ( d)
                          ( inl x))) ∙
                      ( left-inv
                        ( coherence-square-dependent-cocone
                          ( vertical-map-span-cocone-cofork a)
                          ( horizontal-map-span-cocone-cofork a)
                          ( cocone-codiagonal-cofork a e)
                          ( P)
                          ( d)
                          ( inl x))))
                (inr x) →
                  right-whisker-concat
                    ( inv
                      ( ap-inv
                        ( tr P (coh-cofork a e x))
                        ( coherence-square-dependent-cocone
                          ( vertical-map-span-cocone-cofork a)
                          ( horizontal-map-span-cocone-cofork a)
                          ( cocone-codiagonal-cofork a e)
                          ( P)
                          ( d)
                          ( inl x))))
                    ( coherence-square-dependent-cocone
                      ( vertical-map-span-cocone-cofork a)
                      ( horizontal-map-span-cocone-cofork a)
                      ( cocone-codiagonal-cofork a e)
                      ( P)
                      ( d)
                      ( inr x)))))

    is-equiv-dependent-cofork-dependent-cocone-codiagonal :
      is-equiv dependent-cofork-dependent-cocone-codiagonal
    is-equiv-dependent-cofork-dependent-cocone-codiagonal =
      is-equiv-is-invertible
        ( dependent-cocone-codiagonal-dependent-cofork)
        ( is-section-dependent-cocone-codiagonal-dependent-cofork)
        ( is-retraction-dependent-cocone-codiagonal-dependent-cofork)

    equiv-dependent-cofork-dependent-cocone-codiagonal :
      dependent-cocone
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e)
        ( P) ≃
      dependent-cofork a e P
    pr1 equiv-dependent-cofork-dependent-cocone-codiagonal =
      dependent-cofork-dependent-cocone-codiagonal
    pr2 equiv-dependent-cofork-dependent-cocone-codiagonal =
      is-equiv-dependent-cofork-dependent-cocone-codiagonal

  triangle-dependent-cofork-dependent-cocone-codiagonal :
    {l4 : Level} (P : X → UU l4) →
    coherence-triangle-maps
      ( dependent-cofork-map a e)
      ( dependent-cofork-dependent-cocone-codiagonal P)
      ( dependent-cocone-map
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)
        ( cocone-codiagonal-cofork a e)
        ( P))
  triangle-dependent-cofork-dependent-cocone-codiagonal P h =
    eq-htpy-dependent-cofork a P
      ( dependent-cofork-map a e h)
      ( dependent-cofork-dependent-cocone-codiagonal P
        ( dependent-cocone-map
          ( vertical-map-span-cocone-cofork a)
          ( horizontal-map-span-cocone-cofork a)
          ( cocone-codiagonal-cofork a e)
          ( P)
          ( h)))
      ( refl-htpy ,
        right-unit-htpy)
```
