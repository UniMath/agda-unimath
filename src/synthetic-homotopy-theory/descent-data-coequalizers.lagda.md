# Descent data for coequalizers

```agda
module synthetic-homotopy-theory.descent-data-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.function-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
```

</details>

## Idea

Given a [double arrow](foundation.double-arrows.md) `f, g : A → B`, we may ask
how to construct type families over its
[coequalizer](synthetic-homotopy-theory.coequalizers.md).

The data required to construct a type family is called
{{#concept "descent data" Disambiguation="coequalizers" Agda=descent-data-coequalizer}}
for coequalizers. It consists of a type family `PB : B → 𝒰`, and a family of
[equivalences](foundation-core.equivalences.md)
`PA: (a : A) → PB (f a) ≃ PB (g a)`.

The fact that the type of descent data over a double arrow is equivalent to the
type of type families over its coequalizer is recorded in
[`descent-property-coequalizers`](synthetic-homotopy-theory.descent-property-coequalizers.md).

The [identity type](foundation-core.identity-types.md) of descent data for
coequalizers is characterized in
[`equivalences-descent-data-coequalizers`](synthetic-homotopy-theory.equivalences-descent-data-coequalizers.md).

## Definitions

### Descent data for coequalizers

```agda
module _
  {l1 l2 : Level} (F : double-arrow l1 l2)
  where

  descent-data-coequalizer : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  descent-data-coequalizer l =
    Σ ( codomain-double-arrow F → UU l)
      ( λ PB →
        (a : domain-double-arrow F) →
        PB (left-map-double-arrow F a) ≃
        PB (right-map-double-arrow F a))
```

### Components of descent data for coequalizers

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  where

  family-descent-data-coequalizer : codomain-double-arrow F → UU l3
  family-descent-data-coequalizer = pr1 P

  equiv-family-descent-data-coequalizer :
    (a : domain-double-arrow F) →
    family-descent-data-coequalizer (left-map-double-arrow F a) ≃
    family-descent-data-coequalizer (right-map-double-arrow F a)
  equiv-family-descent-data-coequalizer = pr2 P

  map-family-descent-data-coequalizer :
    (a : domain-double-arrow F) →
    family-descent-data-coequalizer (left-map-double-arrow F a) →
    family-descent-data-coequalizer (right-map-double-arrow F a)
  map-family-descent-data-coequalizer a =
    map-equiv (equiv-family-descent-data-coequalizer a)

  is-equiv-map-family-descent-data-coequalizer :
    (a : domain-double-arrow F) →
    is-equiv (map-family-descent-data-coequalizer a)
  is-equiv-map-family-descent-data-coequalizer s =
    is-equiv-map-equiv (equiv-family-descent-data-coequalizer s)
```

### Descent data induced by families over coforks

Given a cofork

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

and a type family `P : X → 𝒰`, we construct a descent datum: the family
`PB : B → 𝒰` is obtained by composition `P ∘ e`, and the equivalence
`PA : (a : A) → P(e(f(a))) ≃ P(e(g(a)))` is obtained by transporting along the
coherence of the cofork.

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  {X : UU l3} (c : cofork F X)
  where

  descent-data-family-cofork :
    {l4 : Level} → (X → UU l4) → descent-data-coequalizer F l4
  pr1 (descent-data-family-cofork P) =
    P ∘ map-cofork c
  pr2 (descent-data-family-cofork P) a =
    equiv-tr P (coh-cofork c a)
```
