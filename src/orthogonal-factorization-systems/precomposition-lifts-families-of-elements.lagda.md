# Precomposition of lifts of families of elements by maps

```agda
module orthogonal-factorization-systems.precomposition-lifts-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.precomposition-functions
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.lifts-families-of-elements
```

</details>

## Idea

Consider a type family `B : A → 𝓤` and a map `a : I → A`. Then, given a map
`f : J → I`, we may pull back a
[lift](orthogonal-factorization-systems.lifts-families-of-elements.md) of `a` to
a lift of `a ∘ f`.

In other words, given a diagram

```text
                Σ (x : A) (B x)
                      |
                      | pr1
                      |
                      v
  J ------> I ------> A         ,
       f         a
```

we get a map of diagonals

```text
  ((i : I) → B (a i)) → ((j : J) → B (a (f j))) .
```

This map of lifts induces a map from lifted families of elements indexed by `I`
to lifted families of elements indexed by `J`.

## Definitions

### Precomposition of lifts of families of elements by functions

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) {J : UU l4}
  (f : J → I)
  where

  precomp-lift-family-of-elements :
    (a : I → A) →
    lift-family-of-elements B a → lift-family-of-elements B (a ∘ f)
  precomp-lift-family-of-elements a b i = b (f i)
```

### Precomposition in lifted families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) {J : UU l4}
  (f : J → I)
  where

  precomp-lifted-family-of-elements :
    lifted-family-of-elements I B → lifted-family-of-elements J B
  precomp-lifted-family-of-elements =
    map-Σ
      ( lift-family-of-elements B)
      ( precomp f A)
      ( precomp-lift-family-of-elements B f)
```

## Properties

### Homotopies between maps induce commuting triangles of precompositions of lifts of families of elements

Consider two maps `f, g : J → I` and a homotopy `H : f ~ g` between them. The
precomposition functions they induce on lifts of families of elements have
different codomains, namely `lift-family-of-elements B (a ∘ f)` and
`lift-family-of-elements B (a ∘ g)`, but they fit into a
[commuting triangle](foundation.commuting-triangles-of-maps.md) with
[transport](foundation.transport-along-identifications.md) in the type of lifts:

```text
                              precomp-lift B f a
  lift-family-of-elements B a ------------------> lift-family-of-elements B (a ∘ f)
                      \                                /
                         \                          /
                            \                    /
           precomp-lift B g a  \              / tr (lift-family-of-elements B) (htpy-precomp H A a)
                                  \        /
                                     V  V
                       lift-family-of-elements B (a ∘ g)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) (a : I → A)
  {J : UU l4} {f : J → I}
  where

  statement-triangle-precomp-lift-family-of-elements-htpy :
    {g : J → I} (H : f ~ g) → UU (l1 ⊔ l3 ⊔ l4)
  statement-triangle-precomp-lift-family-of-elements-htpy {g} H =
    coherence-triangle-maps'
      ( precomp-lift-family-of-elements B g a)
      ( tr (lift-family-of-elements B) (htpy-precomp H A a))
      ( precomp-lift-family-of-elements B f a)

  triangle-precomp-lift-family-of-elements-htpy-refl-htpy :
    statement-triangle-precomp-lift-family-of-elements-htpy refl-htpy
  triangle-precomp-lift-family-of-elements-htpy-refl-htpy b =
    tr-lift-family-of-elements-precomp B a refl-htpy (b ∘ f)

  triangle-precomp-lift-family-of-elements-htpy :
    {g : J → I} (H : f ~ g) →
    statement-triangle-precomp-lift-family-of-elements-htpy H
  triangle-precomp-lift-family-of-elements-htpy =
    ind-htpy f
      ( λ g → statement-triangle-precomp-lift-family-of-elements-htpy)
      ( triangle-precomp-lift-family-of-elements-htpy-refl-htpy)

  abstract
    compute-triangle-precomp-lift-family-of-elements-htpy :
      triangle-precomp-lift-family-of-elements-htpy refl-htpy ＝
      triangle-precomp-lift-family-of-elements-htpy-refl-htpy
    compute-triangle-precomp-lift-family-of-elements-htpy =
      compute-ind-htpy f
        ( λ g → statement-triangle-precomp-lift-family-of-elements-htpy)
        ( triangle-precomp-lift-family-of-elements-htpy-refl-htpy)
```

### TODO

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) (a : I → A)
  {J : UU l4} {f : J → I}
  where

  statement-coherence-triangle-precomp-lift-family-of-elements-htpy :
    {g : J → I} (H : f ~ g) → UU (l1 ⊔ l3 ⊔ l4)
  statement-coherence-triangle-precomp-lift-family-of-elements-htpy H =
    ( triangle-precomp-lift-family-of-elements-htpy B a H) ~
    ( ( ( tr-lift-family-of-elements-precomp B a H) ·r
        ( precomp-lift-family-of-elements B f a)) ∙h
      ( λ b → eq-htpy (λ j → apd b (H j))))

  coherence-triangle-precomp-lift-family-of-elements-htpy-refl-htpy :
    statement-coherence-triangle-precomp-lift-family-of-elements-htpy
      ( refl-htpy)
  coherence-triangle-precomp-lift-family-of-elements-htpy-refl-htpy b =
    ( htpy-eq (compute-triangle-precomp-lift-family-of-elements-htpy B a) b) ∙
    ( inv right-unit) ∙
    ( identification-left-whisk
      ( triangle-precomp-lift-family-of-elements-htpy-refl-htpy B a b)
      ( inv (eq-htpy-refl-htpy (b ∘ f))))

  coherence-triangle-precomp-lift-family-of-elements-htpy :
    {g : J → I} (H : f ~ g) →
    statement-coherence-triangle-precomp-lift-family-of-elements-htpy H
  coherence-triangle-precomp-lift-family-of-elements-htpy =
    ind-htpy f
      ( λ g →
        statement-coherence-triangle-precomp-lift-family-of-elements-htpy)
      ( coherence-triangle-precomp-lift-family-of-elements-htpy-refl-htpy)

  abstract
    compute-coherence-triangle-precomp-lift-family-of-elements-htpy :
      coherence-triangle-precomp-lift-family-of-elements-htpy refl-htpy ＝
      coherence-triangle-precomp-lift-family-of-elements-htpy-refl-htpy
    compute-coherence-triangle-precomp-lift-family-of-elements-htpy =
      compute-ind-htpy f
        ( λ g →
          statement-coherence-triangle-precomp-lift-family-of-elements-htpy)
        ( coherence-triangle-precomp-lift-family-of-elements-htpy-refl-htpy)
```

### TODO

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) {J : UU l4}
  (f : J → I)
  where

  coherence-square-precomp-map-inv-distributive-Π-Σ :
    coherence-square-maps
      ( precomp-lifted-family-of-elements B f)
      ( map-inv-distributive-Π-Σ)
      ( map-inv-distributive-Π-Σ)
      ( precomp f (Σ A B))
  coherence-square-precomp-map-inv-distributive-Π-Σ = refl-htpy
```

### TODO

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) {J : UU l4}
  {f : J → I}
  where

  htpy-precomp-lifted-family-of-elements-htpy :
    {g : J → I} (H : f ~ g) →
    ( precomp-lifted-family-of-elements B f) ~
    ( precomp-lifted-family-of-elements B g)
  htpy-precomp-lifted-family-of-elements-htpy H =
    htpy-map-Σ
      ( lift-family-of-elements B)
      ( htpy-precomp H A)
      ( precomp-lift-family-of-elements B f)
      ( λ a → triangle-precomp-lift-family-of-elements-htpy B a H)

  abstract
    compute-htpy-precomp-lifted-family-of-elements-htpy :
      htpy-precomp-lifted-family-of-elements-htpy refl-htpy ~
      refl-htpy
    compute-htpy-precomp-lifted-family-of-elements-htpy =
      htpy-htpy-map-Σ-refl-htpy
        ( lift-family-of-elements B)
        ( compute-htpy-precomp-refl-htpy f A)
        ( λ a →
          ( htpy-eq
            ( compute-triangle-precomp-lift-family-of-elements-htpy B a)) ∙h
          ( λ b →
            htpy-eq (compute-tr-lift-family-of-elements-precomp B a) (b ∘ f)))
```

### TODO

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) {J : UU l4}
  {f : J → I}
  where

  statement-coherence-blabla :
    {g : J → I} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  statement-coherence-blabla {g} H =
    coherence-square-homotopies
      ( htpy-precomp H (Σ A B) ·r map-inv-distributive-Π-Σ)
      ( coherence-square-precomp-map-inv-distributive-Π-Σ B f)
      ( coherence-square-precomp-map-inv-distributive-Π-Σ B g)
      ( ( map-inv-distributive-Π-Σ) ·l
        ( htpy-precomp-lifted-family-of-elements-htpy B H))

  coherence-blabla-refl-htpy : statement-coherence-blabla refl-htpy
  coherence-blabla-refl-htpy =
    ( ap-left-whisk-htpy
      ( map-inv-distributive-Π-Σ)
      ( compute-htpy-precomp-lifted-family-of-elements-htpy B)) ∙h
    ( inv-htpy
      ( λ h →
        compute-htpy-precomp-refl-htpy f
          ( Σ A B)
          ( map-inv-distributive-Π-Σ h))) ∙h
    ( inv-htpy-right-unit-htpy)

  coherence-blabla :
    {g : J → I} (H : f ~ g) → statement-coherence-blabla H
  coherence-blabla =
    ind-htpy f
      ( λ g → statement-coherence-blabla)
      ( coherence-blabla-refl-htpy)
```
