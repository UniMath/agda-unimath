# Path-split type families

```agda
module foundation.path-split-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.subtypes
```

</details>

## Idea

We say a type family `P : A → 𝒰` is
{{#concept "path-split" Disambiguation="type family" Agda=is-path-split-family}}
if, for every [identification](foundation-core.identity-types.md) `p : x ＝ y`
in `A`, and every pair of elements `u : P x` and `v : P y`, there is a
[dependent identification](foundation-core.dependent-identifications.md) of `u`
and `v` _over_ p. This condition is
[equivalent](foundation.logical-equivalences.md) to asking that `P` is a family
of [propositions](foundation-core.propositions.md).

## Definitions

### Path-split type families

```agda
is-path-split-family :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-path-split-family {A = A} P =
  {x y : A} (p : x ＝ y) (s : P x) (t : P y) → dependent-identification P p s t
```

## Properties

### The first projection map of a path-split type family is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  (H : is-path-split-family P)
  where

  is-injective-pr1-is-path-split-family : is-injective (pr1 {B = P})
  is-injective-pr1-is-path-split-family {x} {y} p =
    eq-pair-Σ p (H p (pr2 x) (pr2 y))

  is-section-is-injective-pr1-is-path-split-family :
    {x y : Σ A P} →
    is-section (ap pr1) (is-injective-pr1-is-path-split-family {x} {y})
  is-section-is-injective-pr1-is-path-split-family {x , u} {.x , v} refl =
    ap-pr1-eq-pair-eq-fiber (H refl u v)

  section-ap-pr1-is-path-split-family :
    (x y : Σ A P) → section (ap pr1 {x} {y})
  section-ap-pr1-is-path-split-family x y =
    is-injective-pr1-is-path-split-family ,
    is-section-is-injective-pr1-is-path-split-family

  is-emb-pr1-is-path-split-family : is-emb (pr1 {B = P})
  is-emb-pr1-is-path-split-family =
    is-emb-section-ap pr1 section-ap-pr1-is-path-split-family
```

### The fibers of a path-split type family are propositions

We give two proofs, one using the previous result and one more direct.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  (H : is-path-split-family P)
  where

  all-elements-equal-is-path-split-family : {x : A} (u v : P x) → u ＝ v
  all-elements-equal-is-path-split-family u v = H refl u v

  is-subtype-is-path-split-family : is-subtype P
  is-subtype-is-path-split-family x =
    is-prop-all-elements-equal all-elements-equal-is-path-split-family

  is-subtype-is-path-split-family' : is-subtype P
  is-subtype-is-path-split-family' =
    is-subtype-is-emb-pr1 (is-emb-pr1-is-path-split-family H)
```

### Path-splittings of type families are unique

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  abstract
    is-proof-irrelevant-is-path-split-family :
      is-proof-irrelevant (is-path-split-family P)
    is-proof-irrelevant-is-path-split-family H =
      is-contr-implicit-Π
        ( λ x →
          is-contr-implicit-Π
            ( λ y →
              is-contr-Π
                ( λ p →
                  is-contr-Π
                    ( λ s →
                      is-contr-Π
                        ( is-subtype-is-path-split-family H y (tr P p s))))))

  is-prop-is-path-split-family : is-prop (is-path-split-family P)
  is-prop-is-path-split-family =
    is-prop-is-proof-irrelevant is-proof-irrelevant-is-path-split-family
```

### Subtypes are path-split

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  is-path-split-family-is-subtype :
    is-subtype P → is-path-split-family P
  is-path-split-family-is-subtype H {x} refl s t = eq-is-prop (H x)
```
