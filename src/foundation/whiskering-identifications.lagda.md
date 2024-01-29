# Whiskering identifications

```agda
module foundation.whiskering-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
```

</details>

## Idea

## Definitions

### Definition of identification whiskering

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  left-whisker-identification :
    (p : x ＝ y) {q q' : y ＝ z} → q ＝ q' → (p ∙ q) ＝ (p ∙ q')
  left-whisker-identification p β = ap (p ∙_) β

  right-whisker-identification :
    {p p' : x ＝ y} → p ＝ p' → (q : y ＝ z) → (p ∙ q) ＝ (p' ∙ q)
  right-whisker-identification α q = ap (_∙ q) α

  htpy-left-whisker-identification :
    {q q' : y ＝ z} → q ＝ q' → (_∙ q) ~ (_∙ q')
  htpy-left-whisker-identification β p = left-whisker-identification p β
```

### Whiskerings of identifications are equivalences

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  is-equiv-left-whisker-identification :
    (p : x ＝ y) {q q' : y ＝ z} →
    is-equiv (left-whisker-identification p {q} {q'})
  is-equiv-left-whisker-identification p {q} {q'} =
    is-emb-is-equiv (is-equiv-concat p z) q q'

  equiv-left-whisker-identification :
    (p : x ＝ y) {q q' : y ＝ z} →
    (q ＝ q') ≃ (p ∙ q ＝ p ∙ q')
  pr1 (equiv-left-whisker-identification p) = left-whisker-identification p
  pr2 (equiv-left-whisker-identification p) =
    is-equiv-left-whisker-identification p

  is-equiv-right-whisker-identification :
    {p p' : x ＝ y} → (q : y ＝ z) →
    is-equiv (λ (α : p ＝ p') → right-whisker-identification α q)
  is-equiv-right-whisker-identification {p} {p'} q =
    is-emb-is-equiv (is-equiv-concat' x q) p p'

  equiv-right-whisker-identification :
    {p p' : x ＝ y} → (q : y ＝ z) →
    (p ＝ p') ≃ (p ∙ q ＝ p' ∙ q)
  pr1 (equiv-right-whisker-identification q) α =
    right-whisker-identification α q
  pr2 (equiv-right-whisker-identification q) =
    is-equiv-right-whisker-identification q
```

### Whiskering of squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : x ＝ y) (p' : x ＝ z) {q : y ＝ u} {q' : z ＝ u} (r : u ＝ v)
  where

  equiv-right-whisker-square-identification :
    ( coherence-square-identifications p p' q q') ≃
    ( coherence-square-identifications p p' (q ∙ r) (q' ∙ r))
  equiv-right-whisker-square-identification =
    ( equiv-concat-assoc' (p' ∙ (q' ∙ r)) p q r) ∘e
    ( equiv-concat-assoc p' q' r (p ∙ q ∙ r)) ∘e
    ( equiv-right-whisker-identification r)

  right-whisker-square-identification :
    coherence-square-identifications p p' q q' →
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r)
  right-whisker-square-identification =
    map-equiv equiv-right-whisker-square-identification

  right-unwhisker-square-identifications :
    coherence-square-identifications p p' (q ∙ r) (q' ∙ r) →
    coherence-square-identifications p p' q q'
  right-unwhisker-square-identifications =
    map-inv-equiv equiv-right-whisker-square-identification

module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : v ＝ x) {q : x ＝ y} {q' : x ＝ z} {r : y ＝ u} {r' : z ＝ u}
  where

  equiv-left-whisker-square-identification :
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') r r')
  equiv-left-whisker-square-identification =
    ( inv-equiv (equiv-concat-assoc p q' r' (p ∙ q ∙ r))) ∘e
    ( inv-equiv (equiv-concat-assoc' (p ∙ (q' ∙ r')) p q r)) ∘e
    ( equiv-left-whisker-identification p)

  left-whisker-square-identification :
    coherence-square-identifications q q' r r' →
    coherence-square-identifications (p ∙ q) (p ∙ q') r r'
  left-whisker-square-identification =
    map-equiv equiv-left-whisker-square-identification

  left-unwhisker-square-identification :
    coherence-square-identifications (p ∙ q) (p ∙ q') r r' →
    coherence-square-identifications q q' r r'
  left-unwhisker-square-identification =
    map-inv-equiv equiv-left-whisker-square-identification

module _
  {l : Level} {A : UU l} {x y z u v w : A}
  where

  equiv-both-whisker-square-identifications :
    (p : x ＝ y) {q : y ＝ z} {q' : y ＝ u} {r : z ＝ v} {r' : u ＝ v} →
    (s : v ＝ w) →
    ( coherence-square-identifications q q' r r') ≃
    ( coherence-square-identifications (p ∙ q) (p ∙ q') (r ∙ s) (r' ∙ s))
  equiv-both-whisker-square-identifications p {q} {q'} s =
    ( equiv-left-whisker-square-identification p) ∘e
    ( equiv-right-whisker-square-identification q q' s)
```

### Unit laws for whiskering

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-law-left-whisker-identification :
    {p p' : x ＝ y} (α : p ＝ p') →
    left-whisker-identification refl α ＝ α
  left-unit-law-left-whisker-identification refl = refl

  right-unit-law-right-whisker-identification :
    {p p' : x ＝ y} (α : p ＝ p') →
    right-whisker-identification α refl ＝
    right-unit ∙ α ∙ inv right-unit
  right-unit-law-right-whisker-identification {p = refl} refl = refl
```

### The whiskering operations allow us to commute higher identifications

There are two natural ways to commute higher identifications: using whiskering
on the left versus using whiskering on the right. These two ways "undo" each
other.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  path-swap-nat-left-whisker-identification :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    coherence-square-identifications
      ( right-whisker-identification α q)
      ( left-whisker-identification p β)
      ( left-whisker-identification p' β)
      ( right-whisker-identification α q')
  path-swap-nat-left-whisker-identification β =
    nat-htpy (htpy-left-whisker-identification β)

  path-swap-nat-right-whisker-identification :
    {p p' : x ＝ y} (α : p ＝ p') {q q' : y ＝ z} (β : q ＝ q') →
    coherence-square-identifications
      ( left-whisker-identification p β)
      ( right-whisker-identification α q)
      ( right-whisker-identification α q')
      ( left-whisker-identification p' β)
  path-swap-nat-right-whisker-identification α =
    nat-htpy (right-whisker-identification α)

  path-swap-right-undoes-path-swap-left :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    inv (path-swap-nat-right-whisker-identification α β) ＝
    (path-swap-nat-left-whisker-identification β α)
  path-swap-right-undoes-path-swap-left refl refl = refl
```

