# Commuting squares of identifications

```agda
module foundation.commuting-squares-of-identifications where

open import foundation-core.commuting-squares-of-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications

open import foundation-core.equivalences
```

</details>

## Idea

In this file we develop some further properties of
[commuting squares of identifications](foundation-core.commuting-squares-of-identifications.md).

## Properties

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
