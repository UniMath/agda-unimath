# Whiskering identifications with respect to concatenation

```agda
module foundation.whiskering-identifications-concatenation where

open import foundation-core.whiskering-identifications-concatenation public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-operations

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

Consider two [identifications](foundation-core.identity-types.md) `p q : x ＝ y`
in a type `A`. The whiskering operations are operations that take
identifications `p ＝ q` to identifications `r ∙ p ＝ r ∙ q` or to
identifications `p ∙ r ＝ q ∙ r`.

The
{{#concept "left whiskering" Disambiguation="identifications" Agda=left-whisker-concat}}
operation takes an identification `r : z ＝ x` and an identification `p ＝ q` to
an identification `r ∙ p ＝ r ∙ q`. Similarly, the
{{#concept "right whiskering" Disambiguation="identifications" Agda=right-whisker-concat}}
operation takes an identification `r : y ＝ z` and an identification `p ＝ q` to
an identification `p ∙ r ＝ q ∙ r`.

The whiskering operations can be defined by the
[acion on identifications](foundation.action-on-identifications-functions.md) of
concatenation. Since concatenation on either side is an
[equivalence](foundation-core.equivalences.md), it follows that the whiskering
operations are equivalences.

## Properties

### Left whiskering of identifications is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {q q' : y ＝ z}
  where

  is-equiv-left-whisker-concat :
    is-equiv (left-whisker-concat p {q} {q'})
  is-equiv-left-whisker-concat =
    is-emb-is-equiv (is-equiv-concat p z) q q'

  equiv-left-whisker-concat : (q ＝ q') ≃ (p ∙ q ＝ p ∙ q')
  pr1 equiv-left-whisker-concat =
    left-whisker-concat p
  pr2 equiv-left-whisker-concat =
    is-equiv-left-whisker-concat
```

### Right whiskering of identifications is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A} {p p' : x ＝ y} (q : y ＝ z)
  where

  is-equiv-right-whisker-concat :
    is-equiv (λ (α : p ＝ p') → right-whisker-concat α q)
  is-equiv-right-whisker-concat =
    is-emb-is-equiv (is-equiv-concat' x q) p p'

  equiv-right-whisker-concat : (p ＝ p') ≃ (p ∙ q ＝ p' ∙ q)
  pr1 equiv-right-whisker-concat α =
    right-whisker-concat α q
  pr2 equiv-right-whisker-concat =
    is-equiv-right-whisker-concat
```

### Left unwhiskering of identifications is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {q q' : y ＝ z}
  where

  is-equiv-left-unwhisker-concat :
    is-equiv (λ (α : p ∙ q ＝ p ∙ q') → left-unwhisker-concat p α)
  is-equiv-left-unwhisker-concat = is-equiv-is-injective-concat p

  equiv-left-unwhisker-concat : (p ∙ q ＝ p ∙ q') ≃ (q ＝ q')
  equiv-left-unwhisker-concat =
    ( left-unwhisker-concat p , is-equiv-left-unwhisker-concat)
```

### Right unwhiskering of identifications is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A} {p p' : x ＝ y} (q : y ＝ z)
  where

  is-equiv-right-unwhisker-concat :
    is-equiv (λ (α : p ∙ q ＝ p' ∙ q) → right-unwhisker-concat q α)
  is-equiv-right-unwhisker-concat = is-equiv-is-injective-concat' q

  equiv-right-unwhisker-concat : (p ∙ q ＝ p' ∙ q) ≃ (p ＝ p')
  equiv-right-unwhisker-concat =
    ( right-unwhisker-concat q , is-equiv-right-unwhisker-concat)
```
