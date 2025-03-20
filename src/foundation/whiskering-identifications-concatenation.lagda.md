# Whiskering identifications with respect to concatenation

```agda
open import foundation.function-extensionality-axiom

module
  foundation.whiskering-identifications-concatenation
  (funext : function-extensionality)
  where

open import foundation-core.whiskering-identifications-concatenation public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import foundation-core.equivalences
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

### Right whiskering of identification is an equivalence

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
