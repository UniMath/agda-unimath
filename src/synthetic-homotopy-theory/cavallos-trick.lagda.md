# Cavallo's trick

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.cavallos-trick
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.sections funext
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation funext

open import structured-types.pointed-homotopies funext
open import structured-types.pointed-maps funext
open import structured-types.pointed-types
```

</details>

## Idea

**Cavallo's trick** is a way of upgrading an unpointed
[homotopy](foundation.homotopies.md) between
[pointed maps](structured-types.pointed-maps.md) to a
[pointed homotopy](structured-types.pointed-homotopies.md).

Originally, this trick was formulated by Evan Cavallo for homogeneous spaces,
but it works as soon as the evaluation map `(id ~ id) → Ω B` has a section.

## Theorem

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  htpy-cavallos-trick :
    (f g : A →∗ B) → section (λ (H : id ~ id) → H (point-Pointed-Type B)) →
    (map-pointed-map f ~ map-pointed-map g) →
    unpointed-htpy-pointed-map f g
  htpy-cavallos-trick (f , refl) (g , q) (K , α) H a =
    K (inv q ∙ inv (H (point-Pointed-Type A))) (f a) ∙ H a

  coherence-point-cavallos-trick :
    (f g : A →∗ B) (s : section (λ (H : id ~ id) → H (point-Pointed-Type B))) →
    (H : map-pointed-map f ~ map-pointed-map g) →
    coherence-point-unpointed-htpy-pointed-Π f g
      ( htpy-cavallos-trick f g s H)
  coherence-point-cavallos-trick (f , refl) (g , q) (K , α) H =
    inv
      ( ( right-whisker-concat
          ( ( right-whisker-concat (α _) (H _)) ∙
            ( is-section-inv-concat' (H _) (inv q)))
          ( q)) ∙
        ( left-inv q))

  cavallos-trick :
    (f g : A →∗ B) → section (λ (H : id ~ id) → H (point-Pointed-Type B)) →
    (map-pointed-map f ~ map-pointed-map g) → f ~∗ g
  pr1 (cavallos-trick f g s H) = htpy-cavallos-trick f g s H
  pr2 (cavallos-trick f g s H) = coherence-point-cavallos-trick f g s H
```

## References

- Cavallo's trick was originally formalized in the
  [cubical agda library](https://agda.github.io/cubical/Cubical.Foundations.Pointed.Homogeneous.html).
- The above generalization was found by Buchholtz, Christensen, Rijke, and
  Taxerås Flaten, in {{#cite BCFR23}}.

{{#bibliography}}
