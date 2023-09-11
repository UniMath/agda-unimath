# Cavallo's trick

```agda
module synthetic-homotopy-theory.cavallos-trick where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sections
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Cavallo's trick is a way of upgrading an unpointed homotopy between pointed maps
to a pointed homotopy. Originally, this trick was formulated by Evan Cavallo for
homogeneous spaces, but it works as soon as the evaluation map `(id ~ id) → Ω B`
has a section.

## Theorem

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  cavallos-trick :
    (f g : A →∗ B) → section (λ (H : id ~ id) → H (point-Pointed-Type B)) →
    (map-pointed-map f ~ map-pointed-map g) → f ~∗ g
  pr1 (cavallos-trick (f , refl) (g , q) (K , α) H) a =
    K (inv q ∙ inv (H (point-Pointed-Type A))) (f a) ∙ H a
  pr2 (cavallos-trick (f , refl) (g , q) (K , α) H) =
    ( ap
      ( concat' (f (point-Pointed-Type A)) (H (point-Pointed-Type A)))
      ( α (inv q ∙ inv (H (point-Pointed-Type A))))) ∙
    ( ( assoc
        ( inv q)
        ( inv (H (point-Pointed-Type A)))
        ( H (point-Pointed-Type A))) ∙
      ( ( ap
          ( concat (inv q) (g (point-Pointed-Type A)))
          ( left-inv (H (point-Pointed-Type A)))) ∙
        ( right-unit)))
```

## References

- Cavallo's trick was originally formalized in the
  [cubical agda library](https://agda.github.io/cubical/Cubical.Foundations.Pointed.Homogeneous.html).
- The above generalization was found by Buchholtz, Christensen, Rijke, and
  Taxerås Flaten, in
  [Central H-spaces and banded types](https://arxiv.org/abs/2301.02636)
