# Quotient rings

```agda
module ring-theory.quotient-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.ideals-rings
open import ring-theory.rings
```

</details>

## Definitions

### The universal property of quotient rings

```agda
precomp-quotient-Ring :
  {l1 l2 l3 l4 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  (S : Ring l3) (T : Ring l4) →
  (f : hom-Ring R S)
  ( H : (x : type-Ring R) → is-in-ideal-Ring R I x →
        map-hom-Ring R S f x ＝ zero-Ring S) →
  hom-Ring S T →
  Σ ( hom-Ring R T)
    ( λ g →
      (x : type-Ring R) →
      is-in-ideal-Ring R I x → map-hom-Ring R T g x ＝ zero-Ring T)
pr1 (precomp-quotient-Ring R I S T f H h) = comp-hom-Ring R S T h f
pr2 (precomp-quotient-Ring R I S T f H h) x K =
  ap (map-hom-Ring S T h) (H x K) ∙ preserves-zero-hom-Ring S T h

universal-property-quotient-Ring :
  {l1 l2 l3 : Level} (l : Level) (R : Ring l1) (I : ideal-Ring l2 R)
  (S : Ring l3) (f : hom-Ring R S)
  ( H : (x : type-Ring R) → is-in-ideal-Ring R I x →
        map-hom-Ring R S f x ＝ zero-Ring S) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
universal-property-quotient-Ring l R I S f H =
  (T : Ring l) → is-equiv (precomp-quotient-Ring R I S T f H)
```
