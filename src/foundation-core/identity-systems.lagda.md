# Identity systems

```agda
module foundation-core.identity-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.universe-levels
```

</details>

## Idea

A unary identity system on a type `A` equipped with a point `a : A` consists of a type family `B` over `A` equipped with a point `b : B a` that satisfies an induction principle analogous to the induction principle of the identity type at `a`.

```agda
module _
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : A → UU l2) (a : A) (b : B a)
  where

  IND-identity-system : UU (l1 ⊔ l2 ⊔ lsuc l)
  IND-identity-system =
    ( P : (x : A) (y : B x) → UU l) →
      sec (λ (h : (x : A) (y : B x) → P x y) → h a b)
```

## Properties

### A type family over `A` is an identity system if and only if it is equivalent to the identity type

```
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    Ind-identity-system :
      (is-contr-AB : is-contr (Σ A B)) →
      {l : Level} → IND-identity-system l B a b
    pr1 (Ind-identity-system is-contr-AB P) p x y =
      tr ( fam-Σ P)
         ( eq-is-contr is-contr-AB)
         ( p)
    pr2 (Ind-identity-system is-contr-AB P) p =
      ap ( λ t → tr (fam-Σ P) t p)
         ( eq-is-contr'
           ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
           ( eq-is-contr is-contr-AB)
           ( refl))

  abstract
    is-contr-total-space-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) → is-contr (Σ A B)
    pr1 (pr1 (is-contr-total-space-IND-identity-system ind)) = a
    pr2 (pr1 (is-contr-total-space-IND-identity-system ind)) = b
    pr2 (is-contr-total-space-IND-identity-system ind) (pair x y) =
      pr1 (ind (λ x' y' → (pair a b) ＝ (pair x' y'))) refl x y

  abstract
    fundamental-theorem-id-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) →
      (f : (x : A) → a ＝ x → B x) → (x : A) → is-equiv (f x)
    fundamental-theorem-id-IND-identity-system ind f =
      fundamental-theorem-id
        ( is-contr-total-space-IND-identity-system ind)
        ( f)
```
