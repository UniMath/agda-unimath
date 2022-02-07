# Homotopies

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.homotopies where

open import foundation-core.homotopies public

open import foundation-core.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-total-path; is-contr-total-path')
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.functoriality-dependent-pair-types using (equiv-tot)

open import foundation.function-extensionality using (equiv-funext)
open import foundation.identity-types using
  ( Id; refl; _∙_; concat; inv; assoc; left-unit; right-unit; left-inv;
    right-inv; ap; inv-con; con-inv; concat'; distributive-inv-concat; ap-inv;
    ap-id; is-injective-concat')
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A homotopy of identifications is a pointwise equality between dependent functions.

### Transpositions of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  inv-con-htpy :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → K ~ ((inv-htpy H) ∙h L)
  inv-con-htpy H K L M x = inv-con (H x) (K x) (L x) (M x)

  con-inv-htpy :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → H ~ (L ∙h (inv-htpy K))
  con-inv-htpy H K L M x = con-inv (H x) (K x) (L x) (M x)
```

### Homotopies preserve the laws of the acion on identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpy :
    (H : f ~ g) (K K' : g ~ h) → K ~ K' → (H ∙h K) ~ (H ∙h K')
  ap-concat-htpy H K K' L x = ap (concat (H x) (h x)) (L x)

  ap-concat-htpy' :
    (H H' : f ~ g) (K : g ~ h) → H ~ H' → (H ∙h K) ~ (H' ∙h K)
  ap-concat-htpy' H H' K L x =
    ap (concat' _ (K x)) (L x)
    
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  ap-inv-htpy :
    H ~ H' → (inv-htpy H) ~ (inv-htpy H')
  ap-inv-htpy K x = ap inv (K x)
```

### Whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
  left-whisk-inv-htpy g H x = ap-inv g (H x)

  right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  right-whisk-inv-htpy H f = refl-htpy
```

### The total space of homotopies is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where
  
  abstract
    is-contr-total-htpy : is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
    is-contr-total-htpy =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (Id f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path f)

  abstract
    is-contr-total-htpy' : is-contr (Σ ((x : A) → B x) (λ g → g ~ f))
    is-contr-total-htpy' =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (λ g → Id g f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path' f)
```
