# Path algebra

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module wild-algebra.path-algebra where

open import foundation.identity-types using
  ( Id; refl; inv; _∙_; assoc; square; ap; concat'; concat; right-unit; ap-id)
open import foundation.universe-levels using (Level; UU)
```

```agda
horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-lleft : Id a b) (p-lbottom : Id b d) (p-rbottom : Id d f) →
  (p-middle : Id c d) (p-ltop : Id a c) (p-rtop : Id c e) (p-rright : Id e f) →
  (s-left : square p-lleft p-lbottom p-ltop p-middle)
  (s-right : square p-middle p-rbottom p-rtop p-rright) →
  square p-lleft (p-lbottom ∙ p-rbottom) (p-ltop ∙ p-rtop) p-rright
horizontal-concat-square {a = a} {f = f}
  p-lleft p-lbottom p-rbottom p-middle p-ltop p-rtop p-rright s-left s-right =
  ( inv (assoc p-lleft p-lbottom p-rbottom)) ∙
  ( ( ap (concat' a p-rbottom) s-left) ∙
    ( ( assoc p-ltop p-middle p-rbottom) ∙
      ( ( ap (concat p-ltop f) s-right) ∙
        ( inv (assoc p-ltop p-rtop p-rright)))))

horizontal-unit-square :
  {l : Level} {A : UU l} {a b : A} (p : Id a b) →
  square p refl refl p
horizontal-unit-square p = right-unit 

left-unit-law-horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d : A}
  (p-left : Id a b) (p-bottom : Id b d) (p-top : Id a c) (p-right : Id c d) →
  (s : square p-left p-bottom p-top p-right) →
  Id ( horizontal-concat-square
       p-left refl p-bottom p-left refl p-top p-right
       ( horizontal-unit-square p-left)
       ( s))
     ( s)
left-unit-law-horizontal-concat-square refl p-bottom p-top p-right s =
  right-unit ∙ ap-id s

{-
right-unit-law-concat-horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d : A}
  (p-left : Id a b) (p-bottom : Id b d) (p-top : Id a c) (p-right : Id c d) →
  (s : square p-left p-bottom p-top p-right) →
  Id ( horizontal-concat-square
       p-left p-bottom refl p-right p-top refl p-right
       ( s)
       ( horizontal-unit-square p-right))
     ( s)
right-unit-law-concat-horizontal-concat-square
  p-left p-bottom p-top p-right s = ?
-}

vertical-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-tleft : Id a b) (p-bleft : Id b c) (p-bbottom : Id c f)
  (p-middle : Id b e) (p-ttop : Id a d) (p-tright : Id d e) (p-bright : Id e f)
  (s-top : square p-tleft p-middle p-ttop p-tright)
  (s-bottom : square p-bleft p-bbottom p-middle p-bright) →
  square (p-tleft ∙ p-bleft) p-bbottom p-ttop (p-tright ∙ p-bright)
vertical-concat-square {a = a} {f = f}
  p-tleft p-bleft p-bbottom p-middle p-ttop p-tright p-bright s-top s-bottom =
  ( assoc p-tleft p-bleft p-bbottom) ∙
  ( ( ap (concat p-tleft f) s-bottom) ∙
    ( ( inv (assoc p-tleft p-middle p-bright)) ∙
      ( ( ap (concat' a p-bright) s-top) ∙
        ( assoc p-ttop p-tright p-bright))))
