{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45Zintegers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes

-- elementary-number-theory.addition-integers.add-ℤ
d_add'45'ℤ_4 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_add'45'ℤ_4 v0 v1
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v2
        -> case coe v2 of
             0 -> coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_pred'45'ℤ_136
                    (coe v1)
             _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_pred'45'ℤ_136
                    (coe
                       d_add'45'ℤ_4
                       (coe
                          MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 (coe v3))
                       (coe v1))
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v2
        -> case coe v2 of
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v3 -> coe v1
             MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v3
               -> case coe v3 of
                    0 -> coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_succ'45'ℤ_130
                           (coe v1)
                    _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
                         coe
                           MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_succ'45'ℤ_130
                           (coe
                              d_add'45'ℤ_4
                              (coe
                                 MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24
                                 (coe
                                    MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 (coe v4)))
                              (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.addition-integers.add-ℤ'
d_add'45'ℤ''_20 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_add'45'ℤ''_20 v0 v1 = coe d_add'45'ℤ_4 (coe v1) (coe v0)
-- elementary-number-theory.addition-integers.ap-add-ℤ
d_ap'45'add'45'ℤ_34 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'add'45'ℤ_34 = erased
-- elementary-number-theory.addition-integers.left-unit-law-add-ℤ
d_left'45'unit'45'law'45'add'45'ℤ_42 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'add'45'ℤ_42 = erased
-- elementary-number-theory.addition-integers.right-unit-law-add-ℤ
d_right'45'unit'45'law'45'add'45'ℤ_48 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'add'45'ℤ_48 = erased
-- elementary-number-theory.addition-integers.left-predecessor-law-add-ℤ
d_left'45'predecessor'45'law'45'add'45'ℤ_58 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'predecessor'45'law'45'add'45'ℤ_58 = erased
-- elementary-number-theory.addition-integers.right-predecessor-law-add-ℤ
d_right'45'predecessor'45'law'45'add'45'ℤ_76 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'predecessor'45'law'45'add'45'ℤ_76 = erased
-- elementary-number-theory.addition-integers.left-successor-law-add-ℤ
d_left'45'successor'45'law'45'add'45'ℤ_96 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'add'45'ℤ_96 = erased
-- elementary-number-theory.addition-integers.right-successor-law-add-ℤ
d_right'45'successor'45'law'45'add'45'ℤ_114 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'add'45'ℤ_114 = erased
-- elementary-number-theory.addition-integers.is-add-one-succ-ℤ'
d_is'45'add'45'one'45'succ'45'ℤ''_132 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'one'45'succ'45'ℤ''_132 = erased
-- elementary-number-theory.addition-integers.is-add-one-succ-ℤ
d_is'45'add'45'one'45'succ'45'ℤ_138 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'one'45'succ'45'ℤ_138 = erased
-- elementary-number-theory.addition-integers.is-add-neg-one-pred-ℤ
d_is'45'add'45'neg'45'one'45'pred'45'ℤ_144 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'neg'45'one'45'pred'45'ℤ_144 = erased
-- elementary-number-theory.addition-integers.is-add-neg-one-pred-ℤ'
d_is'45'add'45'neg'45'one'45'pred'45'ℤ''_150 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'neg'45'one'45'pred'45'ℤ''_150 = erased
-- elementary-number-theory.addition-integers.associative-add-ℤ
d_associative'45'add'45'ℤ_160 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'add'45'ℤ_160 = erased
-- elementary-number-theory.addition-integers.commutative-add-ℤ
d_commutative'45'add'45'ℤ_190 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'add'45'ℤ_190 = erased
-- elementary-number-theory.addition-integers.left-inverse-law-add-ℤ
d_left'45'inverse'45'law'45'add'45'ℤ_208 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'inverse'45'law'45'add'45'ℤ_208 = erased
-- elementary-number-theory.addition-integers.right-inverse-law-add-ℤ
d_right'45'inverse'45'law'45'add'45'ℤ_216 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'inverse'45'law'45'add'45'ℤ_216 = erased
-- elementary-number-theory.addition-integers.issec-add-neg-ℤ
d_issec'45'add'45'neg'45'ℤ_224 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'add'45'neg'45'ℤ_224 = erased
-- elementary-number-theory.addition-integers.isretr-add-neg-ℤ
d_isretr'45'add'45'neg'45'ℤ_234 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'add'45'neg'45'ℤ_234 = erased
-- elementary-number-theory.addition-integers.issec-add-neg-ℤ'
d_issec'45'add'45'neg'45'ℤ''_244 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'add'45'neg'45'ℤ''_244 = erased
-- elementary-number-theory.addition-integers.isretr-add-neg-ℤ'
d_isretr'45'add'45'neg'45'ℤ''_254 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_isretr'45'add'45'neg'45'ℤ''_254 = erased
-- elementary-number-theory.addition-integers.interchange-law-add-add-ℤ
d_interchange'45'law'45'add'45'add'45'ℤ_260 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_interchange'45'law'45'add'45'add'45'ℤ_260 = erased
-- elementary-number-theory.addition-integers.is-injective-add-ℤ'
d_is'45'injective'45'add'45'ℤ''_264 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'ℤ''_264 = erased
-- elementary-number-theory.addition-integers.is-injective-add-ℤ
d_is'45'injective'45'add'45'ℤ_276 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'ℤ_276 = erased
-- elementary-number-theory.addition-integers.right-negative-law-add-ℤ
d_right'45'negative'45'law'45'add'45'ℤ_290 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'negative'45'law'45'add'45'ℤ_290 = erased
-- elementary-number-theory.addition-integers.distributive-neg-add-ℤ
d_distributive'45'neg'45'add'45'ℤ_310 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_distributive'45'neg'45'add'45'ℤ_310 = erased
-- elementary-number-theory.addition-integers.negatives-add-ℤ
d_negatives'45'add'45'ℤ_330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_negatives'45'add'45'ℤ_330 = erased
-- elementary-number-theory.addition-integers.add-one-left-ℤ
d_add'45'one'45'left'45'ℤ_340 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'one'45'left'45'ℤ_340 = erased
-- elementary-number-theory.addition-integers.add-one-right-ℤ
d_add'45'one'45'right'45'ℤ_346 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'one'45'right'45'ℤ_346 = erased
-- elementary-number-theory.addition-integers.add-neg-one-left-ℤ
d_add'45'neg'45'one'45'left'45'ℤ_352 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'neg'45'one'45'left'45'ℤ_352 = erased
-- elementary-number-theory.addition-integers.add-neg-one-right-ℤ
d_add'45'neg'45'one'45'right'45'ℤ_358 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'neg'45'one'45'right'45'ℤ_358 = erased
-- elementary-number-theory.addition-integers.is-nonnegative-add-ℤ
d_is'45'nonnegative'45'add'45'ℤ_366 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'nonnegative'45'add'45'ℤ_366 = erased
-- elementary-number-theory.addition-integers.is-positive-add-ℤ
d_is'45'positive'45'add'45'ℤ_394 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_is'45'positive'45'add'45'ℤ_394 = erased
-- elementary-number-theory.addition-integers.add-int-ℕ
d_add'45'int'45'ℕ_414 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'int'45'ℕ_414 = erased
-- elementary-number-theory.addition-integers.is-zero-add-ℤ
d_is'45'zero'45'add'45'ℤ_426 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'add'45'ℤ_426 = erased
-- elementary-number-theory.addition-integers.is-zero-add-ℤ'
d_is'45'zero'45'add'45'ℤ''_438 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'add'45'ℤ''_438 = erased
-- elementary-number-theory.addition-integers.is-equiv-add-ℤ
d_is'45'equiv'45'add'45'ℤ_448 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'add'45'ℤ_448 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'ℤ_4
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
               (coe v0)))
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'ℤ_4
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
               (coe v0)))
         erased)
-- elementary-number-theory.addition-integers.equiv-add-ℤ
d_equiv'45'add'45'ℤ_462 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'add'45'ℤ_462 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_add'45'ℤ_4 (coe v0))
      (coe d_is'45'equiv'45'add'45'ℤ_448 (coe v0))
-- elementary-number-theory.addition-integers.is-equiv-add-ℤ'
d_is'45'equiv'45'add'45'ℤ''_470 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'add'45'ℤ''_470 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'ℤ''_20
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
               (coe v0)))
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'ℤ''_20
            (coe
               MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.Qintegers.d_neg'45'ℤ_142
               (coe v0)))
         erased)
-- elementary-number-theory.addition-integers.equiv-add-ℤ'
d_equiv'45'add'45'ℤ''_484 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'add'45'ℤ''_484 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_add'45'ℤ''_20 (coe v0))
      (coe d_is'45'equiv'45'add'45'ℤ''_470 (coe v0))
-- elementary-number-theory.addition-integers.is-emb-add-ℤ
d_is'45'emb'45'add'45'ℤ_492 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'add'45'ℤ_492 ~v0 = du_is'45'emb'45'add'45'ℤ_492
du_is'45'emb'45'add'45'ℤ_492 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'add'45'ℤ_492 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'emb'45'is'45'equiv_878
-- elementary-number-theory.addition-integers.is-emb-add-ℤ'
d_is'45'emb'45'add'45'ℤ''_498 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'emb'45'add'45'ℤ''_498 ~v0 = du_is'45'emb'45'add'45'ℤ''_498
du_is'45'emb'45'add'45'ℤ''_498 ::
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'emb'45'add'45'ℤ''_498 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_is'45'emb'45'is'45'equiv_878
